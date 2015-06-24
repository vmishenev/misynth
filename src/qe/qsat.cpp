/*++
Copyright (c) 2015 Microsoft Corporation

Module Name:

    qsat.cpp

Abstract:

    Quantifier Satisfiability Solver.

Author:

    Nikolaj Bjorner (nbjorner) 2015-5-28

Revision History:


--*/

#include "qsat.h"
#include "smt_kernel.h"
#include "qe_mbp.h"
#include "smt_params.h"
#include "ast_util.h"
#include "quant_hoist.h"
#include "ast_pp.h"
#include "model_v2_pp.h"
#include "filter_model_converter.h"

namespace qe {


class qsat : public tactic {

    struct stats {
        unsigned m_num_predicates;
        unsigned m_num_rounds;        
        stats() { reset(); }
        void reset() { memset(this, 0, sizeof(*this)); }
    };
    
    class kernel {
        ast_manager& m;
        smt_params   m_smtp;
        smt::kernel  m_kernel;

    public:
        kernel(ast_manager& m):
            m(m),
            m_kernel(m, m_smtp)
        {
            m_smtp.m_model = true;
            m_smtp.m_relevancy_lvl = 0;
        }
            
        smt::kernel& k() { return m_kernel; }
        smt::kernel const& k() const { return m_kernel; }

        void assert_expr(expr* e) {
            m_kernel.assert_expr(e);
        }

        void get_core(expr_ref_vector& core) {
            unsigned sz = m_kernel.get_unsat_core_size();
            core.reset();
            for (unsigned i = 0; i < sz; ++i) {
                core.push_back(m_kernel.get_unsat_core_expr(i));
            }
            TRACE("qe", tout << "core: ";
                  for (unsigned i = 0; i < sz; ++i) {
                      tout << mk_pp(core[i].get(), m) << " ";
                  }
                  tout << "\n";
                  m_kernel.display(tout);
                  tout << "\n";
                  );
        }
    };


    struct max_level {
        unsigned m_ex, m_fa;
        max_level(): m_ex(UINT_MAX), m_fa(UINT_MAX) {}
        void merge(max_level const& other) {
            merge(m_ex, other.m_ex);
            merge(m_fa, other.m_fa);
        }
        static unsigned max(unsigned a, unsigned b) {
            if (a == UINT_MAX) return b;
            if (b == UINT_MAX) return a;
            return std::max(a, b);
        }
        unsigned max() const {
            return max(m_ex, m_fa);
        }
        void merge(unsigned& lvl, unsigned const& other) {
            lvl = max(lvl, other);
        }
        std::ostream& display(std::ostream& out) const {
            if (m_ex != UINT_MAX) out << "e" << m_ex << " ";
            if (m_fa != UINT_MAX) out << "a" << m_fa << " ";
            return out;
        }
    };

    class move_preds {
        ast_manager& m;
        qsat&        q;
        vector<app_ref_vector> m_preds;
        expr_ref_vector  m_asms;
        unsigned_vector m_asms_lim;

    public:
        move_preds(qsat& _q):
            m(_q.m),
            q(_q),
            m_asms(m)
        {}


        void reset() {
        }

        void push() {
            m_asms_lim.push_back(m_asms.size());
        }

        void pop(unsigned num_scopes) {
            unsigned l = m_asms_lim.size() - num_scopes;
            m_asms.resize(m_asms_lim[l]);
            m_asms_lim.resize(l);
        }
        
        void insert(app* a, max_level const& lvl) {
            unsigned l = lvl.max();
            if (l == UINT_MAX) l = 0;
            while (m_preds.size() <= l) {
                m_preds.push_back(app_ref_vector(m));
            }
            m_preds[l].push_back(a);            
        }

        void get_assumptions(expr_ref_vector& asms) {
            asms.reset();
            unsigned level = q.m_level;
            if (level == 0 || level > m_preds.size()) {
                return;
            }
            model& mdl = *q.m_model.get();
            expr_ref val(m);
            for (unsigned j = 0; j < m_preds[level - 1].size(); ++j) {
                app* p = m_preds[level - 1][j].get();
                VERIFY(mdl.eval(p, val));
                if (m.is_false(val)) {
                    m_asms.push_back(m.mk_not(p));
                }
                else {
                    m_asms.push_back(p);
                }
            }
            asms.append(m_asms);

            for (unsigned i = level + 1; i < m_preds.size(); i += 2) {
                for (unsigned j = 0; j < m_preds[i].size(); ++j) {
                    app* p = m_preds[i][j].get();
                    max_level lvl = q.m_elevel.find(p);
                    bool use = 
                        (lvl.m_fa == i && (lvl.m_ex == UINT_MAX || lvl.m_ex < level)) ||
                        (lvl.m_ex == i && (lvl.m_fa == UINT_MAX || lvl.m_fa < level));
                    if (use) {
                        VERIFY(mdl.eval(p, val));
                        if (m.is_false(val)) {
                            asms.push_back(m.mk_not(p));
                        }
                        else {
                            asms.push_back(p);
                        }
                    }
                }
            }
            TRACE("qe", tout << "level: " << level << "\n";
                  model_v2_pp(tout, mdl);
                  q.display(tout, asms););
        }

        void display(std::ostream& out) const {
            for (unsigned i = 0; i < m_preds.size(); ++i) {
                out << "level " << i << "\n";
                if (q.m_vars.size() > i && !q.m_vars[i].empty()) {
                    for (unsigned j = 0; j < q.m_vars[i].size(); ++j) {
                        expr* v = q.m_vars[i][j].get();
                        out << mk_pp(v, m) << " ";
                    }
                    out << "\n";
                }
                for (unsigned j = 0; j < m_preds[i].size(); ++j) {
                    app* p = m_preds[i][j];
                    expr* e;
                    if (q.m_pred2lit.find(p, e)) {
                        out << mk_pp(p, m) << " := " << mk_pp(e, m) << "\n";
                    }
                    else {
                        out << mk_pp(p, m) << "\n";
                    }
                }
            }            
        }        
    };

    ast_manager&               m;
    params_ref                 m_params;
    stats                      m_stats;
    statistics                 m_st;
    qe::mbp                    m_mbp;
    kernel                     m_fa;
    kernel                     m_ex;
    move_preds                 m_moves;
    expr_ref_vector            m_trail;      // predicates that encode atomic subformulas
    expr_ref_vector            m_answer;
    vector<app_ref_vector>     m_vars;       // variables from alternating prefixes.
    unsigned                   m_level;
    model_ref                  m_model;
    obj_map<expr, expr*>       m_pred2lit;    // maintain definitions of predicates.
    obj_map<expr, app*>        m_lit2pred;    // maintain reverse mapping to predicates
    obj_map<expr, max_level>   m_elevel;
    filter_model_converter_ref m_fmc;
    volatile bool              m_cancel;
    bool                       m_qelim;
    ptr_vector<expr>           todo;          // temporary variable for worklist



    /**
       \brief check alternating satisfiability.
       Even levels are existential, odd levels are universal.
     */
    lbool check_sat() {        
        while (true) {
            ++m_stats.m_num_rounds;
            check_cancel();
            expr_ref_vector asms(m);
            m_moves.get_assumptions(asms);
            lbool res = get_kernel(m_level).k().check(asms);
            switch (res) {
            case l_true:
                get_kernel(m_level).k().get_model(m_model);
                TRACE("qe", display(tout, *m_model.get()); display(tout, asms););
                push();
                break;
            case l_false:
                switch (m_level) {
                case 0: return l_false;
                case 1: 
                    if (!m_qelim) return l_true; 
                    project_qe(asms);
                    break;
                default: project(asms); break;
                }
                break;
            case l_undef:
                return res;
            }
        }
        return l_undef;
    }

    kernel& get_kernel(unsigned j) {        
        if (is_exists(j)) {
            return m_ex; 
        }
        else {
            return m_fa;
        }
    }

    bool is_exists(unsigned level) const {
        return (level % 2) == 0;
    }

    bool is_forall(unsigned level) const {
        return is_exists(level+1);
    }

    void push() {
        m_level++;
        m_moves.push();
    }

    void pop(unsigned num_scopes) {
        SASSERT(num_scopes <= m_level);
        m_moves.pop(num_scopes);
        m_level -= num_scopes;
    }

    void add_pred(app* p, app* lit) {
        m.inc_ref(p);
        m.inc_ref(lit);
        SASSERT(!m_lit2pred.contains(lit));
        m_pred2lit.insert(p, lit);
        m_lit2pred.insert(lit, p);        
        ++m_stats.m_num_predicates;
    }

    void reset() {
        m_level = 0;
        m_trail.reset();
        m_answer.reset();
        m_moves.reset();
        m_vars.reset();
        m_model = 0;
        obj_map<expr, expr*>::iterator it = m_pred2lit.begin(), end = m_pred2lit.end();
        for (; it != end; ++it) {
            m.dec_ref(it->m_key);
            m.dec_ref(it->m_value);
        }
        m_lit2pred.reset();
        m_pred2lit.reset();
        m_elevel.reset();
        m_st.reset();        
        m_fa.k().collect_statistics(m_st);
        m_ex.k().collect_statistics(m_st);
        m_fa.k().reset();
        m_ex.k().reset();        
        m_cancel = false;
    }    

    app_ref mk_not(expr* e) {
        if (!is_app(e)) {
            return app_ref(m.mk_not(e), m);
        }
        app* a = to_app(e);
        if (m.is_and(a) && a->get_num_args() > 0) {
            app_ref_vector args(m);
            for (unsigned i = 0; i < a->get_num_args(); ++i) {
                args.push_back(mk_not(a->get_arg(i)));
            }
            return app_ref(::mk_or(args), m);
        }
        if (m.is_true(a)) return app_ref(m.mk_false(), m);
        if (m.is_false(a)) return app_ref(m.mk_true(), m);
        return app_ref(to_app(::mk_not(m, e)), m);
    }

    app_ref fresh_bool(char const* name) {
        app_ref r(m.mk_fresh_const(name, m.mk_bool_sort()), m);
        m_fmc->insert(r->get_decl());
        return r;
    }

    /**
       \brief create a quantifier prefix formula.
     */
    void hoist(expr_ref& fml) {
        quantifier_hoister hoist(m);
        app_ref_vector vars(m);
        bool is_forall = false;        
        get_free_vars(fml, vars);
        m_vars.push_back(vars);
        vars.reset();
        if (m_qelim) {
            is_forall = true;
            hoist.pull_quantifier(is_forall, fml, vars);
            m_vars.push_back(vars);
        }
        else {
            hoist.pull_quantifier(is_forall, fml, vars);
            m_vars.back().append(vars);
        }
        do {
            is_forall = !is_forall;
            vars.reset();
            hoist.pull_quantifier(is_forall, fml, vars);
            m_vars.push_back(vars);
        }
        while (!vars.empty());
        SASSERT(m_vars.back().empty()); 

        // initialize levels.
        for (unsigned i = 0; i < m_vars.size(); ++i) {
            max_level lvl;
            if (is_exists(i)) {
                lvl.m_ex = i;
            }
            else {
                lvl.m_fa = i;
            }
            for (unsigned j = 0; j < m_vars[i].size(); ++j) {
                m_elevel.insert(m_vars[i][j].get(), lvl);
            }
        }
        TRACE("qe", tout << fml << "\n";);
    }

    void get_free_vars(expr_ref& fml, app_ref_vector& vars) {
        ast_fast_mark1 mark;
        unsigned sz0 = todo.size();
        todo.push_back(fml);
        while (sz0 != todo.size()) {
            expr* e = todo.back();
            todo.pop_back();
            if (mark.is_marked(e) || is_var(e)) {
                continue;
            }
            mark.mark(e);
            if (is_quantifier(e)) {
                todo.push_back(to_quantifier(e)->get_expr());
                continue;
            }
            SASSERT(is_app(e));
            app* a = to_app(e);
            if (is_uninterp_const(a)) { // TBD generalize for uninterpreted functions.
                vars.push_back(a);
            }
            for (unsigned i = 0; i < a->get_num_args(); ++i) {
                todo.push_back(a->get_arg(i));
            }
        }
    }

    /** 
        \brief create propositional abstraction of formula by replacing atomic sub-formulas by fresh 
        propositional variables, and adding definitions for each propositional formula on the side.
        Assumption is that the formula is quantifier-free.
    */
    void abstract_atoms(expr* fml, max_level& level) {
        expr_mark mark;
        ptr_vector<expr> args;
        app_ref r(m), eq(m);
        app* p;
        unsigned sz0 = todo.size();
        todo.push_back(fml);
        m_trail.push_back(fml);
        while (sz0 != todo.size()) {
            app* a = to_app(todo.back());
            todo.pop_back();
            if (mark.is_marked(a)) {
                continue;
            }

            mark.mark(a);
            if (m_lit2pred.find(a, p)) {
                level.merge(m_elevel.find(p));
                continue;
            }

            if (is_uninterp_const(a) && m.is_bool(a)) {
                max_level l = m_elevel.find(a);
                m_moves.insert(a, l);
                level.merge(l);
                add_pred(a, a);
                continue;
            }

            unsigned sz = a->get_num_args();
            for (unsigned i = 0; i < sz; ++i) {
                expr* f = a->get_arg(i);
                if (!mark.is_marked(f)) {
                    todo.push_back(f);
                }
            } 

            bool is_boolop = 
                (a->get_family_id() == m.get_basic_family_id()) &&
                (!m.is_eq(a)       || m.is_bool(a->get_arg(0))) && 
                (!m.is_distinct(a) || m.is_bool(a->get_arg(0)));

            if (!is_boolop && m.is_bool(a)) {
                TRACE("qe", tout << mk_pp(a, m) << "\n";);
                r = fresh_bool("p");
                add_pred(r, a);
                eq = m.mk_eq(a, r);
                m_fa.assert_expr(eq);
                m_ex.assert_expr(eq);
                max_level l = compute_level(a);
                m_elevel.insert(r, l);
                m_moves.insert(r, l);
                level.merge(l);
            }
        }
    }

    // optional pass to replace atoms by predicates 
    // so that SMT core works on propositional
    // abstraction only.
    expr_ref mk_abstract(expr* fml) {
        expr_ref_vector trail(m), args(m);
        obj_map<expr, expr*> cache;
        app* b;
        expr_ref r(m);
        unsigned sz0 = todo.size();
        todo.push_back(fml);
        while (sz0 != todo.size()) {
            app* a = to_app(todo.back());
            if (cache.contains(a)) {
                todo.pop_back();
                continue;
            }
            if (m_lit2pred.find(a, b)) {
                cache.insert(a, b);
                todo.pop_back();
                continue;
            }
            unsigned sz = a->get_num_args();
            bool diff = false;
            args.reset();
            for (unsigned i = 0; i < sz; ++i) {
                expr* f = a->get_arg(i), *f1;
                if (cache.find(f, f1)) {
                    args.push_back(f1);
                    diff |= f != f1;
                }
                else {
                    todo.push_back(f);
                }
            } 
            if (sz == args.size()) {
                if (diff) {
                    r = m.mk_app(a->get_decl(), sz, args.c_ptr());
                    trail.push_back(r);
                }
                else {
                    r = a;
                }
                cache.insert(a, r);
                todo.pop_back();
            }
        }
        return expr_ref(cache.find(fml), m);
    }

    void mk_concrete(expr_ref_vector& fmls) {
        obj_map<expr,expr*> cache;
        expr_ref_vector trail(m);
        expr* p;
        app_ref r(m);
        ptr_vector<expr> args;
        unsigned sz0 = todo.size();
        todo.append(fmls.size(), (expr*const*)fmls.c_ptr());
        while (sz0 != todo.size()) {
            app* a = to_app(todo.back());
            if (cache.contains(a)) {
                todo.pop_back();
                continue;
            }
            if (m_pred2lit.find(a, p)) {
                cache.insert(a, p);
                todo.pop_back();
                continue;
            }
            unsigned sz = a->get_num_args();
            args.reset();
            bool diff = false;
            for (unsigned i = 0; i < sz; ++i) {
                expr* f = a->get_arg(i), *f1;
                if (cache.find(f, f1)) {
                    args.push_back(f1);
                    diff |= f != f1;
                }
                else {
                    todo.push_back(f);
                }
            } 
            if (args.size() == sz) {
                if (diff) {
                    r = m.mk_app(a->get_decl(), sz, args.c_ptr());
                }
                else {
                    r = to_app(a);
                }
                cache.insert(a, r);
                trail.push_back(r);
                todo.pop_back();
            }
        }
        for (unsigned i = 0; i < fmls.size(); ++i) {
            fmls[i] = to_app(cache.find(fmls[i].get()));
        }
    }

    max_level compute_level(app* e) {
        unsigned sz0 = todo.size();
        todo.push_back(e);        
        while (sz0 != todo.size()) {
            app* a = to_app(todo.back());
            if (m_elevel.contains(a)) {
                todo.pop_back();
                continue;
            }
            max_level lvl, lvl0;
            bool has_new = false;
            for (unsigned i = 0; i < a->get_num_args(); ++i) {
                app* arg = to_app(a->get_arg(i));
                if (m_elevel.find(arg, lvl)) {
                    lvl0.merge(lvl);
                }
                else {
                    todo.push_back(arg);
                    has_new = true;
                }
            }
            if (!has_new) {
                m_elevel.insert(a, lvl0);
                todo.pop_back();
            }
        }
        return m_elevel.find(e);
    }

    void get_core(expr_ref_vector& core, unsigned level) {
        get_kernel(level).get_core(core);
    }

    void check_cancel() {
        if (m_cancel) {
            throw tactic_exception(TACTIC_CANCELED_MSG);
        }
    }

    void display(std::ostream& out) const {
        out << "level: " << m_level << "\n";
        out << "pred2lit:\n";
        obj_map<expr, expr*>::iterator it = m_pred2lit.begin(), end = m_pred2lit.end();
        for (; it != end; ++it) {
            out << mk_pp(it->m_key, m) << " |-> " << mk_pp(it->m_value, m) << "\n";
        }
        m_moves.display(out);
    }

    void display(std::ostream& out, model& model) const {
        display(out);
        model_v2_pp(out, model);
    }

    void display(std::ostream& out, expr_ref_vector const& asms) const {
        expr* e = 0;
        max_level lvl;
        for (unsigned i = 0; i < asms.size(); ++i) {
            out << mk_pp(asms[i], m);
            if (m_elevel.find(asms[i], lvl)) {
                lvl.display(out << " - ");
            }
            if (m_pred2lit.find(asms[i], e)) {
                out << " : " << mk_pp(e, m);
            }
            out << "\n";
        }
    }

    void project_qe(expr_ref_vector& core) {
        SASSERT(m_level == 1);
        expr_ref fml(m), fml0(m);
        model& mdl = *m_model.get();
        app_ref_vector vars(m);


        get_core(core, 1);
        for (unsigned i = 1; i < m_vars.size(); ++i) {
            vars.append(m_vars[i]);
        }

        mk_concrete(core);
        m_mbp(vars, mdl, core);
        fml = mk_not(mk_and(core));
        m_ex.assert_expr(fml);
        m_answer.push_back(fml);
        pop(1);
    }

    void project(expr_ref_vector& core) {
        get_core(core, m_level);
        TRACE("qe", display(tout); display(tout << "core\n", core););
        SASSERT(m_level >= 2);
        app_ref_vector vars(m);
        expr_ref fml(m), fml0(m), fml1(m); 
        max_level level;
        model& mdl = *m_model.get();

        for (unsigned i = m_level-1; i < m_vars.size(); ++i) {
            vars.append(m_vars[i]);
        }
        mk_concrete(core);
        fml0 = mk_and(core);
        m_mbp(vars, mdl, core);
        fml = mk_and(core);
        abstract_atoms(fml, level);
        fml = mk_abstract(fml);
        fml1 = mk_not(fml);
        unsigned num_scopes = 0;
        
        if (level.max() == UINT_MAX) {
            num_scopes = 2*(m_level/2);
        }
        else {
            SASSERT(level.max() + 2 <= m_level);
            SASSERT(0 == ((m_level - level.max()) % 2));
            num_scopes = m_level - level.max();
        }
        TRACE("qe", tout << "backtrack: " << num_scopes << "\nproject:\n" << fml0 << "\n|->\n" << fml << "\n";);
        pop(num_scopes); 
        get_kernel(m_level).assert_expr(fml1);
    }

public:

    qsat(ast_manager& m, params_ref const& p, bool qelim):
        m(m),
        m_mbp(m),
        m_fa(m),
        m_ex(m),
        m_moves(*this),
        m_trail(m),
        m_answer(m),
        m_level(0),
        m_cancel(false),
        m_qelim(qelim)
    {
        reset();
    }

    virtual ~qsat() {
        reset();
    }
    
    void updt_params(params_ref const & p) {
    }

    void collect_param_descrs(param_descrs & r) {
    }

    void operator()(/* in */  goal_ref const & in, 
                    /* out */ goal_ref_buffer & result, 
                    /* out */ model_converter_ref & mc, 
                    /* out */ proof_converter_ref & pc,
                    /* out */ expr_dependency_ref & core) {
        tactic_report report("qsat-tactic", *in);
        ptr_vector<expr> fmls;
        expr_ref fml(m);
        max_level level;
        mc = 0; pc = 0; core = 0;
        in->get_formulas(fmls);
        fml = mk_and(m, fmls.size(), fmls.c_ptr());

        // for now:
        // fail if cores.  (TBD)
        // fail if proofs. (TBD)

        m_fmc = alloc(filter_model_converter, m);
        reset();
        TRACE("qe", tout << fml << "\n";);
        if (m_qelim) {
            fml = mk_not(fml);
        }
        hoist(fml);
        abstract_atoms(fml, level);
        fml = mk_abstract(fml);
        m_ex.assert_expr(fml);
        m_fa.assert_expr(m.mk_not(fml));
        TRACE("qe", tout << "ex: " << fml << "\n";);
        lbool is_sat = check_sat();
        
        switch (is_sat) {
        case l_false:
            in->reset();
            in->inc_depth();
            if (m_qelim) {
                fml = ::mk_and(m_answer);
                in->assert_expr(fml);
            }
            else {
                in->assert_expr(m.mk_false());
            }
            result.push_back(in.get());
            break;
        case l_true:
            in->reset();
            in->inc_depth();
            result.push_back(in.get());
            if (in->models_enabled()) {
                mc = model2model_converter(m_model.get());
                mc = concat(m_fmc.get(), mc.get());
            }
            break;
        case l_undef:
            result.push_back(in.get());
            std::string s = m_ex.k().last_failure_as_string() + m_fa.k().last_failure_as_string();
            throw tactic_exception(s.c_str()); 
        }
        
    }

    void collect_statistics(statistics & st) const {
        st.copy(m_st);
        st.update("qsat num predicates", m_stats.m_num_predicates);
        st.update("qsat num rounds", m_stats.m_num_rounds); 
    }

    void reset_statistics() {
        m_stats.reset();
        m_fa.k().reset_statistics();
        m_ex.k().reset_statistics();        
    }

    void cleanup() {
        reset();
        set_cancel(false);
    }

    void set_logic(symbol const & l) {
    }

    void set_progress_callback(progress_callback * callback) {
    }

    tactic * translate(ast_manager & m) {
        return alloc(qsat, m, m_params, m_qelim);
    }

    virtual void set_cancel(bool f) {
        m_fa.k().set_cancel(f);        
        m_ex.k().set_cancel(f);        
        m_cancel = f;
    }

};

};

tactic * mk_qsat_tactic(ast_manager& m, params_ref const& p) {
    return alloc(qe::qsat, m, p, false);
}

tactic * mk_qe2_tactic(ast_manager& m, params_ref const& p) {
    return alloc(qe::qsat, m, p, true);
}

