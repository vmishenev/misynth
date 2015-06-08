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
#include "qe_util.h"
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
        stats() { reset(); }
        void reset() { memset(this, 0, sizeof(*this)); }
    };
    
    class kernel {
        ast_manager& m;
        smt_params   m_smtp;
        smt::kernel  m_kernel;
        vector<expr_ref_vector> m_replay;

    public:
        kernel(ast_manager& m):
            m(m),
            m_kernel(m, m_smtp)
        {
            m_smtp.m_model = true;
            m_smtp.m_relevancy_lvl = 0;
            m_replay.push_back(expr_ref_vector(m));
        }
            
        smt::kernel& k() { return m_kernel; }
        smt::kernel const& k() const { return m_kernel; }

        void push() {
            m_kernel.push();
            m_replay.push_back(expr_ref_vector(m));            
        }
        void pop(unsigned num_scopes) {
            expr_ref_vector replay(m);
            for (unsigned i = 0; i < num_scopes; ++i) {
                replay.append(m_replay.back());
                m_replay.pop_back();
            }
            m_kernel.pop(num_scopes);
            for (unsigned i = 0; i < replay.size(); ++i) {
                m_kernel.assert_expr(replay[i].get());
            }
            m_replay.back().append(replay);
        }

        void assert_expr(expr* e) {
            m_kernel.assert_expr(e);
        }

        void persist_expr(expr* e) {
            m_kernel.assert_expr(e);
            m_replay.back().push_back(e);
        }

        void get_core(app_ref_vector& core) {
            unsigned sz = m_kernel.get_unsat_core_size();
            core.reset();
            for (unsigned i = 0; i < sz; ++i) {
                core.push_back(to_app(m_kernel.get_unsat_core_expr(i)));
            }
        }
    };

    // trail encapsulating model assignment.
    class move_trail {
        ast_manager& m;
        qsat&        q;
        vector<app_ref_vector> const& m_vars;
        vector<app_ref_vector>  m_vals;
        vector<app_ref_vector>  m_preds;

    public:
        move_trail(qsat& _q):
            m(_q.m),
            q(_q),
            m_vars(q.m_vars)

        {}
        
        void init() {
            m_vals.reset();
            m_preds.reset();
            m_vals.append(m_vars);            
            m_preds.append(m_vars);
        }        
                
        void get_assumptions(app_ref_vector& asms) const {
            asms.reset();
            unsigned level = q.m_level;
            if (level == 0) {
                return;
            }
            for (unsigned i = 0; i + 2 < level; ++i) {
                asms.append(m_preds[i]);
            }
            for (unsigned i = level - 1; i < m_preds.size(); i += 2) {
                asms.append(m_preds[i]);
            }
        }

        void reset() {
            m_vals.reset();
            m_preds.reset();
        }
        
        void update_tail(model& mdl) {
            SASSERT(q.m_level > 0);
            unsigned start = q.m_level-1;
            expr_ref val(m);
            app_ref pred(m), eq(m);
            for (unsigned i = start; i < m_vars.size(); i += 2) {
                for (unsigned j = 0; j < m_vars[i].size(); ++j) {
                    q.del_pred(m_preds[i][j].get());
                    app* var = m_vars[i][j];
                    VERIFY (mdl.eval(var, val));
                    m_vals[i][j] = to_app(val);
                    if (m.is_bool(var)) {
                        SASSERT(m.is_true(val) || m.is_false(val));
                        pred = m.is_true(val)?var:m.mk_not(var);
                        eq = pred;
                    }
                    else {
                        pred = q.fresh_bool("eq");
                        eq = m.mk_eq(var, val);
                    }
                    q.add_pred(pred, eq, i);
                    m_preds[i][j] = pred;
                }
            }
        }

        void display(std::ostream& out) const {
            app_ref_vector asms(m);
            get_assumptions(asms);
            out << "assumptions:\n";
            for (unsigned i = 0; i < asms.size(); ++i) {
                out << mk_pp(asms[i].get(), m) << "\n";
            }
            out << "values:\n";
            for (unsigned i = 0; i < m_vars.size(); ++i) {
                out << (q.is_exists(i)?"E: ":"A: ");
                for (unsigned j = 0; j < m_vars[i].size(); ++j) {
                    out << mk_pp(m_vars[i][j], m) << " |-> " << mk_pp(m_vals[i][j], m) << " ";
                }
                out << "\n";
            }                    
        }        
    };

    ast_manager&            m;
    params_ref              m_params;
    stats                   m_stats;
    qe::mbp                 m_mbp;
    kernel                  m_fa;
    kernel                  m_ex;
    move_trail              m_moves;
    app_ref_vector          m_atoms;      // predicates that encode atomic subformulas
    vector<app_ref_vector>  m_vars;       // variables from alternating prefixes.
    unsigned                m_level;
    model_ref               m_last_model;
    model_ref               m_model;
    obj_map<app, expr*>     m_pred2lit;    // maintain definitions of predicates.
    obj_map<expr, app*>     m_lit2pred;    // maintain reverse mapping to predicates
    obj_map<app, unsigned>  m_pred2level;  // maintain level of predicates.
    filter_model_converter_ref m_fmc;
    volatile bool              m_cancel;


    kernel& get_kernel(unsigned j) {        
        if (is_exists(j)) {
            return m_ex; 
        }
        else {
            return m_fa;
        }
    }
    /**
       \brief check alternating satisfiability.
       Even levels are existential, odd levels are universal.
     */
    lbool check_sat() {
        
        while (true) {
            check_cancel();
            TRACE("qe", display(tout););
            app_ref_vector asms(m);
            m_moves.get_assumptions(asms);
            lbool res = get_kernel(m_level).k().check(asms);
            switch (res) {
            case l_true:
                get_kernel(m_level).k().get_model(m_last_model);
                if (m_level == 0) {
                    m_model = m_last_model;
                }
                TRACE("qe", display(tout, *m_last_model.get()); display(tout, asms););
                push();
                break;
            case l_false:
                TRACE("qe", display(tout); display(tout, asms););                
                if (m_level == 0) {
                    return l_false;
                }
                if (m_level == 1) {
                    return l_true;
                }
                get_core(asms, m_level);
                backtrack(asms);
                break;
            case l_undef:
                return res;
            }
        }
        return l_undef;
    }


    void backtrack(app_ref_vector& core) {
        unsigned level = is_exists(m_level)?0:1;
        for (unsigned i = 0; i < core.size(); ++i) {
            unsigned lvl = get_level(core[i].get());
            if (lvl + 1 < m_level) {
                level = std::max(level, lvl);                
            }
            else {
                core[i] = m.mk_true();                
            }
        }
        SASSERT(level < m_level);
        pop(m_level - level);
        expr_ref fml(::mk_not(m, ::mk_and(core)), m);
        persist_expr(level, fml);
    }

    void display_expr(std::ostream& out, expr* t) {
        ptr_vector<expr> todo;
        todo.push_back(t);
        while (!todo.empty()) {
            app* a = to_app(todo.back());
            todo.pop_back();
            out << a->get_id() << " " << a->get_decl()->get_name() << " " << a->get_num_args() << "  refs: " << a->get_ref_count() << " args: ";
            for (unsigned i = 0; i < a->get_num_args(); ++i) {
                out << a->get_arg(i)->get_id() << " ";
                todo.push_back(a->get_arg(i));
            }
            out << "\n";
        }
    }

    void persist_expr(unsigned level, expr* fml) {
        get_kernel(level).persist_expr(fml);
    }

    bool is_exists(unsigned level) const {
        return (level % 2) == 0;
    }

    bool is_forall(unsigned level) const {
        return is_exists(level+1);
    }

    unsigned get_level(expr* p) const {
        return m_pred2level.find(to_app(p));
    }

    void push() {
        m_level++;
        m_fa.push();
        m_ex.push();
        m_moves.update_tail(*m_last_model.get());
    }

    void pop(unsigned num_scopes) {
        SASSERT(num_scopes <= m_level);
        m_fa.pop(num_scopes);
        m_ex.pop(num_scopes);
        m_level -= num_scopes;
    }

    void del_pred(app* p) {
        expr* lit;
        if (m_pred2lit.find(p, lit)) {
            SASSERT(m_lit2pred.find(lit) == p);
            m_lit2pred.remove(lit);
            m_pred2lit.remove(p);
            m_pred2level.remove(p);
            m.dec_ref(p);
            m.dec_ref(lit);
        }
    }

    void add_pred(app* p, app* lit, unsigned level) {
        if (p != lit) {
            expr_ref eq(m);
            eq = m.mk_eq(p, lit);
            if (level == 0) {
                m_fa.persist_expr(eq);
                m_ex.persist_expr(eq);
            }
            else {
                get_kernel(level).assert_expr(eq);
            }
        }
        m.inc_ref(p);
        m.inc_ref(lit);
        del_pred(p);
        m_pred2lit.insert(p, lit);
        m_lit2pred.insert(lit, p);
        m_pred2level.insert(p, level);
        ++m_stats.m_num_predicates;
    }

    void reset() {
        m_level = 0;
        m_atoms.reset();
        m_moves.reset();
        m_vars.reset();
        m_model = 0;
        m_last_model = 0;
        m_pred2level.reset();
        m_lit2pred.reset();
        m_pred2lit.reset();
        m_fa.k().reset();
        m_ex.k().reset();
        m_cancel = false;
    }

    

    app_ref mk_not(expr* e) {
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
        hoist.pull_quantifier(is_forall, fml, vars);
        m_vars.back().append(vars);
        do {
            is_forall = !is_forall;
            vars.reset();
            hoist.pull_quantifier(is_forall, fml, vars);
            m_vars.push_back(vars);
        }
        while (!vars.empty());
        SASSERT(m_vars.back().empty()); 
        TRACE("qe", tout << fml << "\n";);
    }

    void get_free_vars(expr_ref& fml, app_ref_vector& vars) {
        ast_fast_mark1 mark;
        ptr_vector<expr> todo;
        todo.push_back(fml);
        while (!todo.empty()) {
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
    app_ref mk_abstract(expr* fml) {
        expr_ref_vector todo(m), trail(m);
        obj_map<expr,expr*> cache;
        ptr_vector<expr> args;
        app_ref r(m);
        todo.push_back(fml);
        while (!todo.empty()) {
            expr* e = todo.back();
            if (cache.contains(e)) {
                todo.pop_back();
                continue;
            }
            SASSERT(is_app(e));
            app* a = to_app(e);
            if (a->get_family_id() == m.get_basic_family_id()) {
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
                        r = to_app(e);
                    }
                    cache.insert(e, r);
                    trail.push_back(r);
                    todo.pop_back();
                }
            }
            else if (is_uninterp_const(a)) {
                cache.insert(a, a);
                m_atoms.push_back(a);
            }
            else {
                // TBD: nested Booleans.    
                SASSERT(m.is_bool(a));
                r = fresh_bool("p");
                cache.insert(a, r);
                add_pred(r, a, 0);
                m_atoms.push_back(r);
            }
        }
        r = to_app(cache.find(fml));
        return r;
    }


    void get_core(app_ref_vector& core, unsigned level) {
        get_kernel(level).get_core(core);
    }

    void check_cancel() {
        if (m_cancel) {
            throw tactic_exception(TACTIC_CANCELED_MSG);
        }
    }

    void display(std::ostream& out) const {
        out << "level: " << m_level << "\n";
        out << "atoms:\n";
        for (unsigned i = 0; i < m_atoms.size(); ++i) {
            out << mk_pp(m_atoms[i], m) << "\n";
        }
        out << "pred2lit:\n";
        obj_map<app, expr*>::iterator it = m_pred2lit.begin(), end = m_pred2lit.end();
        for (; it != end; ++it) {
            out << mk_pp(it->m_key, m) << " |-> " << mk_pp(it->m_value, m) << "\n";
        }
        m_moves.display(out);
    }

    void display(std::ostream& out, model& model) const {
        display(out);
        model_v2_pp(out, model);
    }

    void display(std::ostream& out, app_ref_vector const& asms) const {
        expr* e = 0;
        unsigned lvl = 0;
        for (unsigned i = 0; i < asms.size(); ++i) {
            out << mk_pp(asms[i], m);
            if (m_pred2level.find(asms[i], lvl)) {
                out << " - " << lvl; 
            }
            if (m_pred2lit.find(asms[i], e)) {
                out << " : " << mk_pp(e, m);
            }
            out << "\n";
        }
    }

#if 0

    void project(app_ref_vector& imp, model_ref& mdl) {
        if (m_level == 0) {
            return;
        }
        expr* e;

        app_ref_vector vars(m);
        expr_ref fml(m), fml1(m);

        for (unsigned i = m_level; i < m_vars.size(); ++i) {
            vars.append(m_vars[i]);
        }
        for (unsigned i = 0; i < imp.size(); ++i) {
            if (m_pred2lit.find(to_app(imp[i].get()), e)) {
                imp[i] = to_app(e);
            }
        }
        
        fml = mk_and(imp);
        m_mbp(vars, *mdl.get(), fml);
        fml1 = mk_not(fml);
        fml1 = mk_abstract(fml1);
        persist_expr(m_level - 1, fml1);
    }

    /** 
        \brief use dual propagation to minimize model.
    */
    bool minimize_assignment(app_ref_vector& assignment, unsigned level) {        
        bool result = false;
        lbool res = get_kernel(level+1).k().check(assignment);
        switch (res) {
        case l_true:
            UNREACHABLE();
            break;
        case l_undef:
            break;
        case l_false: 
            result = true;
            get_core(assignment, level+1);
            break;
        }
        return result;
    }


    bool get_implicant(app_ref_vector& impl, model_ref& mdl, unsigned level) {
        expr_ref tmp(m);
        impl.reset();
        get_kernel(level).k().get_model(mdl);
        for (unsigned i = 0; i < m_atoms.size(); ++i) {
            app* p = m_atoms[i].get();
            if (mdl->eval(p, tmp)) {
                if (m.is_true(tmp)) {
                    impl.push_back(p);
                }
                else if (m.is_false(tmp)) {
                    impl.push_back(mk_not(p));
                }
            }                
        }
        return minimize_assignment(impl, level);
    }

#endif

public:
    qsat(ast_manager& m, params_ref const& p):
        m(m),
        m_mbp(m),
        m_fa(m),
        m_ex(m),
        m_moves(*this),
        m_atoms(m),
        m_level(0),
        m_cancel(false)
    {
        reset();
    }

    virtual ~qsat() {}
    
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
        mc = 0; pc = 0; core = 0;
        in->get_formulas(fmls);
        fml = mk_and(m, fmls.size(), fmls.c_ptr());

        // for now:
        // fail if cores.  (TBD)
        // fail if proofs. (TBD)

        m_fmc = alloc(filter_model_converter, m);
        reset();
        TRACE("qe", tout << fml << "\n";);
        hoist(fml);
        fml = mk_abstract(fml);
        m_ex.assert_expr(fml);
        m_fa.assert_expr(m.mk_not(fml));
        lbool is_sat = check_sat();
        
        switch (is_sat) {
        case l_false:
            in->reset();
            in->assert_expr(m.mk_false());
            result.push_back(in.get());
            break;
        case l_true:
            in->reset();
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
        m_fa.k().collect_statistics(st);
        m_ex.k().collect_statistics(st);
        st.update("num predicates", m_stats.m_num_predicates);
    }
    void reset_statistics() {
        m_stats.reset();
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
        return alloc(qsat, m, m_params);
    }

    virtual void set_cancel(bool f) {
        m_fa.k().set_cancel(f);        
        m_ex.k().set_cancel(f);        
        m_cancel = f;
    }

};

};

tactic * mk_qsat_tactic(ast_manager& m, params_ref const& p) {
    return alloc(qe::qsat, m, p);
}

