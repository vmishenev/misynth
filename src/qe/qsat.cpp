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

using namespace qe;


class qsat::impl {
    ast_manager&      m;
    qe::mbp           mbp;
    smt_params        m_smtp;
    smt::kernel       m_kernel;
    app_ref           m_fml_pred;   // predicate that encodes top-level formula
    app_ref           m_nfml_pred;  // predicate that encodes top-level formula
    app_ref_vector    m_atoms;      // predicates that encode atomic subformulas
    unsigned_vector   m_atoms_lim;
    vector<app_ref_vector>  m_vars;  // variables from alternating prefixes.
    vector<app_ref_vector>  m_vals;
    vector<app_ref_vector>  m_preds;
    app_ref_vector          m_assumptions;
    vector<expr_ref_vector> m_replay;
    unsigned_vector         m_assumptions_lim;
    unsigned                m_level;
    model_ref               m_model;
    obj_map<app, expr*>     m_pred2lit;  // maintain definitions of predicates.
    obj_map<expr, app*>     m_lit2pred;  // maintain reverse mapping to predicates
    obj_map<app, unsigned>  m_pred2level; // maintain level of predicates.
    filter_model_converter_ref m_fmc;


    /**
       \brief check alternating satisfiability.
       Even levels are existential, odd levels are universal.
     */
    lbool check_sat() {
        lbool res;
        if (initialize(res)) {
            return res;
        }
        while (true) {
            app_ref_vector asms(m_assumptions);
            model_ref mdl;
            assume_tail(m_level, asms);
            res = check_sat(asms, get_fml());            
            switch (res) {
            case l_true:
                m_kernel.get_model(mdl);                
                if (m_level == 0) {
                    m_model = mdl;
                }
                update_tail(*mdl.get(), m_level);
                TRACE("qe", display(tout, *mdl.get()); display(tout, asms););
                project(asms, mdl);
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
                backtrack(asms);
                break;
            case l_undef:
                return res;
            }
        }
        return l_undef;
    }

    bool initialize(lbool& result) {
        m_vals.reset();
        m_vals.append(m_vars);
        expr_ref val(m);
        app_ref_vector emp(m);
        model_ref mdl;
        result = l_undef;
        lbool r = check_sat(emp, m_fml_pred);
        if (r != l_true) {
            result = r;
            return true;
        }
        m_kernel.get_model(mdl);
        update_tail(*mdl.get(), 0);
        r = check_sat(emp, m_nfml_pred);
        switch (r) {
        case l_false:
            result = l_true;
            m_model = mdl.get();
            return true;
        case l_undef:
            result = l_undef;
            return true;
        default:
            break;
        }
        m_kernel.get_model(mdl);
        update_tail(*mdl.get(), 1);
        return false;
    }

    void project(app_ref_vector& imp, model_ref& mdl) {
        if (m_level == 0) {
            return;
        }

        app_ref_vector vars(m);
        expr_ref fml(m);

        for (unsigned i = m_level; i < m_vars.size(); ++i) {
            vars.append(m_vars[i]);
        }
        assume_tail(m_level + 2, imp);
        for (unsigned i = 0; i < imp.size(); ++i) {
            imp[i] = to_app(m_pred2lit.find(to_app(imp[i].get())));
        }
        
        fml = mk_and(imp);
        mbp(vars, mdl, fml);
        fml = m.mk_not(fml);
        persist_assertion(m_level - 1, fml);
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
        persist_assertion(level, fml);
    }

    void persist_assertion(unsigned level, expr* fml) {
        expr_ref fml2(m);
        fml2 = m.mk_implies(get_fml(level), fml);
        m_kernel.assert_expr(fml2);
        m_replay.back().push_back(fml2);        
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
        m_assumptions_lim.push_back(m_assumptions.size());
        m_atoms_lim.push_back(m_atoms.size());
        m_level++;
        m_kernel.push(); 
        m_replay.push_back(expr_ref_vector(m));
        if (m_level >= 2) {
            m_assumptions.append(m_preds[m_level-2]);            
        }
    }

    void pop(unsigned num_scopes) {
        SASSERT(num_scopes <= m_level);
        expr_ref_vector replay(m);
        m_level -= num_scopes;
        for (unsigned i = 0; i < num_scopes; ++i) {
            replay.append(m_replay.back());
            m_replay.pop_back();
        }
        for (unsigned i = m_assumptions_lim[m_level]; i < m_assumptions.size(); ++i) {
            del_pred(to_app(m_assumptions[i].get()));
        }
        m_atoms.resize(m_atoms_lim[m_level]);
        m_assumptions.resize(m_assumptions_lim[m_level]);
        m_assumptions_lim.resize(m_level);
        m_atoms_lim.resize(m_level);
        m_kernel.pop(num_scopes);
        for (unsigned i = 0; i < replay.size(); ++i) {
            m_kernel.assert_expr(replay[i].get());
        }
        m_replay.back().append(replay);
    }

    void del_pred(app* p) {
        expr* lit;
        if (m_pred2lit.find(p, lit)) {
            m_lit2pred.remove(lit);
            m_pred2lit.remove(p);
            m_pred2level.remove(p);
        }
    }

    void add_pred(app* p, app* lit, unsigned level) {
        if (p != lit) {
            m_kernel.assert_expr(m.mk_eq(p, lit));
        }
        m_pred2lit.insert(p, lit);
        m_lit2pred.insert(lit, p);
        m_pred2level.insert(p, level);        
        m_atoms.push_back(p);
    }

    void update_tail(model& mdl, unsigned start) {
        expr_ref val(m);
        app_ref pred(m), eq(m);
        for (unsigned i = start; i < m_vars.size(); i += 2) {
            for (unsigned j = 0; j < m_vars[i].size(); ++j) {
                del_pred(m_preds[i][j].get());
                expr* var = m_vars[i][j].get();
                VERIFY (mdl.eval(var, val));
                m_vals[i][j] = to_app(val);
                eq = m.mk_eq(var, val);
                pred = m.mk_fresh_const("eq", m.mk_bool_sort());
                m_preds[i][j] = pred;
                add_pred(pred, eq, i);
            }
        }
    }

    void assume_tail(unsigned level, app_ref_vector& assumptions) {
        unsigned start = (level > 0)?(level - 1):(m_level + 1);
        for (unsigned i = start; i < m_vars.size(); i += 2) {
            assumptions.append(m_preds[i]);
        }
    }


    void reset() {
        m_level = 0;
        m_vars.reset();
        m_vals.reset();
        m_assumptions.reset();
        m_assumptions_lim.reset();
        m_replay.push_back(expr_ref_vector(m));
    }

    app* get_fml(unsigned lvl) {
        return is_exists(lvl)?m_fml_pred:m_nfml_pred;
    }

    app* get_fml() {
        return get_fml(m_level);
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
        m_vals.push_back(vars);
        m_preds.push_back(vars);
        vars.reset();
        hoist.pull_quantifier(is_forall, fml, vars);
        m_vars.back().append(vars);
        do {
            is_forall = !is_forall;
            vars.reset();
            hoist.pull_quantifier(is_forall, fml, vars);
            m_vars.push_back(vars);
            m_vals.push_back(vars);
            m_preds.push_back(vars);
        }
        while (!vars.empty());
        SASSERT(m_vars.back().empty()); 
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
    void mk_abstract(expr* fml) {
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
                add_pred(a, a, 0);
            }
            else {
                // TBD: nested Booleans.    
                SASSERT(m.is_bool(e));
                r = m.mk_fresh_const("p", m.mk_bool_sort());
                cache.insert(e, r);
                add_pred(r, a, 0);
            }
        }
        r = m.mk_fresh_const("fml", m.mk_bool_sort());
        m_fml_pred  = r;
        m_nfml_pred = m.mk_not(r);
        m_kernel.assert_expr(m.mk_eq(r, cache.find(fml)));
    }

    /** 
        \brief use dual propagation to minimize model.
    */
    bool minimize_assignment(app_ref_vector& assignment, app* not_fml) {        
        bool result = false;
        assignment.push_back(not_fml);
        lbool res = m_kernel.check(assignment);
        switch (res) {
        case l_true:
            UNREACHABLE();
            break;
        case l_undef:
            break;
        case l_false: 
            result = true;
            get_core(assignment, not_fml);
            break;
        }
        return result;
    }

    lbool check_sat(app_ref_vector& assignment, app* fml) {
        assignment.push_back(fml);
        lbool res = m_kernel.check(assignment);
        switch (res) {
        case l_true: 
            if (!get_implicant(assignment, fml)) {
                res = l_undef;
            }
            break;
        case l_undef:            
            break;
        case l_false:
            get_core(assignment, fml);
            break;
        }
        return res;
    }

    bool get_implicant(app_ref_vector& impl, expr* fml) {
        model_ref mdl;
        expr_ref tmp(m);
        impl.reset();
        m_kernel.get_model(mdl);
        for (unsigned i = 0; i < m_atoms.size(); ++i) {
            app* p = m_atoms[i].get();
            if (mdl->eval(p, tmp)) {
                if (m.is_true(tmp)) {
                    impl.push_back(p);
                }
                else if (m.is_false(tmp)) {
                    impl.push_back(m.mk_not(p));
                }
            }                
        }
        app_ref not_fml = mk_not(fml);
        return minimize_assignment(impl, not_fml);
    }

    void get_core(app_ref_vector& core, expr* exclude) {
        unsigned sz = m_kernel.get_unsat_core_size();
        core.reset();
        for (unsigned i = 0; i < sz; ++i) {
            app* e = to_app(m_kernel.get_unsat_core_expr(i));
            if (e != exclude) {
                core.push_back(e);
            } 
        }        
    }

    app_ref mk_not(expr* e) {
        return app_ref(to_app(::mk_not(m, e)), m);
    }

    void display(std::ostream& out) const {
        out << "level: " << m_level << "\n";
        out << "fml: "   << m_fml_pred  << "\n";
        out << "!fml: "  << m_nfml_pred << "\n";
        out << "atoms:\n";
        for (unsigned i = 0; i < m_atoms.size(); ++i) {
            out << mk_pp(m_atoms[i], m) << "\n";
        }
        out << "pred2lit:\n";
        obj_map<app, expr*>::iterator it = m_pred2lit.begin(), end = m_pred2lit.end();
        for (; it != end; ++it) {
            out << mk_pp(it->m_key, m) << " |-> " << mk_pp(it->m_value, m) << "\n";
        }
        out << "assumptions:\n";
        for (unsigned i = 0; i < m_assumptions.size(); ++i) {
            out << mk_pp(m_assumptions[i], m) << "\n";
        }
        out << "values:\n";
        for (unsigned i = 0; i < m_vars.size(); ++i) {
            out << (is_exists(i)?"E: ":"A: ");
            for (unsigned j = 0; j < m_vars[i].size(); ++j) {
                out << mk_pp(m_vars[i][j], m) << " |-> " << mk_pp(m_vals[i][j], m) << " ";
            }
            out << "\n";
        }        
    }

    void display(std::ostream& out, model& model) const {
        display(out);
        model_v2_pp(out, model);
    }

    void display(std::ostream& out, app_ref_vector const& asms) const {
        for (unsigned i = 0; i < asms.size(); ++i) {
            out << mk_pp(asms[i], m) << " - " << get_level(asms[i]) << " : " << mk_pp(m_pred2lit.find(asms[i]), m) << "\n";
        }
    }

public:
    impl(ast_manager& m):
        m(m),
        mbp(m),
        m_kernel(m, m_smtp),
        m_fml_pred(m),
        m_nfml_pred(m),
        m_atoms(m),
        m_assumptions(m),
        m_level(0)
    {}
    
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

        reset();
        hoist(fml);
        mk_abstract(fml);
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
            throw tactic_exception(m_kernel.last_failure_as_string().c_str());
        }
        
    }

    void collect_statistics(statistics & st) const {

    }
    void reset_statistics() {
    }

    void cleanup() {
    }

    void set_logic(symbol const & l) {
    }

    void set_progress_callback(progress_callback * callback) {
    }

    tactic * translate(ast_manager & m) {
        return 0;
        // return alloc(qsat, m);
    }

};

qsat::qsat(ast_manager& m) {
    m_impl = alloc(impl, m);
}

qsat::~qsat() {
    dealloc(m_impl);
}

void qsat::updt_params(params_ref const & p) {
    m_impl->updt_params(p);
}
void qsat::collect_param_descrs(param_descrs & r) {
    m_impl->collect_param_descrs(r);
}
void qsat::operator()(/* in */  goal_ref const & in, 
                      /* out */ goal_ref_buffer & result, 
                      /* out */ model_converter_ref & mc, 
                      /* out */ proof_converter_ref & pc,
                      /* out */ expr_dependency_ref & core) {
    (*m_impl)(in, result, mc, pc, core);
}

void qsat::collect_statistics(statistics & st) const {
    m_impl->collect_statistics(st);
}
void qsat::reset_statistics() {
    m_impl->reset_statistics();
}
void qsat::cleanup() {
    m_impl->cleanup();
}
void qsat::set_logic(symbol const & l) {
    m_impl->set_logic(l);
}
void qsat::set_progress_callback(progress_callback * callback) {
    m_impl->set_progress_callback(callback);
}
tactic * qsat::translate(ast_manager & m) {
    return m_impl->translate(m);
}


