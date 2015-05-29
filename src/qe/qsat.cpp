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

using namespace qe;


struct pdef_t {
    expr_ref  m_pred;
    expr_ref  m_atom;
    pdef_t(expr_ref& p, expr* a):
        m_pred(p),
        m_atom(a, p.get_manager())
    {}
};

class qsat::impl {
    ast_manager&      m;
    qe::mbp           mbp;
    smt_params        m_smtp;
    smt::kernel       m_kernel;
    expr_ref          m_fml_pred;   // predicate that encodes top-level formula
    expr_ref          m_nfml_pred;  // predicate that encodes top-level formula
    expr_ref_vector   m_atoms;      // predicates that encode atomic subformulas
    unsigned_vector   m_atoms_lim;
    vector<app_ref_vector>  m_vars;  // variables from alternating prefixes.
    expr_ref_vector         m_assumptions;
    vector<expr_ref_vector> m_replay;
    unsigned_vector         m_assumptions_lim;
    unsigned                m_level;
    model_ref               m_model;
    obj_map<app, expr*>     m_pred2lit;  // maintain definitions of predicates.


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
        
    }

    /**
       \brief check alternating satisfiability.
       Even levels are existential, odd levels are universal.
     */
    lbool check_sat() {
        while (true) {
            expr_ref_vector asms(m_assumptions);
            lbool res = check_sat(asms, get_fml());
            switch (res) {
            case l_true:
                if (m_level == 0) {
                    m_kernel.get_model(m_model);
                }
                project(asms);
                push();
                m_assumptions.append(asms);
                break;
            case l_false:
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

    void project(expr_ref_vector& imp) {
        app_ref_vector vars(m);
        model_ref mdl;
        m_kernel.get_model(mdl);
        for (unsigned i = m_level+1; i < m_vars.size(); ++i) {
            vars.append(m_vars[i]);
        }
        expr_ref fml(m);
        fml = mk_and(m, imp.size(), imp.c_ptr());
        mbp(vars, mdl, fml);
        imp.reset();
        flatten_and(fml, imp);
        app_ref p(m);
        for (unsigned i = 0; i < imp.size(); ++i) {
            p = m.mk_fresh_const("p", m.mk_bool_sort());
            m_kernel.assert_expr(m.mk_eq(p, imp[i].get()));
            m_assumptions.push_back(p);
            m_pred2lit.insert(p, imp[i].get());
            m_atoms.push_back(p);
        }
    }

    void backtrack(expr_ref_vector const& core) {
        unsigned level = ((m_level % 2) == 0)?0:1;
        for (unsigned i = 0; i < core.size(); ++i) {
            level = std::max(level, get_level(core[i]));
        }
        SASSERT(level < m_level);
        pop(m_level - level);
        expr_ref ncore(m);
        ncore = ::mk_not(m, mk_and(m, core.size(), core.c_ptr()));
        m_kernel.assert_expr(ncore);
        m_replay.back().push_back(ncore);
    }

    unsigned get_level(expr* p) const {
        unsigned j = 0;
        for (unsigned i = 0; i < m_assumptions_lim.size(); ++i) {
            for (; j < m_assumptions_lim[i]; ++j) {
                if (m_assumptions[j]  == p)
                    return i;
            }
        }
        UNREACHABLE();
        return 0;
    }

    void push() {
        m_assumptions_lim.push_back(m_assumptions.size());
        m_atoms_lim.push_back(m_atoms.size());
        m_level++;
        m_kernel.push(); 
        m_replay.push_back(expr_ref_vector(m));
    }

    void pop(unsigned num_scopes) {
        SASSERT(num_scopes <= m_level);
        expr_ref_vector replay(m);
        while (num_scopes > 0) {
            replay.append(m_replay.back());
            m_replay.pop_back();
            --num_scopes;
        }
        for (unsigned i = m_assumptions_lim[m_level]; i < m_assumptions.size(); ++i) {
            m_pred2lit.remove(to_app(m_assumptions[i].get()));
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

    void reset() {
        m_level = 0;
        m_assumptions.reset();
        m_assumptions_lim.reset();
        m_replay.push_back(expr_ref_vector(m));
    }

    expr* get_fml() {
        if ((m_level % 2) == 0) {
            return m_fml_pred;
        }
        else {
            return m_nfml_pred;
        }
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
        \brief create propositional abstration of formula by replacing atomic sub-formulas by fresh 
        propositional variables, and adding definitions for each propositional formula on the side.
        Assumption is that the formula is quantifier-free.
    */
    void mk_abstract(expr_ref& fml, vector<pdef_t>& pdefs) {
        expr_ref_vector todo(m), trail(m);
        obj_map<expr,expr*> cache;
        ptr_vector<expr> args;
        expr_ref r(m);
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
                for (unsigned i = 0; i < sz; ++i) {
                    expr* f = a->get_arg(i);
                    if (cache.find(f, f)) {
                        args.push_back(f);
                    }
                    else {
                        todo.push_back(f);
                    }
                } 
                if (args.size() == sz) {
                    r = m.mk_app(a->get_decl(), sz, args.c_ptr());
                    cache.insert(e, r);
                    trail.push_back(r);
                    todo.pop_back();
                }
            }
            else if (is_uninterp_const(a)) {
                cache.insert(e, e);
            }
            else {
                // TBD: nested Booleans.    

                r = m.mk_fresh_const("p",m.mk_bool_sort());
                trail.push_back(r);
                cache.insert(e, r);
                pdefs.push_back(pdef_t(r, e));
            }
        }
        fml = cache.find(fml);
    }

    /** 
        \brief use dual propagation to minimize model.
    */
    bool minimize_assignment(expr_ref_vector& assignment, expr* not_fml) {        
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

    lbool check_sat(expr_ref_vector& assignment, expr* fml) {
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

    bool get_implicant(expr_ref_vector& impl, expr* fml) {
        model_ref mdl;
        expr_ref tmp(m);
        impl.reset();
        m_kernel.get_model(mdl);
        for (unsigned i = 0; i < m_atoms.size(); ++i) {
            expr* p = m_atoms[i].get();
            if (mdl->eval(p, tmp)) {
                if (m.is_true(tmp)) {
                    impl.push_back(p);
                }
                else if (m.is_false(tmp)) {
                    impl.push_back(m.mk_not(p));
                }
            }                
        }
        expr_ref not_fml = mk_not(fml);
        return minimize_assignment(impl, not_fml);
    }

    void get_core(expr_ref_vector& core, expr* exclude) {
        unsigned sz = m_kernel.get_unsat_core_size();
        core.reset();
        for (unsigned i = 0; i < sz; ++i) {
            expr* e = m_kernel.get_unsat_core_expr(i);
            if (e != exclude) {
                core.push_back(e);
            } 
        }        
    }

    expr_ref mk_not(expr* e) {
        return expr_ref(::mk_not(m, e), m);
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


