/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    smt_consequences.cpp

Abstract:

    Tuned consequence finding for smt_context.

Author:

    nbjorner 2016-07-28.

Revision History:

--*/
#include "smt_context.h"
#include "ast_util.h"

namespace smt {

    expr_ref context::antecedent2fml(uint_set const& vars) {
        expr_ref_vector premises(m_manager);
        uint_set::iterator it = vars.begin(), end = vars.end();
        for (; it != end; ++it) {
            expr* e =  bool_var2expr(*it);
            premises.push_back(get_assignment(*it) != l_false ? e : m_manager.mk_not(e));
        }
        return mk_and(premises);
    }

    void context::extract_fixed_consequences(unsigned start, obj_map<expr, expr*>& vars, uint_set const& assumptions, expr_ref_vector& conseq) {
        ast_manager& m = m_manager;
        pop_to_search_lvl();
        literal_vector const& lits = assigned_literals();
        unsigned sz = lits.size();
        expr* e1, *e2;       
        expr_ref fml(m);
        for (unsigned i = start; i < sz; ++i) {            
            literal lit = lits[i];
            if (lit == true_literal) continue;
            expr* e = bool_var2expr(lit.var());
            uint_set s;
            if (assumptions.contains(lit.var())) {
                s.insert(lit.var());
            }
            else {
                b_justification js = get_justification(lit.var());
                switch (js.get_kind()) {
                case b_justification::CLAUSE: {
                    clause * cls      = js.get_clause();
                    unsigned num_lits = cls->get_num_literals();
                    for (unsigned j = 0; j < num_lits; ++j) {
                        literal lit2 = cls->get_literal(j);
                        if (lit2.var() != lit.var()) {
                            s |= m_antecedents.find(lit2.var());
                        }
                    }
                    break;
                }
                case b_justification::BIN_CLAUSE: {
                    s |= m_antecedents.find(js.get_literal().var());
                    break;
                }
                case b_justification::AXIOM: {
                    break;
                }
                case b_justification::JUSTIFICATION: {
                    literal_vector literals;
                    m_conflict_resolution->justification2literals(js.get_justification(), literals);
                    for (unsigned j = 0; j < literals.size(); ++j) {
                        s |= m_antecedents.find(literals[j].var());
                    }
                    break;
                }
                }                
            }       
            m_antecedents.insert(lit.var(), s);
            TRACE("context", display_literal_verbose(tout, lit); tout << " " << s << "\n";);
            bool found = false;
            if (vars.contains(e)) {
                found = true;
                fml = lit.sign()?m.mk_not(e):e;
                vars.erase(e);
            }
            else if (!lit.sign() && m.is_eq(e, e1, e2)) {
                if (vars.contains(e2)) {
                    std::swap(e1, e2);
                }
                if (vars.contains(e1) && m.is_value(e2)) {
                    found = true;
                    fml = e;
                    vars.erase(e1);                    
                }
            }
            if (found) {
                fml = m.mk_implies(antecedent2fml(s), fml);
                conseq.push_back(fml);
            }
        }
    }

    void context::delete_unfixed(obj_map<expr, expr*>& var2val) {
        ast_manager& m = m_manager;
        ptr_vector<expr> to_delete;
        obj_map<expr,expr*>::iterator it = var2val.begin(), end = var2val.end();
        for (; it != end; ++it) {
            expr* k = it->m_key;
            expr* v = it->m_value;
            if (m.is_bool(k)) {
                literal lit = get_literal(k);
                switch (get_assignment(lit)) {
                case l_true: 
                    if (m.is_false(v)) {
                        to_delete.push_back(k);
                    }
                    else {
                        force_phase(lit.var(), false);
                    }
                    break;
                case l_false:
                    if (m.is_true(v)) {
                        to_delete.push_back(k);
                    }
                    else {
                        force_phase(lit.var(), true);
                    }
                    break;
                default:
                    to_delete.push_back(k);
                    break;
                }
            }
            else if (e_internalized(k) && m.are_distinct(v, get_enode(k)->get_root()->get_owner())) {
                to_delete.push_back(k);
            }
        }
        IF_VERBOSE(1, verbose_stream() << "(get-consequences deleting: " << to_delete.size() << " num-values: " << var2val.size() << ")\n";);
        for (unsigned i = 0; i < to_delete.size(); ++i) {
            var2val.remove(to_delete[i]);
        }
    }

    lbool context::get_consequences(expr_ref_vector const& assumptions, 
                                    expr_ref_vector const& vars, expr_ref_vector& conseq) {

        m_antecedents.reset();
        lbool is_sat = check(assumptions.size(), assumptions.c_ptr());
        if (is_sat != l_true) {
            return is_sat;
        }
        obj_map<expr, expr*> var2val;
        uint_set _assumptions;
        for (unsigned i = 0; i < assumptions.size(); ++i) {
            _assumptions.insert(get_literal(assumptions[i]).var());
        }
        model_ref mdl;
        get_model(mdl);
        ast_manager& m = m_manager;
        expr_ref_vector trail(m);
        model_evaluator eval(*mdl.get());
        expr_ref val(m);
        for (unsigned i = 0; i < vars.size(); ++i) {
            eval(vars[i], val);
            if (m.is_value(val)) {
                trail.push_back(val);
                var2val.insert(vars[i], val);
            } 
        }
        extract_fixed_consequences(0, var2val, _assumptions, conseq);
        unsigned num_units = assigned_literals().size();
        app_ref eq(m);
        TRACE("context", 
              tout << "vars: " << vars.size() << "\n";
              tout << "lits: " << num_units << "\n";);
        m_case_split_queue->init_search_eh();
        unsigned num_iterations = 0;
        unsigned model_threshold = 2;
        while (!var2val.empty()) {
            ++num_iterations;
            obj_map<expr,expr*>::iterator it = var2val.begin();
            expr* e = it->m_key;
            expr* val = it->m_value;
            push_scope();
            unsigned current_level = m_scope_lvl;

            literal lit;
            if (m.is_bool(e)) {
                lit = literal(get_bool_var(e), m.is_true(val));
            }
            else {
                eq = mk_eq_atom(e, val);
                internalize_formula(eq, false);
                lit = literal(get_bool_var(eq), true);
            }
            assign(lit, b_justification::mk_axiom(), true);
            flet<bool> l(m_searching, true);
            while (true) {
                is_sat = bounded_search();
                TRACE("context", tout << "search result: " << is_sat << "\n";);
                if (is_sat != l_true && m_last_search_failure != OK) {
                    return is_sat;
                }
                if (is_sat == l_undef) {
                    TRACE("context", tout << "restart\n";);
                    inc_limits();
                    continue;
                }
                break;
            }
            if (get_assignment(lit) == l_true) {
                var2val.erase(e);
            }
            else if (get_assign_level(lit) > get_search_level()) {
                TRACE("context", tout << "Retry fixing: " << mk_pp(e, m) << "\n";);
                pop_to_search_lvl();
                continue;
            }
            else {
                TRACE("context", tout << "Fixed: " << mk_pp(e, m) << "\n";);
            }

            TRACE("context", tout << "Unfixed variables: " << var2val.size() << "\n";);
            if (model_threshold <= num_iterations) {
                delete_unfixed(var2val);
                // The next time we check the model is after 1.5 additional iterations.
                model_threshold *= 3;
                model_threshold /= 2;                
            }
            // repeat until we either have a model with negated literal or 
            // the literal is implied at base.

            extract_fixed_consequences(num_units, var2val, _assumptions, conseq);
            num_units = assigned_literals().size();
            if (var2val.contains(e)) {
                TRACE("context", tout << "Fixed value to " << mk_pp(e, m) << " was not processed\n";);
                expr_ref fml(m);
                fml = m.mk_eq(e, var2val.find(e));
                fml = m.mk_implies(antecedent2fml(m_antecedents[lit.var()]), fml);
                conseq.push_back(fml);
                var2val.erase(e);
                SASSERT(get_assignment(lit) == l_false);
            }
        
        }
        end_search();
        return l_true;
    }

}