/*++
Copyright (c) 2015 Microsoft Corporation

Module Name:

    qe_datatypes.cpp

Abstract:

    Simple projection function for algebraic datatypes.

Author:

    Nikolaj Bjorner (nbjorner) 2015-06-13

Revision History:

--*/

#include "qe_arith.h"
#include "qe_util.h"
#include "ast_pp.h"
#include "th_rewriter.h"
#include "expr_functors.h"
#include "model_v2_pp.h"
#include "expr_safe_replace.h"
#include "obj_pair_hashtable.h"
#include "qe_datatypes.h"

namespace qe {
    
    struct datatype_project_plugin::imp  {
        ast_manager&              m;
        datatype_util             dt;
        app_ref                   m_val;
        scoped_ptr<contains_app>  m_var;
        
        imp(ast_manager& m):
            m(m), dt(m), m_val(m) {}
        
        bool operator()(model& model, app* var, app_ref_vector& vars, expr_ref_vector& lits) {
            expr_ref val(m);
            VERIFY(model.eval(var, val));
            SASSERT(is_app(val));
            SASSERT(dt.is_constructor(to_app(val)));
            m_val = to_app(val);
            m_var = alloc(contains_app, m, var);

            try {
                if (dt.is_recursive(m.get_sort(var))) {
                    project_rec(model, vars, lits);
                }
                else {
                    project_nonrec(model, vars, lits);
                }
            }
            catch (cant_project) {
                TRACE("qe", tout << "can't project:" << mk_pp(var, m) << "\n";);
                return false;
            }
            return true;
        }        
    
        void project_nonrec(model& model, app_ref_vector& vars, expr_ref_vector& lits) {
            expr_ref tmp(m), val(m);
            expr_ref_vector args(m);
            app_ref arg(m);
            SASSERT(dt.is_constructor(m_val));
            func_decl* f = m_val->get_decl();
            ptr_vector<func_decl> const& acc = *dt.get_constructor_accessors(f);
            for (unsigned i = 0; i < acc.size(); ++i) {
                arg = m.mk_fresh_const(acc[i]->get_name().str().c_str(), acc[i]->get_range());
                model.register_decl(arg->get_decl(), arg->get_arg(i));
                args.push_back(arg);
            }
            val = m.mk_app(f, args.size(), args.c_ptr());
            reduce(val, lits);
        }

        void project_rec(model& model, app_ref_vector& vars, expr_ref_vector& lits) {
            func_decl* f = m_val->get_decl();
            expr_ref rhs(m);
            for (unsigned i = 0; i < lits.size(); ++i) {
                if (solve(lits[i].get(), rhs)) {
                    reduce(rhs, lits);
                    return;
                }
            }

            // otherwise, unfold the constructor associated with m_var
            // once according to the model. In this way, selector-constructor
            // redexes are reduced and disequalities are eventually solved
            // by virtue of the constructors being different.
            project_nonrec(model, vars, lits);
        }

        void reduce(expr* val, expr_ref_vector& lits) {
            expr_safe_replace sub(m);
            th_rewriter rw(m);
            expr_ref tmp(m);
            sub.insert(m_var->x(), val);
            for (unsigned i = 0; i < lits.size(); ++i) {                
                sub(lits[i].get(), tmp);
                rw(tmp);
                lits[i] = tmp;
            }
        }

        bool contains_x(expr* e) {
            return (*m_var)(e);
        }

        bool solve(expr* fml, expr_ref& t) {
            expr* t1, *t2;
            if (m.is_eq(fml, t1, t2)) {
                if (contains_x(t1) && !contains_x(t2) && is_app(t1)) {
                    return solve(to_app(t1), t2, t);
                }
                if (contains_x(t2) && !contains_x(t1) && is_app(t2)) {
                    return solve(to_app(t2), t1, t);
                }
            }
            return false;
        }

        bool solve(app* a, expr* b, expr_ref& t) {
            SASSERT(contains_x(a));
            SASSERT(!contains_x(b));
            if (m_var->x() == a) {
                t = b;
                return true;
            }
            if (!dt.is_constructor(a)) {
                return false;
            }
            func_decl* c = a->get_decl();
            func_decl* r = dt.get_constructor_recognizer(c);
            ptr_vector<func_decl> const & acc = *dt.get_constructor_accessors(c);
            SASSERT(acc.size() == a->get_num_args());
            //
            // It suffices to solve just the first available equality.
            // The others are determined by the first.
            //
            for (unsigned i = 0; i < a->get_num_args(); ++i) {
                expr* l = a->get_arg(i);
                if (is_app(l) && contains_x(l)) {
                    expr_ref r(m.mk_app(acc[i], b), m);
                    if (solve(to_app(l), r, t)) {
                        return true;
                    }
                }
            }
            return false;
        }
        
    };
    
    datatype_project_plugin::datatype_project_plugin(ast_manager& m) {
        m_imp = alloc(imp, m);
    }
    
    datatype_project_plugin::~datatype_project_plugin() {
        dealloc(m_imp);
    }
    
    bool datatype_project_plugin::operator()(model& model, app* var, app_ref_vector& vars, expr_ref_vector& lits) {
        return (*m_imp)(model, var, vars, lits);
    }
    
    family_id datatype_project_plugin::get_family_id() {
        return m_imp->dt.get_family_id();
    }
    
}



