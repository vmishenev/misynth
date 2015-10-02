/*++
Copyright (c) 2015 Microsoft Corporation

Module Name:

    qe_rec.cpp

Abstract:

    Recursive application of quantifier elimination.

Author:

    Nikolaj Bjorner (nbjorner) 2015-9-30

Revision History:


--*/

#include "qe.h"    // definition of extract_vars.
#include "qe_rec.h"

using namespace qe;


struct qe_rec::imp {
    ast_manager& m;
    qe_helper&   q;
    imp(ast_manager& m, qe_helper& q):
        m(m),
        q(q)
    {}    
};

qe_rec::qe_rec(ast_manager& m, qe_helper& q) {
    m_imp = alloc(imp, m, q);
}

qe_rec::~qe_rec() {
    dealloc(m_imp);
}

expr_ref qe_rec::operator()(expr* fml) {
    ast_manager& m = m_imp->m;
    expr_ref tmp(m);
    expr_ref_vector     trail(m);
    obj_map<expr,expr*> visited;
    ptr_vector<expr>    todo;
    trail.push_back(fml);
    todo.push_back(fml);
    expr* e = 0, *r = 0;

    while (!todo.empty()) {
        e = todo.back();
        if (visited.contains(e)) {
            todo.pop_back();
            continue;            
        }
        
        switch(e->get_kind()) {
        case AST_APP: {
            app* a = to_app(e);
            expr_ref_vector args(m);
            unsigned num_args = a->get_num_args();
            bool all_visited = true;
            for (unsigned i = 0; i < num_args; ++i) {
                if (visited.find(a->get_arg(i), r)) {
                    args.push_back(r);
                }
                else {
                    todo.push_back(a->get_arg(i));
                    all_visited = false;
                }
            }
            if (all_visited) {
                r = m.mk_app(a->get_decl(), args.size(), args.c_ptr());
                todo.pop_back();
                trail.push_back(r);
                visited.insert(e, r);
            }
            break;
        }
        case AST_QUANTIFIER: {
            app_ref_vector vars(m);
            quantifier* q = to_quantifier(e);
            bool is_fa = q->is_forall();
            tmp = q->get_expr();
            extract_vars(q, tmp, vars);
            tmp = operator()(tmp);
            tmp = m_imp->q(is_fa, vars.size(), vars.c_ptr(), tmp);
            trail.push_back(tmp);
            visited.insert(e, tmp);
            todo.pop_back();
            break;
        }
        default:
            UNREACHABLE();
            break;
        }        
    }    
    VERIFY (visited.find(fml, e));
    return expr_ref(e, m);
}

void qe_rec::collect_statistics(statistics & st) const {
    m_imp->q.collect_statistics(st);
}

void qe_rec::updt_params(params_ref const& p) {
    m_imp->q.updt_params(p);
}

void qe_rec::collect_param_descrs(param_descrs& r) {
    // m_imp->q.collect_param_descrs(r);
}

void qe_rec::set_cancel(bool f) {
    m_imp->q.set_cancel(f);
}

