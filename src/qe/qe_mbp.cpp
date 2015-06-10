/*++
Copyright (c) 2015 Microsoft Corporation

Module Name:

    qe_mbp.cpp

Abstract:

    Model-based projection utilities

Author:

    Nikolaj Bjorner (nbjorner) 2015-5-29

Revision History:


--*/

#include "qe_mbp.h"
#include "qe_arith.h"
#include "arith_decl_plugin.h"
#include "expr_safe_replace.h"
#include "ast_pp.h"
#include "th_rewriter.h"
#include "model_v2_pp.h"

using namespace qe;


class mbp::impl {
    ast_manager& m;
public:
    impl(ast_manager& m):m(m) {}
    ~impl() {}
 
    void operator()(app_ref_vector const& vars, model& mdl, expr_ref& fml) {
        TRACE("qe", tout << fml << "\n";
              model_v2_pp(tout, mdl););
        expr_ref tmp(m);
        expr_safe_replace sub(m);
        app_ref_vector vars1(vars);
        fml = arith_project(mdl, vars1, fml);
        if (!vars1.empty()) {
            th_rewriter rw(m);
            for (unsigned i = 0; i < vars1.size(); ++i) {
                VERIFY(mdl.eval(vars1[i].get(), tmp));
                sub.insert(vars1[i].get(), tmp);
            }
            sub(fml);
            rw(fml);
        }
    }   
};
    
mbp::mbp(ast_manager& m) {
    m_impl = alloc(impl, m);
}
        
mbp::~mbp() {
    dealloc(m_impl);
}
        
void mbp::operator()(app_ref_vector const& vars, model& mdl, expr_ref& fml) {
    (*m_impl)(vars, mdl, fml);
}
        
