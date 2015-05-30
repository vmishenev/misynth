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
#include "arith_decl_plugin.h"
#include "expr_safe_replace.h"
#include "ast_pp.h"

using namespace qe;

enum lra_category {
    lra_none,
    lra_unknown,
    lra_gt,
    lra_ge,
    lra_lt,
    lra_le
};

class mbp::impl {
    ast_manager& m;
    arith_util   m_arith;
public:
    impl(ast_manager& m):m(m), m_arith(m) {}
    ~impl() {}
 
    void operator()(app_ref_vector const& vars, model_ref& mdl, expr_ref& fml) {
        for (unsigned i = 0; i < vars.size(); ++i) {
            project(vars[i], mdl, fml);
        }
    }   
private:
    void project(app* var, model_ref& mdl, expr_ref& fml) {
        // TBD
    }

    lra_category categorize_lra(app* var, expr* fml, expr_ref& t) {
        // TBD
        return lra_unknown;
    }

    void project_lra(app* var, model_ref& mdl, expr_ref_vector& fmls) {
        expr_ref_vector lt(m), le(m), gt(m), ge(m), other(m);
        expr_ref t(m), val(m);
        if (!mdl->eval(var, val)) {
            return;
        }
        
        for (unsigned i = 0; i < fmls.size(); ++i) {
            expr* fml = fmls[i].get();
            switch (categorize_lra(var, fml, t)) {
            case lra_none:
                other.push_back(fml);
                break;
            case lra_unknown:
                TRACE("qe", tout << "unhandled constraint:\n" << mk_pp(fml, m) << "\n";);
                replace_value(var, val, mdl, fmls);
                return;
            case lra_lt:
                lt.push_back(t);
                break;
            case lra_le:
                le.push_back(t);
                break;
            case lra_gt:
                gt.push_back(t);
                break;
            case lra_ge:
                ge.push_back(t);
                break;
            }
        }
        rational glb;
        unsigned ltle = le.size() + lt.size();
        unsigned gtge = ge.size() + gt.size();
        bool is_strict = !gt.empty();
        bool is_lower = (ltle <= gtge);
        if (is_lower) {
            is_strict = !lt.empty();
            gt.swap(lt);
            ge.swap(le);
        }
        for (unsigned i = 0; i < gt.size(); ++i) {
            update_bound(gt[i].get(), mdl, is_lower, i == 0, glb);
        }
        for (unsigned i = 0; i < ge.size(); ++i) {
            is_strict &= !update_bound(ge[i].get(), mdl, is_lower, i == 0 && ge.empty(), glb);
        }
        // TBD.
    }
    
    bool update_bound(expr* t, model_ref& mdl, bool is_lower, bool is_first, rational& r) {
        rational n;
        expr_ref tmp(m);
        VERIFY(mdl->eval(t, tmp) && m_arith.is_numeral(tmp, n));
        if (is_first || (is_lower?(r < n):(r > n))) {
            r = n;
            return true;
        }
        else {
            return false;
        }
    }

    void replace_value(app* var, expr* val, model_ref& mdl, expr_ref_vector& fmls) {
        expr_safe_replace rep(m);
        expr_ref tmp(m);
        rep.insert(var, val);
        for (unsigned j = 0; j < fmls.size(); ++j) {
            rep(fmls[j].get(), tmp);
            fmls[j] = tmp;
        }
    }
};
    
mbp::mbp(ast_manager& m) {
    m_impl = alloc(impl, m);
}
        
mbp::~mbp() {
    dealloc(m_impl);
}
        
void mbp::operator()(app_ref_vector const& vars, model_ref& mdl, expr_ref& fml) {
    (*m_impl)(vars, mdl, fml);
}
        
