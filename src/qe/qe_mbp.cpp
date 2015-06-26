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
#include "qe_datatypes.h"
#include "expr_safe_replace.h"
#include "ast_pp.h"
#include "th_rewriter.h"
#include "model_v2_pp.h"

using namespace qe;


class mbp::impl {
    ast_manager& m;
    ptr_vector<project_plugin> m_plugins;

    void add_plugin(project_plugin* p) {
        family_id fid = p->get_family_id();
        SASSERT(!m_plugins.get(fid, 0));
        m_plugins.setx(fid, p, 0);
    }

    project_plugin* get_plugin(app* var) {
        family_id fid = m.get_sort(var)->get_family_id();
        return m_plugins.get(fid, 0);
    }

public:
    impl(ast_manager& m):m(m) {
        add_plugin(alloc(arith_project_plugin, m));
        add_plugin(alloc(datatype_project_plugin, m));
    }

    ~impl() {
        std::for_each(m_plugins.begin(), m_plugins.end(), delete_proc<project_plugin>());
    }

    void operator()(app_ref_vector const& vars0, model& mdl, expr_ref_vector& fmls) {
        expr_ref val(m), tmp(m);
        app_ref_vector vars(vars0);
        app_ref var(m);
        th_rewriter rw(m);
        bool change = true;
        while (change) {
            change = false;
            for (unsigned i = 0; i < m_plugins.size(); ++i) {
                if (m_plugins[i] && (*m_plugins[i])(vars, fmls)) {
                    change = true;
                }
            }
        }
        while (!vars.empty()) {
            var = vars.back();
            vars.pop_back();
            project_plugin* p = get_plugin(var);
            if (!p || !(*p)(mdl, var, vars, fmls)) {
                expr_safe_replace sub(m);
                VERIFY(mdl.eval(var, val));
                sub.insert(var, val);
                for (unsigned i = 0; i < fmls.size(); ++i) {
                    sub(fmls[i].get(), tmp);
                    rw(tmp);
                    fmls[i] = tmp;
                }
            }
        }
    }
};
    
mbp::mbp(ast_manager& m) {
    m_impl = alloc(impl, m);
}
        
mbp::~mbp() {
    dealloc(m_impl);
}
        
void mbp::operator()(app_ref_vector const& vars, model& mdl, expr_ref_vector& fmls) {
    (*m_impl)(vars, mdl, fmls);
}
        
