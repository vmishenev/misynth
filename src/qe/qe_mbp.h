/*++
Copyright (c) 2015 Microsoft Corporation

Module Name:

    qe_mbp.h

Abstract:

    Model-based projection utilities

Author:

    Nikolaj Bjorner (nbjorner) 2015-5-28

Revision History:


--*/

#ifndef __QE_MBP_H__
#define __QE_MBP_H__

#include "ast.h"
#include "params.h"
#include "model.h"


namespace qe {

    struct cant_project {};

    class project_plugin {
    public:
        virtual ~project_plugin() {}
        virtual bool operator()(model& model, app* var, app_ref_vector& vars, expr_ref_vector& lits) = 0;
        virtual bool operator()(app_ref_vector& vars, expr_ref_vector& lits) = 0;
        virtual family_id get_family_id() = 0;
    };

    class mbp {
        class impl;
        impl * m_impl;
    public:
        mbp(ast_manager& m);
        
        ~mbp();
        
        /**
           \brief
           Apply model-based qe on constants provided as vector of variables. 
           Return the updated formula and updated set of variables that were not eliminated.           
        */
        void operator()(app_ref_vector const& vars, model& mdl, expr_ref_vector& fmls);
    };
}

#endif 
