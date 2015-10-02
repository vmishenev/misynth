/*++
Copyright (c) 2015 Microsoft Corporation

Module Name:

    qe_rec.h

Abstract:

    Recursive application of quantifier elimination.

Author:

    Nikolaj Bjorner (nbjorner) 2015-9-30

Revision History:


--*/

#ifndef __QE_REC_H__
#define __QE_REC_H__

#include "ast.h"
#include "params.h"
#include "model.h"


namespace qe {

    class qe_helper {     
    public:
        virtual void collect_statistics(statistics & st) const = 0;
        virtual expr_ref operator()(bool is_forall, unsigned num_vars, app* const* vars, expr* fml) = 0;      
        virtual void set_cancel(bool f) = 0;
        virtual void updt_params(params_ref const& p) {}
    };

    class qe_rec {
        struct imp;
        imp * m_imp;
    public:
        qe_rec(ast_manager& m, qe_helper& q);
        ~qe_rec();
        expr_ref operator()(expr* fml);
        void collect_statistics(statistics & st) const;
        void updt_params(params_ref const& p);
        void collect_param_descrs(param_descrs& r);
        void set_cancel(bool f);
    };
}

#endif 
