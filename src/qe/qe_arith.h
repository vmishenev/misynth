
/*++
Copyright (c) 2015 Microsoft Corporation

--*/


#ifndef __QE_ARITH_H_
#define __QE_ARITH_H_

#include "model.h"
#include "arith_decl_plugin.h"

namespace qe {
    /**
       Loos-Weispfenning model-based projection for a basic conjunction.
       Lits is a vector of literals.
       return vector of variables that could not be projected.
     */
    expr_ref arith_project(model& model, app_ref_vector& vars, expr_ref_vector const& lits);

    expr_ref arith_project(model& model, app_ref_vector& vars, expr* fml);

    // match e := t mod k = 0.
    bool is_divides(arith_util& a, expr* e, rational& k, expr_ref& t);

};

#endif
