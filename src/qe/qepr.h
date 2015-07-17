/*++
Copyright (c) 2015 Microsoft Corporation

Module Name:

    qepr.h

Abstract:

    EPR symbol elimination routine

Author:

    Nikolaj Bjorner (nbjorner) 2015-7-16

Revision History:


--*/

#ifndef QE_QEPR_H_
#define QE_QEPR_H_

#include "tactic.h"


tactic * mk_epr_qe_tactic(ast_manager & m, params_ref const& p = params_ref());


/*
  ADD_TACTIC("epr_qe", "apply a QSAT based EPR quantifier elimination.", "mk_epr_qe_tactic(m, p)") 
*/

#endif 
