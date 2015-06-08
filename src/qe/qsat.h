/*++
Copyright (c) 2015 Microsoft Corporation

Module Name:

    qsat.h

Abstract:

    Quantifier Satisfiability Solver.

Author:

    Nikolaj Bjorner (nbjorner) 2015-5-28

Revision History:


--*/

#ifndef __QE_QSAT_H__
#define __QE_QSAT_H__

#include "tactic.h"


tactic * mk_qsat_tactic(ast_manager & m, params_ref const& p = params_ref());

tactic * mk_qe2_tactic(ast_manager & m, params_ref const& p = params_ref());


/*
  ADD_TACTIC("qsat", "apply a QSAT solver.", "mk_qsat_tactic(m, p)") 

  ADD_TACTIC("qe2", "apply a QSAT based quantifier elimination.", "mk_qe2_tactic(m, p)") 
*/

#endif 
