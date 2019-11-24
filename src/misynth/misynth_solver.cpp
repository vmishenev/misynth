#include "misynth_solver.h"
#include "collector_invocation_operands.h"

#include "ast/ast_pp.h"

#include <iomanip>
#include <iostream>
#include <set>

#define VERBOSE true
#define DEBUG true

namespace misynth
{


    misynth_solver::misynth_solver(cmd_context &cmd_ctx, ast_manager &m, solver *solver)
        : m_cmd(cmd_ctx)
        , m(m)
        , m_solver(solver)
        , m_utils(cmd_ctx, m)
        , m_arith(m)
        , m_constraints(m)

    {
    }

    bool misynth_solver::solve(func_decl_ref_vector &synth_funs, expr_ref spec)
    {
        collect_invocation_operands(spec, synth_funs, m_ops);
        //std::cout << "m_ops size: " << m_ops.size() << std::endl;
        prove_unrealizability(spec);


        return false;
    }

    bool misynth_solver::prove_unrealizability(expr_ref spec)
    {
        std::cout << "prove_unrealizability: " << mk_ismt2_pp(spec, m, 3) << std::endl;

        if (m_utils.is_unsat(spec))
        {
            if (VERBOSE)
            {
                std::cout << "Unrealizability!!! Specification is unsat \n. " << mk_ismt2_pp(spec, m, 3) << std::endl;
            }

            return true;
        }

        expr_ref_vector assumptions(m);
        generate_assumptions_from_operands(assumptions);

        if (VERBOSE)
        {
            for (unsigned int i = 0; i < assumptions.size(); ++i)
            {
                std::cout << "assumptions: " << mk_ismt2_pp(assumptions.get(i), m, 3) << std::endl;
            }
        }

        return check_assumptions(spec, assumptions);

    }

    bool misynth_solver::check_assumptions(expr_ref spec, expr_ref_vector &assumptions)
    {
        params_ref params;
        ref<solver> slv = m_cmd.get_solver_factory()(m, params, false, true, false, symbol::null);
        subsets_backtracking(assumptions, spec, slv.get(), 0);
        return false;
    }

    bool misynth_solver::subsets_backtracking(expr_ref_vector &assump, expr *spec, solver *slv, unsigned int index)
    {
        if (index > 0)
        {
            if (slv->check_sat() == lbool::l_false)
            {
                // Next any superset is unsat
                return false;

            }
            else
            {
                slv->push();
                slv->assert_expr(spec);

                if (slv->check_sat() == lbool::l_false)  // unsat -- unrealizability
                {
                    slv->pop(1);

                    if (VERBOSE)
                    {

                        std::cout << "Unrealizability!!! Specification is unsat. \n Unrealizability assumptions:" << std::endl;

                        for (unsigned i = 0; i < slv->get_num_assertions(); ++i)
                        {
                            std::cout << mk_ismt2_pp(slv->get_assertion(i), m, 3) << std::endl;
                        }
                    }

                    return true;
                }

                slv->pop(1);
            }
        }

        for (unsigned int i = index; i < assump.size(); ++i)
        {

            // include the A[i] in subset.
            slv->push();
            slv->assert_expr(assump.get(i));



            // move onto the next element.
            if (subsets_backtracking(assump, spec, slv, i + 1))
            {
                return true;
            }

            // exclude the A[i] from subset and triggers backtracking.
            slv->pop(1);
        }

        return false;
    }

    void misynth_solver::generate_assumptions_from_operands(expr_ref_vector &assumptions)
    {
        for (unsigned int i = 0; i < m_ops.size(); ++i)
        {
            for (unsigned int j = 0; j < i; ++j)
            {
                expr_ref eq = m_utils.mk_eq(m_ops.get(i), m_ops.get(j));

                if (m_utils.is_sat(eq))
                {
                    assumptions.push_back(eq);
                }
            }
        }
    }

} // namespace misynth
