#ifndef SMT_UTILS_H
#define SMT_UTILS_H

#include "cmd_context/cmd_context.h"

namespace misynth
{

    struct smt_utils
    {
        cmd_context &m_cmd;
        ast_manager &m;
        arith_util m_arith;
        params_ref m_params;
        ref<solver> m_solver;

        smt_utils(cmd_context &cmd_ctx, ast_manager &m)
            : m_cmd(cmd_ctx)
            , m(m)
            , m_arith(m)
        {
        }
        model_ref get_model()
        {
            model_ref model;
            m_solver->get_model(model);
            return model;
        }
        proof_ref get_proof()
        {
            proof_ref pr ( m_solver->get_proof(), m);
            return pr;
        }
        bool implies(expr *a, expr *b)
        {
            return !is_sat(a, m.mk_not(b));
        }
        bool is_equil(expr *a, expr *b)
        {
            return implies(a, b) && implies(b, a);
        }

        bool is_unsat(expr *e)
        {
            m_solver = m_cmd.get_solver_factory()(m, m_params, true/*need proof*/, true, false, symbol::null);
            m_solver->push();
            m_solver->assert_expr(e);
            lbool r = m_solver->check_sat();
            std::cout << "proof0: " << mk_ismt2_pp(m_solver->get_proof(), m, 3) << std::endl;
            m_solver->pop(1);
            return r == lbool::l_false;
        }

        bool is_sat(expr *e)
        {
            m_solver = m_cmd.get_solver_factory()(m, m_params, false, true, false, symbol::null);
            m_solver->push();
            m_solver->assert_expr(e);
            lbool r = m_solver->check_sat();
            m_solver->pop(1);
            return r == lbool::l_true;
        }

        bool is_sat(expr *e1, expr *e2)
        {
            m_solver = m_cmd.get_solver_factory()(m, m_params, false, true, false, symbol::null);
            m_solver->push();
            m_solver->assert_expr(e1);
            m_solver->assert_expr(e2);
            lbool r = m_solver->check_sat();
            m_solver->pop(2);
            return r == lbool::l_true;
        }


        expr_ref con_join(expr_ref_vector &vec)
        {
            expr_ref all(m);

            if (vec.size() > 1)
            {
                all = m.mk_and(vec.size(), vec.c_ptr());
            }
            else if (vec.size() == 1)
            {
                all = vec[0].get();
            }
            else
            {
                all = m.mk_true();
            }

            return all;
        }
        /*
         * Return (and (= a[0] b[0]) ... (= a[n-1] b[n-1]))
         * */
        expr_ref mk_eq(expr_ref_vector &a, expr_ref_vector &b)
        {
            SASSERT(a.size() == b.size());
            expr_ref_vector vec_of_equals(m);

            for (unsigned int i = 0; i < a.size(); ++i)
            {
                vec_of_equals.push_back(m.mk_eq(a.get(i), b.get(i)));
            }

            return con_join(vec_of_equals);
        }
    };

} // misynth
#endif // SMT_UTILS_H
