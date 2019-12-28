#ifndef SMT_UTILS_H
#define SMT_UTILS_H

#include "cmd_context/cmd_context.h"
#include "ast/rewriter/expr_replacer.h"
#include <ast/rewriter/th_rewriter.h>

namespace misynth
{
    extern bool DEBUG_MODE;
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
            proof_ref pr(m_solver->get_proof(), m);
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
            //std::cout << "proof0: " << mk_ismt2_pp(m_solver->get_proof(), m, 3) << std::endl;
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
        expr_ref dis_join(expr_ref_vector &vec)
        {
            expr_ref all(m);

            if (vec.size() > 1)
            {
                all = m.mk_or(vec.size(), vec.c_ptr());
            }
            else if (vec.size() == 1)
            {
                all = vec[0].get();
            }
            else
            {
                all = m.mk_false();
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
        expr_ref mk_eq(func_decl_ref_vector &a, expr_ref_vector &b)
        {
            SASSERT(a.size() == b.size());
            expr_ref_vector vec_of_equals(m);

            for (unsigned int i = 0; i < a.size(); ++i)
            {
                vec_of_equals.push_back(m.mk_eq(m.mk_const(a.get(i)), b.get(i)));
            }

            return con_join(vec_of_equals);
        }

        expr_ref mk_eq(func_decl_ref_vector &a, func_decl_ref_vector &b)
        {
            SASSERT(a.size() == b.size());
            expr_ref_vector vec_of_equals(m);

            for (unsigned int i = 0; i < a.size(); ++i)
            {
                vec_of_equals.push_back(m.mk_eq(m.mk_const(a.get(i)), m.mk_const(b.get(i))));
            }

            return con_join(vec_of_equals);
        }

        expr_ref  replace_vars_according_to_model(expr *e, model_ref mdl, func_decl_ref_vector &vars)
        {
            scoped_ptr<expr_replacer> rp = mk_default_expr_replacer(m);
            expr_substitution sub(m);

            for (func_decl *fd : vars)
            {
                expr_ref e(to_expr(m.mk_const(fd)), m);

                if (DEBUG_MODE)
                {
                    std::cout << "replace " << mk_ismt2_pp((e), m, 3) << " to " << mk_ismt2_pp((*mdl)(e), m, 3) << std::endl;
                }

                sub.insert(e, (*mdl)(e));
            }

            rp->set_substitution(&sub);
            expr_ref result(m);
            (*rp)(e, result);
            return result;
        }
        expr_ref  replace_vars_decl(expr *e, func_decl_ref_vector &src_vars, func_decl_ref_vector &dest_vars)
        {
            // TODO Optimize
            SASSERT(src_vars.size() <=  dest_vars.size());
            scoped_ptr<expr_replacer> rp = mk_default_expr_replacer(m);
            expr_substitution sub(m);

            for (unsigned int i = 0; i < src_vars.size(); ++i)
            {
                expr_ref e1(to_expr(m.mk_const(src_vars.get(i))), m);
                expr_ref e2(to_expr(m.mk_const(dest_vars.get(i))), m);

                sub.insert(e1, e2);
            }

            rp->set_substitution(&sub);
            expr_ref result(m);
            (*rp)(e, result);
            return result;
        }
        expr_ref  replace_vars_decl(expr *e, func_decl_ref_vector &src_vars, expr_ref_vector &dest_expr)
        {

            SASSERT(src_vars.size() <= dest_expr.size());
            scoped_ptr<expr_replacer> rp = mk_default_expr_replacer(m);
            expr_substitution sub(m);

            for (unsigned int i = 0; i < src_vars.size(); ++i)
            {
                expr_ref e1(to_expr(m.mk_const(src_vars.get(i))), m);

                sub.insert(e1, dest_expr.get(i));
            }

            rp->set_substitution(&sub);
            expr_ref result(m);
            (*rp)(e, result);
            return result;
        }

        expr_ref  replace_expr(expr *e, expr_ref_vector &src_expr, expr_ref_vector &dest_expr)
        {

            SASSERT(src_expr.size() <= dest_expr.size());
            scoped_ptr<expr_replacer> rp = mk_default_expr_replacer(m);
            expr_substitution sub(m);

            for (unsigned int i = 0; i < src_expr.size(); ++i)
            {
                sub.insert(src_expr.get(i), dest_expr.get(i));
            }

            rp->set_substitution(&sub);
            expr_ref result(m);
            (*rp)(e, result);
            return result;
        }
        /*
         *
         * Return \not \exists quantifier_vars \not   e
         * */
        expr_ref universal_quantified(expr_ref e, func_decl_ref_vector &quantifier_vars)
        {
            sort_ref_vector quantifier_vars_sort(m);
            vector<symbol > quantifier_vars_names;
            expr_ref_vector subst(m);
            unsigned int idx = 0;
            for (func_decl *fd :  quantifier_vars)
            {
                subst.push_back(m.mk_var(idx++, fd->get_range()));
                quantifier_vars_sort.push_back(fd->get_range());
                quantifier_vars_names.push_back(symbol("_x_"));  //fd->get_name()
            }
            expr_ref quant_e(m.mk_not(m.mk_exists(quantifier_vars_sort.size(), quantifier_vars_sort.c_ptr(), quantifier_vars_names.c_ptr(), m.mk_not(e))), m);
            subst.reverse();
            return replace_vars_decl(quant_e, quantifier_vars, subst);
        }
        //only performs "local simplifications"
        expr_ref simplify(expr_ref e)
        {
            expr_ref th_res(m);
            proof_ref pr(m);

            params_ref th_solv_params;
            th_rewriter s(m, th_solv_params);
            th_solver solver(m_cmd);
            s.set_solver(alloc(th_solver, m_cmd));
            s(e, th_res, pr);
            return th_res;
        }
    }; // smt_utils
} // misynth
#endif // SMT_UTILS_H
