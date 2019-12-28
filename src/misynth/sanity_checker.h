#ifndef SANITY_CHECKER_H
#define SANITY_CHECKER_H

#include "cmd_context/cmd_context.h"
#include "smt_utils.h"
#include "collector_invocation_operands.h"
#include "ast/ast_pp.h"

namespace misynth
{
    extern bool DEBUG_MODE;
    class sanity_checker
    {
        private:
            cmd_context &m_cmd;
            ast_manager &m;
            arith_util m_arith;
            smt_utils m_utils;
            //params_ref m_params;
            //ref<solver> m_solver;
        public:
            sanity_checker(cmd_context &cmd_ctx, ast_manager &m)
                : m_cmd(cmd_ctx)
                , m(m)
                , m_arith(m)
                , m_utils(cmd_ctx, m)
            {
            }
            expr_ref build_invocation_fun_body(func_decl_ref var, expr_ref_vector &precs, expr_ref_vector &branches, func_decl_ref_vector pattern, expr_ref_vector invocation_args)
            {
                expr_ref_vector pre_branch(m);
                for (unsigned int i = 0; i < precs.size(); ++i)
                {
                    expr_ref var_eq_branch(m.mk_eq(m.mk_const(var), branches.get(i)), m);
                    pre_branch.push_back(m.mk_implies(precs.get(i), var_eq_branch));
                }
                expr_ref res = m_utils.con_join(pre_branch);
                return m_utils.replace_vars_decl(res, pattern, invocation_args);
            }

            bool check(expr_ref spec, expr_ref_vector &precs, expr_ref_vector &branches, func_decl_ref_vector &synth_funs, func_decl_ref_vector pattern)
            {
                std::string prefix_new_vars("_y_");
                expr_ref_vector new_vars(m), invocations_expr(m);

                app_ref_vector invocations(m);
                collect_invocation(spec, synth_funs, invocations);

                expr_ref_vector enviroment(m);

                for (unsigned int i = 0; i < invocations.size(); ++i)
                {
                    sort * range = invocations.get(i)->get_decl()->get_range();
                    func_decl_ref new_var(
                        m.mk_const_decl(prefix_new_vars + std::to_string(i),
                                        range), m);
                    new_vars.push_back(m.mk_const(new_var));
                    invocations_expr.push_back(invocations.get(i));
                    expr_ref_vector invocation_args(m, invocations.get(i)->get_num_args(), invocations.get(i)->get_args());
                    enviroment.push_back(build_invocation_fun_body(new_var, precs, branches, pattern, invocation_args));
                }

                expr_ref new_spec = m_utils.replace_expr(spec, invocations_expr, new_vars);
                //expr_ref sanity_check_formula(m.mk_implies(m_utils.con_join(enviroment), new_spec), m);
                std::cout << "Sanity checker: " << mk_ismt2_pp(m_utils.con_join(enviroment), m, 3) << " ==> " << mk_ismt2_pp(new_spec, m, 3) << std::endl;

                return m_utils.implies(m_utils.con_join(enviroment), new_spec);
            }
    };
}

#endif // SANITY_CHECKER_H
