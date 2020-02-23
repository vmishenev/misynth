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
            ref<solver> m_solver;

        public:
            sanity_checker(cmd_context &cmd_ctx, ast_manager &m)
                : m_cmd(cmd_ctx)
                , m(m)
                , m_arith(m)
                , m_utils(cmd_ctx, m)
            {
                reset_constraint_for_model_x();
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


            bool check_through_implication(expr_ref spec, expr_ref_vector &precs, expr_ref_vector &branches, func_decl_ref_vector &synth_funs, func_decl_ref_vector pattern)
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

            bool check(expr_ref_vector &constraints, expr_ref body_fun, func_decl_ref_vector &synth_funs, func_decl_ref_vector args)
            {
                func_decl *fd = synth_funs.get(0);

                expr_ref_vector args_app(m);
                for (auto &fd : args)
                {
                    args_app.push_back(m.mk_const(fd));
                }
                expr_ref fd_eq_body_fun(m.mk_eq(m.mk_app(fd, args_app.size(), args_app.c_ptr()), body_fun), m);
                expr_ref macros(m_utils.universal_quantified(fd_eq_body_fun, args));
                std::cout << "Sanity checker:: macros: " << mk_ismt2_pp(macros, m, 3) << std::endl;

                params_ref params;
                ref<solver> slv = m_cmd.get_solver_factory()(m, params, false, true, false, symbol::null);
                slv->push();
                slv->assert_expr(macros);

                for (unsigned int i = 0; i < constraints.size(); ++i)
                {
                    slv->push();
                    slv->assert_expr(m.mk_not(constraints.get(i)));
                    lbool r = slv->check_sat();
                    if (r != lbool::l_false)
                    {
                        std::cout << "!!!Sanity checker:: constraint is failed: " <<  mk_ismt2_pp(constraints.get(i), m, 3) <<  std::endl;
                        model_ref mdl;
                        slv->get_model(mdl);
                        std::cout << *mdl << std::endl;
                        return false;
                    }
                    slv->pop(1);
                }
                return true;
            }

            //expr * last_body;
            bool check(expr_ref_vector &constraints, func_decl_ref_vector used_vars, expr_ref body_fun, func_decl_ref_vector &synth_funs, func_decl_ref_vector args, model_ref &mdl)
            {
                /*if (last_body != body_fun.get())
                {
                    last_body = body_fun.get();
                    reset_constraint_for_model_x();
                }*/
                if (!body_fun.get())
                {
                    lbool r = m_solver->check_sat();
                    if (r != lbool::l_false)
                    {
                        m_solver->get_model(mdl);
                        add_blacklist(mdl, used_vars);
                    }
                    return false;
                }
                func_decl *fd = synth_funs.get(0);

                expr_ref_vector args_app(m);
                for (auto &fd : args)
                {
                    args_app.push_back(m.mk_const(fd));
                }
                expr_ref fd_eq_body_fun(m.mk_eq(m.mk_app(fd, args_app.size(), args_app.c_ptr()), body_fun), m);
                expr_ref macros(m_utils.universal_quantified(fd_eq_body_fun, args));
                std::cout << "Sanity checker:: macros: " << mk_ismt2_pp(macros, m, 3) << std::endl;




                m_solver->push();
                m_solver->assert_expr(macros);
                for (unsigned int i = 0; i < m_solver->get_num_assertions(); ++i)
                {
                    std::cout << "Sanity checker:: assert: " << mk_ismt2_pp(m_solver->get_assertion(i), m, 3) << std::endl;
                }
                for (unsigned int i = 0; i < constraints.size(); ++i)
                {
                    m_solver->push();
                    m_solver->assert_expr(m.mk_not(constraints.get(i)));
                    lbool r = m_solver->check_sat();
                    if (r != lbool::l_false)
                    {
                        std::cout << "!!!Sanity checker:: constraint is failed: " <<  mk_ismt2_pp(constraints.get(i), m, 3) <<  std::endl;

                        m_solver->get_model(mdl);
                        std::cout << *mdl << std::endl;

                        m_solver->pop(2); // remove macros and constraint
                        add_blacklist(mdl, used_vars);
                        return false;
                    }
                    m_solver->pop(1);
                }
                m_solver->pop(1);// remove macros
                return true;
            }
            void add_blacklist(model_ref mdl,  func_decl_ref_vector used_vars)
            {
                m_solver->push();
                m_solver->assert_expr(m.mk_not(m_utils.get_logic_model_with_default_value(mdl, used_vars)));
            }
            void reset_constraint_for_model_x()
            {
                params_ref params;
                m_solver = m_cmd.get_solver_factory()(m, params, false, true, false, symbol::null);

            }
    };
}

#endif // SANITY_CHECKER_H
