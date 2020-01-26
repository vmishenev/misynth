#include "misynth_solver.h"
#include "collector_invocation_operands.h"
#include "rewriter_coefficients.h"
#include "ast/ast_pp.h"
#include "ast/rewriter/rewriter.h"
#include "ast/rewriter/rewriter_def.h"

#include "ast/used_vars.h"
#include "ast/rewriter/th_rewriter.h"
#include "misynth/synth_params.hpp"
#include "sanity_checker.h"
#include "search_simultaneously_branches.h"
#include "misynth/function_utils.h"
#include "misynth/collector_constants.h"
#include "model/model2expr.h"

#include <iomanip>
#include <iostream>
#include <set>



#define VERBOSE true
#define DEBUG true

namespace misynth
{
    unsigned int max_iter_iso_mor = 0;
    unsigned int iters_main_alg = 0;
    unsigned int alg3_run = 0;

    bool DEBUG_MODE = true;
    misynth_solver::misynth_solver(cmd_context &cmd_ctx, ast_manager &m, solver *solver)
        : m_cmd(cmd_ctx)
        , m(m)
        , m_solver(solver)
        , m_utils(cmd_ctx, m)
        , m_arith(m)
        , m_futils(cmd_ctx, m)
        , m_coeff_decl_vec(m),

          m_used_vars(m),
          m_precs(m),
          m_branches(m),
          m_terms(m),
          m_assumptions(m),
          m_abducer(cmd_ctx, m)
    {
    }


    model_ref misynth_solver::get_coeff_model_from_slv(ref<solver> &slv, expr_ref spec_for_concrete_x, expr_ref heuristic)
    {
        bool is_added_heuristic = heuristic.get();
        slv->push();
        slv->assert_expr(spec_for_concrete_x);

        if (is_added_heuristic)
        {
            slv->push();
            slv->assert_expr(heuristic);
        }

        lbool res_spec_for_x = slv->check_sat();

        model_ref mdl_for_coeff;

        if (res_spec_for_x != lbool::l_true)
        {
            //TODO: take into account a heuristic
            if (is_added_heuristic)
            {
                std::cout << "WARNING!!! Heuristic for this spec and model x is unsat. " << std::endl;
                is_added_heuristic = false;
                slv->pop(1); // remove a heuristic
                lbool res_spec_for_x = slv->check_sat();
                if (res_spec_for_x != lbool::l_true)
                {
                    return mdl_for_coeff;//not found
                }
            }
            else
            {
                return mdl_for_coeff;//not found
            }

        }
        if (is_added_heuristic)
        {
            slv->pop(1);
            is_added_heuristic = false;
        }

        slv->get_model(mdl_for_coeff);
        slv->pop(1);

        expr_ref logic_mdl = m_utils.get_logic_model_with_default_value(mdl_for_coeff, m_coeff_decl_vec);
        slv->assert_expr(m.mk_not(logic_mdl));
        return mdl_for_coeff;

    }

    model_ref misynth_solver::get_coeff_model(expr_ref spec_for_concrete_x, expr_ref heuristic)
    {


        if (m_params.fairness())
        {





            unsigned int i = 0;
            model_ref mdl;
            while (i <=  m_slv_for_coeff_vec.size())
            {
                ref<solver> &slv = m_slv_for_coeff_vec.get(m_current_slv_for_coeff);
                mdl = get_coeff_model_from_slv(slv, spec_for_concrete_x, heuristic);
                if (mdl.get()) break;
                if (++m_current_slv_for_coeff ==  m_slv_for_coeff_vec.size())
                {
                    m_current_slv_for_coeff = 0;
                }
                ++i;
            }
            if (!mdl.get()) return mdl;



            for (unsigned int i = 0; i < m_slv_for_coeff_vec.size(); ++i)
            {
                if (i == m_current_slv_for_coeff)
                    continue;
                expr_ref value_for_coeff = m_utils.get_default_value_from_mdl(mdl, m_coeff_decl_vec.get(i));
                m_slv_for_coeff_vec.get(i)->push();
                m_slv_for_coeff_vec.get(i)->assert_expr(m.mk_not(m.mk_eq(m.mk_const(m_coeff_decl_vec.get(i)), value_for_coeff)));

            }


            if (++m_current_slv_for_coeff ==  m_slv_for_coeff_vec.size())
            {
                m_current_slv_for_coeff = 0;
            }
            return mdl;

        }
        else return get_coeff_model_from_slv(m_slv_for_coeff, spec_for_concrete_x, heuristic);

    }



    void misynth_solver::generate_coeff_decl(func_decl_ref_vector & synth_funs)
    {
        m_coeff_decl_vec.reset();

        // for function synth_funs.get(0)
        unsigned num_of_coeff = synth_funs.get(0)->get_arity();
        std::string coeff_prefix = "C";

        for (unsigned i = 0; i < num_of_coeff + 1; ++i)
        {
            func_decl_ref coef(
                m.mk_const_decl(coeff_prefix + std::to_string((i)),
                                synth_funs.get(0)->get_range()), m);
            m_coeff_decl_vec.push_back(coef);
        }
    }



    /*void misynth_solver::rewrite_expr(expr *f, expr_ref &res, app2expr_map& subst)
    {
        invocations_rewriter_cfg inv_cfg(m, subst);
        rewriter_tpl<invocations_rewriter_cfg> rwr(m, false, inv_cfg);
        rwr(f, res);
    }*/
    void misynth_solver::init_used_variables(func_decl_ref_vector & synth_funs, expr_ref spec)
    {
        decl_collector decls(m);
        decls.visit(spec);

        for (func_decl *fd :  decls.get_func_decls())
        {
            if (VERBOSE)
            {
                //std::cout << "add used var: " << fd->get_name() << "  " << mk_ismt2_pp(fd, m, 3)  << std::endl;
            }

            if (!synth_funs.contains(fd))
            {
                m_used_vars.push_back(fd);
            }
        }


    }


    bool misynth_solver::solve(func_decl_ref_vector & synth_funs, expr_ref_vector & constraints,  obj_map<func_decl, args_t *> &synth_fun_args_decl)
    {
        // [+] INITIALIZE
        m_current_slv_for_coeff = 0;
        params_ref params;
        expr_ref spec = m_utils.con_join(constraints);

        m_slv_for_coeff = m_cmd.get_solver_factory()(m, params, false, true, false, symbol::null);

        for (unsigned int i = 0; i < synth_funs.get(0)->get_arity() + 1; ++i)
        {
            m_slv_for_coeff_vec.push_back(m_cmd.get_solver_factory()(m, params, false, true, false, symbol::null));
        }

        // [-] INITIALIZE


        m_synth_fun_args_decl = synth_fun_args_decl; // COPY
        collect_invocation_operands(spec, synth_funs, m_ops);

        //std::cout << "m_ops size: " << m_ops.size() << std::endl;
        if (prove_unrealizability(spec))
        {
            std::cout << "Unrealizability!!! Specification is unsat \n. " << std::endl;
            return false;
        }

        init_used_variables(synth_funs, spec);

        generate_coeff_decl(synth_funs);
        expr_ref spec_with_coeff(m);
        invocations_rewriter inv_rwr(m_cmd, m);
        inv_rwr.rewriter_functions_to_linear_term(m_coeff_decl_vec, synth_funs, spec, spec_with_coeff);

        if (VERBOSE)
        {
            std::cout << "spec_with_coeff: " << mk_ismt2_pp(spec_with_coeff, m, 3) << std::endl;
        }


        //params_ref params;
        ref<solver> slv_for_prec = m_cmd.get_solver_factory()(m, params, false, true, false, symbol::null);
        ref<solver> slv_for_coeff = m_cmd.get_solver_factory()(m, params, false, true, false, symbol::null);

        m_slv_for_prec_completing_cond = m_cmd.get_solver_factory()(m, params, false, true, false, symbol::null);

        expr_ref last_precond(0, m);

        //func_decl *fd  = m.mk_const_decl("x", m_arith.mk_int());
        //precond = m_arith.mk_lt(m.mk_const(fd), m_arith.mk_int(0));

        //precond = spec_with_coeff;
        args_t *args_decl = get_args_decl_for_synth_fun(synth_funs.get(0));


        const unsigned int MAX_ITERATION = UINT_MAX;

        unsigned int current_assumption_idx = 0;
        unsigned int attempt_number_current_assumption = 0;
        bool pushed_assumption = false;


        bool is_added_heuristic = false;

        unsigned int  current_iter_model_x = UINT_MAX - 1;
        unsigned int  current_iter_trivial_model_x = 0;

        expr_ref spec_for_concrete_x(m);
        model_ref mdl_for_x;

        expr_ref  heuristic_constaraint_coeff(generate_heuristic_constaraint_coeff(spec, m_coeff_decl_vec));

        std::cout << "generated heuristic: " << mk_ismt2_pp(heuristic_constaraint_coeff, m, 0) << std::endl;

        args_t *synth_fun_args = get_args_decl_for_synth_fun(synth_funs.get(0));

        expr_ref_vector all_precs_for_ops(m);
        slv_for_prec->push();
        slv_for_prec->assert_expr(m.mk_true());

        for (unsigned int i = 0; i < MAX_ITERATION; ++i)
        {
            iters_main_alg++;
            if (DEBUG_MODE)
                std::cout << "====  Itreration #" << i << "  ====" << std::endl;

            if (last_precond.get()) // non first iteration
            {

                expr_ref_vector precs_for_one_op(m);
                for (unsigned int i = 0; i < m_ops.size(); ++i)
                {
                    invocation_operands &op = m_ops.get(i);

                    expr_ref called_prec = m_utils.replace_vars_decl(last_precond, *args_decl, op);
                    precs_for_one_op.push_back(m.mk_not(called_prec));

                    //slv_for_prec->push();
                    //slv_for_prec->assert_expr(m.mk_not(called_prec));

                    if (DEBUG_MODE)
                    {
                        //std::cout << "add to solver called precondition: " << mk_ismt2_pp(slv_for_prec->get_assertion(slv_for_prec->get_num_assertions() - 1), m, 0) << std::endl;
                    }
                }

                all_precs_for_ops.push_back(m_utils.con_join(precs_for_one_op));

                slv_for_prec->pop(1);// pop previos precs
                slv_for_prec->push();
                slv_for_prec->assert_expr(m_utils.dis_join(all_precs_for_ops));
                std::cout << "Current precs: " << mk_ismt2_pp(slv_for_prec->get_assertion(slv_for_prec->get_num_assertions() - 1), m, 0) << std::endl;

                last_precond = 0;
            }
            if (current_iter_model_x++ >= (m_params.attempts_per_one_model_x() + m_params.trivial_attempts_per_one_model_x()))
            {
                current_iter_model_x = 0;
                current_iter_trivial_model_x = 0;
                if (attempt_number_current_assumption >= m_params.attempts_per_one_assumption())
                {
                    ++current_assumption_idx;
                    attempt_number_current_assumption = 0;
                }
                if (current_assumption_idx < m_assumptions.size())
                {
                    pushed_assumption = true;
                    slv_for_prec->push();
                    slv_for_prec->assert_expr(m_assumptions.get(current_assumption_idx));
                    std::cout << "pushed assumption " << mk_ismt2_pp(m_assumptions.get(current_assumption_idx), m, 0) << std::endl;

                    ++attempt_number_current_assumption;
                }

                lbool r = slv_for_prec->check_sat();
                if (pushed_assumption)
                {
                    slv_for_prec->pop(1); //remove assumption
                    pushed_assumption = false;
                }
                if (r != lbool::l_true)//without assumption
                {
                    current_assumption_idx++;
                    r = slv_for_prec->check_sat();
                }




                if (r == lbool::l_true)
                {

                    slv_for_prec->get_model(mdl_for_x);
                    std::cout << "SAT Precond!! "  << std::endl;

                    if (prove_unrealizability_with_mdl(spec, mdl_for_x))
                    {
                        return false;
                    }

                    //push to blacklist
                    //slv_for_prec->push();
                    //slv_for_prec->assert_expr(m.mk_not(m_utils.get_logic_model_with_default_value(mdl_for_x, m_used_vars)));

                    // slv->pop(1);
                    /*std::cout << "SAT Precond!! " << *mdl << std::endl;

                    for (func_decl *fd : m_used_vars)
                    {
                        expr_ref e( to_expr(m.mk_const(fd)), m) ;
                        std::cout << fd->get_name() << " " <<  mk_ismt2_pp((*mdl)(e), m, 3) << std::endl;
                    }*/
                }
                else
                {
                    std::cout << "!!! UNSAT of precs with replaced operands"  << std::endl;
                    model_ref mdl = m_utils.get_model(spec_with_coeff);
                    if (try_find_simultaneously_branches(synth_funs, constraints, mdl))
                        return true;
                    continue;

                    // completed_solving(synth_funs, constraints);
                    //return true;
                }


                spec_for_concrete_x = m_utils.replace_vars_according_to_model(spec_with_coeff, mdl_for_x, m_used_vars, true);
            }
            else// simply check sat of prec
            {
                lbool r = slv_for_prec->check_sat();
                if (r == lbool::l_false)
                {
                    std::cout << "!!! UNSAT of precs with replaced operands"  << std::endl;
                    std::cout << "ERROR!!!! TODO: simply check sat of prec" << r << std::endl;
                    //completed_solving(synth_funs, constraints);
                    model_ref mdl = m_utils.get_model(spec_with_coeff);
                    if (try_find_simultaneously_branches(synth_funs, constraints, mdl))
                        return true;
                    continue;

                }

            }
            if (DEBUG_MODE)
            {
                std::cout << "spec_with_coeff " << mk_ismt2_pp(spec_with_coeff, m, 3) << std::endl;
                std::cout << "spec_for_concrete_x " << mk_ismt2_pp(spec_for_concrete_x, m, 3) << std::endl;
            }


            /*
             * [+] getting model for coefficients
             * */
            if (current_iter_trivial_model_x++ < m_params.trivial_attempts_per_one_model_x())
            {
                std::cout << "pushed heuristic constaraint for coeff" << std::endl;
                is_added_heuristic = true;
                //slv_for_coeff->push();
                //slv_for_coeff->assert_expr(heuristic_constaraint_coeff);
            }
            /*else if (current_iter_trivial_model_x >= m_params.trivial_attempts_per_one_model_x() && is_added_heuristic)
            {
                std::cout << "popped heuristic constaraint for coeff" << std::endl;
                is_added_heuristic = false;
                slv_for_coeff->pop(1);
            }*/
            ++current_iter_trivial_model_x;




            /*
            slv_for_coeff->push();
            slv_for_coeff->assert_expr(spec_for_concrete_x);
            lbool res_spec_for_x = slv_for_coeff->check_sat();

            model_ref mdl_for_coeff;

            if (res_spec_for_x != lbool::l_true)
            {
                //TODO: take into account a heuristic
                if (is_added_heuristic)
                {
                    std::cout << "WARNING!!! Heuristic for this spec and model x is unsat. " << std::endl;
                    is_added_heuristic = false;
                    slv_for_coeff->pop(2); // remove spec_for_concrete_x and heuristic
                    continue;
                }

                std::cout << "WARNING!!! There are several branches. " << std::endl;

                if (try_find_simultaneously_branches(synth_funs, constraints, mdl_for_x))
                    return true;

                //return false;
            }

            slv_for_coeff->get_model(mdl_for_coeff);
            slv_for_coeff->pop(1);
            if (is_added_heuristic)
            {
                slv_for_coeff->pop(1);
                is_added_heuristic = false;
            }
            */

            model_ref mdl_for_coeff = get_coeff_model(spec_for_concrete_x, is_added_heuristic ? heuristic_constaraint_coeff : expr_ref(m));
            is_added_heuristic = false;

            if (!mdl_for_coeff)
            {
                std::cout << "WARNING!!! There are several branches. " << std::endl;

                if (try_find_simultaneously_branches(synth_funs, constraints, mdl_for_x))
                    return true;

                // TODO:???

            }
            std::cout << "SAT res_spec_for_x!! " << *mdl_for_coeff << std::endl;
            //simplify spec for concrete coef
            expr_ref branch = m_futils.generate_branch(m_coeff_decl_vec, *synth_fun_args, synth_funs, mdl_for_coeff);

            expr_ref additional_cond = generate_fun_macros(branch, synth_funs, *synth_fun_args);
            expr_ref simplified_spec = m_utils.simplify_context_cond(spec, additional_cond);
            std::cout << "simplified_spec for concrete coeff " << mk_ismt2_pp(simplified_spec, m, 3) << std::endl;

            //
            //expr_ref spec_for_concrete_coeff(m);
            //spec_for_concrete_coeff = m_utils.replace_vars_according_to_model(spec_with_coeff, mdl_for_coeff, m_coeff_decl_vec, true);
            // std::cout << "spec_for_concrete_coeff " << mk_ismt2_pp(spec_for_concrete_coeff, m, 3) << std::endl;
            /*[-] */



            /*[+] Find a precondition*/
            last_precond = find_precondition(synth_funs, simplified_spec, mdl_for_coeff);

            /*expr_ref_vector eval_coeff_model(m);
            for (func_decl *fd : m_coeff_decl_vec)
            {
                eval_coeff_model.push_back((*mdl_for_coeff)(m.mk_const(fd)));
            }
            //remember this coef
            slv_for_coeff->push();
            slv_for_coeff->assert_expr(m.mk_not(m_utils.mk_eq(m_coeff_decl_vec, eval_coeff_model)));*/

            if (m_utils.is_unsat(last_precond))
            {
                last_precond = 0;
                std::cout << "!!! Precond is unsat" << std::endl;
                continue;
            }



            if (m_utils.is_unsat(m.mk_not(last_precond)))
                //if(m.is_true(last_precond))
            {
                m_branches.reset();
                m_precs.reset();
                m_precs.push_back(m.mk_true());
                m_branches.push_back(branch);
                completed_solving(synth_funs, constraints);
                return true;
            }

            m_precs.push_back(last_precond);
            m_branches.push_back(branch);

            m_slv_for_prec_completing_cond->push();
            m_slv_for_prec_completing_cond->assert_expr(m.mk_not(last_precond));



            /*[-] */
            if (DEBUG_MODE)
            {
                std::cout << "-------------------" << std::endl;
                std::cout << mk_ismt2_pp(last_precond, m, 0) << "  ==> " << mk_ismt2_pp(m_branches.back(), m, 0) << std::endl;
            }

            if (try_find_simultaneously_branches(synth_funs, constraints, 0))
                return true;




        }

        return false;
    }




    bool misynth_solver::try_find_simultaneously_branches(func_decl_ref_vector & synth_funs, expr_ref_vector & constraints, model_ref mdl_for_x)
    {
        args_t *synth_fun_args = get_args_decl_for_synth_fun(synth_funs.get(0));


        search_simultaneously_branches search(m_cmd, m);
        int is_added_heuristic = m_params.type_heuristic_branches();

        params_ref params_slv;
        //slv_for_x_prec = m_cmd.get_solver_factory()(m, params_slv, false, true, false, symbol::null);



        unsigned int iter = 0;
        bool is_infinity_loop = false;

        if (mdl_for_x.get())
        {
            is_infinity_loop = true; // if alg1 gave a model
            std::cout << "start search_simultaneously_branches with mdl: " << *mdl_for_x << std::endl;

            m_branches.reset();
            m_precs.reset();
            search(synth_funs, constraints, mdl_for_x, *synth_fun_args, m_branches, m_precs, is_added_heuristic);
            m_slv_for_prec_completing_cond = m_cmd.get_solver_factory()(m, params_slv, false, true, false, symbol::null);
            for (expr * e : m_precs)
            {
                m_slv_for_prec_completing_cond->push();
                m_slv_for_prec_completing_cond->assert_expr(m.mk_not(e));
                std::cout << "prec " << mk_ismt2_pp(e, m, 3) << std::endl;
            }
        }



        sanity_checker sanity(m_cmd, m);
        while (is_infinity_loop || m_precs.size() == 0 || m_slv_for_prec_completing_cond->check_sat() == lbool::l_false)
        {
            if (iter >= m_params.trivial_attempts_simultaneously_branches())
            {
                is_added_heuristic = 0;
            }
            // else ++is_added_heuristic;

            std::cout << "Completing condition is sat!  "  << std::endl;
            expr_ref fun_body = generate_clia_fun_body(true);

            bool sanity_res = sanity.check(constraints, m_used_vars, fun_body, synth_funs, *synth_fun_args, mdl_for_x);
            if (sanity_res)
            {
                completed_solving(synth_funs, constraints);
                return true;
            }
            else
            {
                std::cout << "Sanity failed, start   search_simultaneously_branches"  << *mdl_for_x << std::endl;

                m_branches.reset();
                m_precs.reset();
                alg3_run++;
                search(synth_funs, constraints, mdl_for_x, *synth_fun_args, m_branches, m_precs, is_added_heuristic);

                m_slv_for_prec_completing_cond = m_cmd.get_solver_factory()(m, params_slv, false, true, false, symbol::null);
                if (m_precs.size() > 0)
                {
                    sanity.reset_constraint_for_model_x();
                }
                for (expr * e : m_precs)
                {
                    m_slv_for_prec_completing_cond->push();
                    m_slv_for_prec_completing_cond->assert_expr(m.mk_not(e));
                    std::cout << "prec " << mk_ismt2_pp(e, m, 3) << std::endl;
                }
                //try_find_simultaneously_branches(synth_funs, constraints, mdl_for_x);
            }
            iter++;
        }
        std::cout << "Completing condition is unsat!  "  << std::endl;
        return false;
    }

    void misynth_solver::completed_solving(func_decl_ref_vector & synth_funs, expr_ref_vector & constraints)
    {
        std::cout << "###Complete "  << std::endl;

        args_t *synth_fun_args = get_args_decl_for_synth_fun(synth_funs.get(0));

        std::cout << "Incompact solution: ";
        print_def_fun(std::cout, synth_funs.get(0), *synth_fun_args, generate_clia_fun_body());

        expr_ref fun_body = generate_clia_fun_body(true);
        print_def_fun(std::cout, synth_funs.get(0), *synth_fun_args, fun_body);


        sanity_checker sanity(m_cmd, m);
        bool sanity_res = sanity.check(constraints, fun_body, synth_funs, *synth_fun_args);
        std::cout << "Sanity Checker Result: " << sanity_res << std::endl;
        std::cout << iters_main_alg << " " << max_iter_iso_mor << " " << m_precs.size()  << std::endl;
        std::cout  << " alg3_run: " << alg3_run << std::endl;

        //bool sanity_res2 = sanity.check_through_implication(m_utils.con_join(constraints),  m_precs, m_branches, synth_funs, *synth_fun_args);
        //std::cout << "Sanity Checker implication Result: " << sanity_res2 << std::endl;

    }
    expr_ref misynth_solver::find_precondition(func_decl_ref_vector & synth_funs, expr_ref & spec, model_ref mdl_for_coeff)
    {
        args_t *synth_fun_args = get_args_decl_for_synth_fun(synth_funs.get(0));

        vector<invocation_operands> current_ops;
        collect_invocation_operands(spec, synth_funs, current_ops);
        expr_ref spec_with_coeff(m);
        invocations_rewriter inv_rwr(m_cmd, m);
        if (m_params.reused_brances())
        {
            inv_rwr.rewriter_functions_to_linear_term_with_prec(m_coeff_decl_vec, synth_funs, spec, spec_with_coeff, *synth_fun_args, m_precs, m_branches);
        }
        else
        {
            inv_rwr.rewriter_functions_to_linear_term(m_coeff_decl_vec, synth_funs, spec, spec_with_coeff);
        }

        std::cout << "spec_with_coeff " << mk_ismt2_pp(spec_with_coeff, m, 3) << std::endl;

        expr_ref spec_for_concrete_coeff = m_utils.replace_vars_according_to_model(spec_with_coeff, mdl_for_coeff, m_coeff_decl_vec, true);
        std::cout << "spec_for_concrete_coeff " << mk_ismt2_pp(spec_for_concrete_coeff, m, 3) << std::endl;

        //simplify
        /*expr_ref th_res(m);
        proof_ref pr(m);

        params_ref th_solv_params;
        th_rewriter s(m, th_solv_params);
        th_solver solver(m_cmd);
        s.set_solver(alloc(th_solver, m_cmd));
        s(spec_for_concrete_coeff, th_res, pr);*/
        expr_ref th_res = m_utils.simplify_context(spec_for_concrete_coeff);
        std::cout << "Simplified precondition candidate: " << mk_ismt2_pp(th_res, m, 3) << std::endl;
        //



        decl_collector decls(m);
        decls.visit(th_res);
        func_decl_ref_vector used_vars(m);

        for (func_decl *fd :  decls.get_func_decls())
        {
            if (!synth_funs.contains(fd))
            {
                used_vars.push_back(fd);
            }
        }



        expr_ref res(m);

        if (used_vars.size() == 0 || (synth_fun_args->size() == 1 && used_vars.size() == 1))
            //if (used_vars.size() <= synth_fun_args->size())
        {
            res = m_utils.replace_vars_decl(th_res, used_vars, *synth_fun_args);

            if (DEBUG_MODE)
            {
                std::cout << "used_vars.size() <= args.size()" << std::endl;

            }

            return res;
        }
        else
        {
            /*//[+]sample
            func_decl_ref_vector sample_pattern(m);
            func_decl *x_decl = m.mk_const_decl("x", m_arith.mk_int());
            sample_pattern.push_back(x_decl);
            func_decl *y_decl = m.mk_const_decl("y", m_arith.mk_int());
            //etalon.push_back(y_decl);

            expr_ref s(m);

            expr_ref_vector r_x(m);
            r_x.push_back(m.mk_const(x_decl));

            expr_ref_vector r_y(m);
            r_y.push_back(m.mk_const(y_decl));


            vector<expr_ref_vector> inv_args;
            inv_args.push_back(r_x);
            inv_args.push_back(r_y);

            expr_ref sample_expr(m_arith.mk_ge(m_arith.mk_add(m.mk_const(x_decl), m.mk_const(y_decl)), m_arith.mk_int(10)), m);
            expr_ref res2 = m_abducer.nonlinear_abduce(inv_args, expr_ref(m.mk_true(), m), sample_expr, sample_pattern);
            std::cout << "Sample x+y>=10: " << mk_ismt2_pp(sample_expr, m, 3) << mk_ismt2_pp(res2, m, 3) << std::endl;

            //[-]
            */
            if (m.is_or(th_res))
            {

                for (unsigned int i = 0; i < to_app(th_res)->get_num_args(); ++i)
                {
                    th_res = to_app(th_res)->get_arg(i);
                    res = m_abducer.nonlinear_abduce(current_ops, expr_ref(m.mk_true(), m), th_res, *synth_fun_args);
                    if (!m_utils.is_unsat(res))
                        return res;
                }
                // we take first argument

            }
            else
                res = m_abducer.nonlinear_abduce(current_ops, expr_ref(m.mk_true(), m), th_res, *synth_fun_args);


            //lit(x1) /\ lit(x2) => phi(x1, x2)
            //try_to_separate_into_disjoint_sets();


        }

        return res;
    }

    args_t *misynth_solver::get_args_decl_for_synth_fun(func_decl * f)
    {
        return m_synth_fun_args_decl[f];
    }

    bool misynth_solver::prove_unrealizability_with_mdl(expr_ref spec, model_ref & mdl)
    {
        expr_ref logic_mdl(m);
        model2expr(mdl, logic_mdl);
        if (m_utils.is_unsat(m.mk_and(spec, logic_mdl)))
        {
            if (VERBOSE)
            {
                std::cout << "Unrealizability!!! Specification is unsat. \n  with model: " << mk_ismt2_pp(logic_mdl, m, 3) << std::endl;
            }

            return true;
        }
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

        //expr_ref_vector assumptions(m);
        generate_assumptions_from_operands(m_assumptions);

        if (VERBOSE)
        {
            for (unsigned int i = 0; i < m_assumptions.size(); ++i)
            {
                std::cout << "assumptions: " << mk_ismt2_pp(m_assumptions.get(i), m, 3) << std::endl;
            }
        }
        if (m_params.check_assumptions())
            return check_assumptions(spec, m_assumptions);
        else
            return false;
    }

    bool misynth_solver::check_assumptions(expr_ref spec, expr_ref_vector & assumptions)
    {
        params_ref params;
        ref<solver> slv = m_cmd.get_solver_factory()(m, params, false, true, false, symbol::null);
        return subsets_backtracking(assumptions, spec, slv.get(), 0);
    }

    bool misynth_solver::subsets_backtracking(expr_ref_vector & assump, expr * spec, solver * slv, unsigned int index)
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
                /*else
                {
                    model_ref mdl;
                    slv->get_model(mdl);
                    m_models_from_assumptions.push_back(mdl);
                }*/

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

    void misynth_solver::generate_assumptions_from_operands(expr_ref_vector & assumptions)
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

    void misynth_solver::print_def_fun(std::ostream & out, func_decl * f, func_decl_ref_vector & args, expr_ref body)
    {
        out << "(define-fun " << f->get_name() << " (";
        m_utils.print_sorted_var_list(out, args);
        out << ") " << f->get_range()->get_name() << " ";
        out << mk_ismt2_pp(body, m, 0);
        out << ") " << std::endl;
    }

    expr_ref misynth_solver::generate_clia_fun_body(bool is_compact)
    {
        SASSERT(m_precs.size() == m_branches.size());
        expr_ref res(m);
        if (m_precs.size() == 0) return res;

        std::set<unsigned int> todo_remove;
        //[+] compaction
        if (is_compact)
        {


            for (unsigned int i = 0 ; i < m_precs.size() - 1; ++i)
            {
                if (todo_remove.find(i) != todo_remove.end())
                {
                    continue;
                }
                for (unsigned int j = 0 ; j < m_precs.size(); ++j)
                {
                    if (i != j)
                    {
                        if (todo_remove.find(j) != todo_remove.end())
                        {
                            continue;
                        }
                        if (m_utils.implies(m_precs.get(i), m_precs.get(j)))
                        {
                            //std::cout << "remove " <<  mk_ismt2_pp(m_precs.get(j), m, 0)
                            //          << " ===> " << mk_ismt2_pp(m_precs.get(i), m, 0) << std::endl;
                            todo_remove.insert(i);
                            break;
                        }
                        else if (m_utils.implies(m_precs.get(j), m_precs.get(i)))
                        {
                            todo_remove.insert(j);
                            //std::cout << "remove " <<  mk_ismt2_pp(m_precs.get(i), m, 0)
                            //         << " ===> " << mk_ismt2_pp(m_precs.get(j), m, 0) << std::endl;

                        }

                    }
                }
            }
        }
        //[-] compaction

        for (unsigned int i = m_precs.size() - 1 ; i < m_precs.size(); --i)
        {
            if (todo_remove.find(i) != todo_remove.end())
            {
                continue;
            }
            res = m_branches.get(i);
            break;
        }

        expr_ref_vector v(m);

        for (unsigned int i = 0 ; i < m_precs.size() - 1; ++i)
        {
            if (todo_remove.find(i) != todo_remove.end())
            {
                continue;
            }
            res = m.mk_ite(m_precs.get(i), m_branches.get(i), res);
        }
        return res;
    }

    expr_ref misynth_solver::generate_heuristic_constaraint_coeff(expr_ref spec, func_decl_ref_vector & coeff_decls)
    {
        if (m_params.type_heuristic() == 1)
        {
            expr_ref_vector v(m);
            //for (func_decl * fd : coeff_decls)
            for (unsigned int i = 0; i < coeff_decls.size(); i++)
            {
                func_decl * fd = coeff_decls.get(i);
                expr_ref e(m.mk_const(fd), m);
                v.push_back(m.mk_or(
                                m.mk_eq(e, m_arith.mk_int(-1)),
                                m.mk_eq(e, m_arith.mk_int(0)),
                                m.mk_eq(e, m_arith.mk_int(1))
                            ));
            }
            //v.reverse();
            return m_utils.dis_join(v);
        }
        else if (m_params.type_heuristic() == 2)
        {
            expr_ref_vector v(m);
            //for (func_decl * fd : coeff_decls)
            for (unsigned int i = 0; i < coeff_decls.size(); i++)
            {
                func_decl * fd = coeff_decls.get(i);
                expr_ref e(m.mk_const(fd), m);
                v.push_back(m.mk_or(
                                m.mk_eq(e, m_arith.mk_int(-1)),
                                m.mk_eq(e, m_arith.mk_int(0)),
                                m.mk_eq(e, m_arith.mk_int(1))
                            ));
            }
            //v.reverse();
            return m_utils.con_join(v);

        }
        else
        {

            expr_set constants_set;
            collect_consts(spec, constants_set, m);
            expr_ref_vector v(m);
            //for (func_decl * fd : coeff_decls)
            for (unsigned int i = 0; i < coeff_decls.size(); i++)
            {
                func_decl * fd = coeff_decls.get(i);
                expr_ref e(m.mk_const(fd), m);
                expr_ref_vector disj(m);
                disj.push_back(m.mk_eq(e, m_arith.mk_int(-1)));
                disj.push_back(m.mk_eq(e, m_arith.mk_int(0)));
                disj.push_back(m.mk_eq(e, m_arith.mk_int(1)));
                for (auto it = constants_set.begin(); it != constants_set.end(); it++)
                {
                    disj.push_back(m.mk_eq(e, *it));
                    disj.push_back(m.mk_eq(e, m_arith.mk_uminus(*it)));
                }
                v.push_back(m_utils.dis_join(disj));
            }
            //v.reverse();
            return m_utils.con_join(v);
        }
    }


    expr_ref misynth_solver::generate_fun_macros(expr_ref body_fun, func_decl_ref_vector & synth_funs, func_decl_ref_vector args)
    {
        func_decl *fd = synth_funs.get(0);

        expr_ref_vector args_app(m);
        for (auto &fd : args)
        {
            args_app.push_back(m.mk_const(fd));
        }
        expr_ref fd_eq_body_fun(m.mk_eq(m.mk_app(fd, args_app.size(), args_app.c_ptr()), body_fun), m);
        expr_ref macros(m_utils.universal_quantified(fd_eq_body_fun, args));

        return macros;
    }
} // namespace misynth
