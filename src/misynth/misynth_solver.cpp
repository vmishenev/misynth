#include "misynth_solver.h"
#include "collector_invocation_operands.h"
#include "rewriter_coefficients.h"
#include "ast/ast_pp.h"
#include "ast/rewriter/rewriter.h"
#include "ast/rewriter/rewriter_def.h"
#include <iomanip>
#include <iostream>
#include <set>

#include <ast/used_vars.h>
#include <ast/rewriter/th_rewriter.h>
#include "sanity_checker.h"




#define VERBOSE true
#define DEBUG true

namespace misynth
{

    bool DEBUG_MODE = true;
    misynth_solver::misynth_solver(cmd_context &cmd_ctx, ast_manager &m, solver *solver)
        : m_cmd(cmd_ctx)
        , m(m)
        , m_solver(solver)
        , m_utils(cmd_ctx, m)
        , m_arith(m)
        , m_coeff_decl_vec(m),

          m_used_vars(m),
          m_precs(m),
          m_branches(m),
          m_terms(m),
          m_abducer(cmd_ctx, m)
    {
    }

    void misynth_solver::generate_coeff_decl(func_decl_ref_vector &synth_funs)
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



    void misynth_solver::rewriter_functions_to_linear_term(func_decl_ref_vector &synth_funs,
            expr_ref spec, expr_ref &new_spec)
    {
        invocation_collector collector(synth_funs);
        collector(spec);

        generate_coeff_decl(synth_funs);
        obj_hashtable<app > set = collector.get_invocation();

        /*
         *
         * scoped_ptr<expr_replacer> rp = mk_default_expr_replacer(m());
                        expr_substitution sub(m());
                        sub.insert(a, z());
                        rp->set_substitution(&sub);
         * */

        for (auto it = set.begin(); it != set.end(); it++)
        {
            app *ap_f = (*it);
            expr_ref_vector mult_terms(m);
            mult_terms.push_back(m.mk_const(m_coeff_decl_vec.get(0)));


            for (unsigned i = 0; i < ap_f->get_num_args(); ++i)
            {
                expr *term = m_arith.mk_mul(m.mk_const(m_coeff_decl_vec.get(1 + i)), ap_f->get_arg(i));
                mult_terms.push_back(term);
            }

            expr_ref linear_term = m_arith.mk_add_simplify(mult_terms);
            m_term_subst.insert(ap_f, linear_term);
            m_terms.push_back(linear_term);
        }

        rewrite_expr(spec, new_spec);

    }

    void misynth_solver::rewrite_expr(expr *f, expr_ref &res)
    {
        invocations_rewriter_cfg inv_cfg(m, m_term_subst);
        rewriter_tpl<invocations_rewriter_cfg> rwr(m, false, inv_cfg);
        rwr(f, res);
    }
    void misynth_solver::init_used_variables(func_decl_ref_vector &synth_funs, expr_ref spec)
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
    expr_ref misynth_solver::generate_branch(func_decl_ref_vector &synth_funs, model_ref mdl)
    {
        func_decl_ref_vector *args_decl = get_args_decl_for_synth_fun(synth_funs.get(0));

        //get coeeficients
        expr_ref_vector  mult_terms(m);

        for (unsigned i = 0; i < m_coeff_decl_vec.size(); ++i)
        {

            expr_ref val = (*mdl)(m.mk_const(m_coeff_decl_vec.get(i)));



            if (m_arith.is_numeral(val))
            {
                if (i == 0)
                {
                    mult_terms.push_back(val);
                    continue;
                }
                else
                {
                    mult_terms.push_back(m_arith.mk_mul(val, m.mk_const(args_decl->get(i - 1))));
                }
            }
            else
            {
                //mult_terms.push_back(m_arith.mk_mul(m_arith.mk_int(0), m.mk_const(args_decl.get(i))));

            }
        }

        return m_arith.mk_add_simplify(mult_terms);
    }

    bool misynth_solver::solve(func_decl_ref_vector &synth_funs, expr_ref spec,  obj_map<func_decl, args_t *> &synth_fun_args_decl)
    {
        // [+] INITIALIZE
        // [-] INITIALIZE


        m_synth_fun_args_decl = synth_fun_args_decl; // COPY
        collect_invocation_operands(spec, synth_funs, m_ops);

        //std::cout << "m_ops size: " << m_ops.size() << std::endl;
        prove_unrealizability(spec);

        init_used_variables(synth_funs, spec);


        expr_ref spec_with_coeff(m);
        rewriter_functions_to_linear_term(synth_funs, spec, spec_with_coeff);

        if (VERBOSE)
        {
            std::cout << "spec_with_coeff: " << mk_ismt2_pp(spec_with_coeff, m, 3) << std::endl;
        }

        /* used_vars uv;

         for (unsigned i = 0; i < uv.get_num_vars(); ++i)
         {
             if (uv.get(i))
             }*/

        params_ref params;
        ref<solver> slv_for_prec = m_cmd.get_solver_factory()(m, params, false, true, false, symbol::null);
        ref<solver> slv_for_coeff = m_cmd.get_solver_factory()(m, params, false, true, false, symbol::null);

        expr_ref last_precond(m.mk_false(), m);

        //func_decl *fd  = m.mk_const_decl("x", m_arith.mk_int());
        //precond = m_arith.mk_lt(m.mk_const(fd), m_arith.mk_int(0));

        //precond = spec_with_coeff;
        args_t *args_decl = get_args_decl_for_synth_fun(synth_funs.get(0));


        const unsigned int MAX_ITERATION = 5;

        for (unsigned int i = 0; i < MAX_ITERATION; ++ i)
        {

            if (DEBUG_MODE)
            {
                std::cout << "====  Itreration #" << i << "  ====" << std::endl;
            }


            if (i > 0) // non first iteration
                for (unsigned int i = 0; i < m_ops.size(); ++i)
                {
                    invocation_operands &op = m_ops.get(i);

                    expr_ref called_prec = m_utils.replace_vars_decl(last_precond, *args_decl, op);
                    slv_for_prec->push();
                    slv_for_prec->assert_expr(m.mk_not(called_prec));

                    if (DEBUG_MODE)
                    {
                        std::cout << "add to solver called precondition " << mk_ismt2_pp(slv_for_prec->get_assertion(slv_for_prec->get_num_assertions() - 1), m, 0) << std::endl;
                    }
                }



            lbool r = slv_for_prec->check_sat();
            expr_ref spec_for_concrete_x(m);

            if (r == lbool::l_true)
            {
                model_ref mdl;
                slv_for_prec->get_model(mdl);
                std::cout << "SAT Precond!! "  << std::endl;
                spec_for_concrete_x = m_utils.replace_vars_according_to_model(spec_with_coeff, mdl, m_used_vars);
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

                std::cout << "Complete " << r << std::endl;
                sanity_checker sanity(m_cmd, m);
                args_t *synth_fun_args = get_args_decl_for_synth_fun(synth_funs.get(0));

                bool sanity_res = sanity.check(spec, m_precs, m_branches, synth_funs, *synth_fun_args);
                std::cout << "Sanity Checker Result: " << sanity_res << std::endl;
                return true;
            }

            if (DEBUG_MODE)
            {
                std::cout << "spec_with_coeff " << mk_ismt2_pp(spec_with_coeff, m, 3) << std::endl;
                std::cout << "spec_for_concrete_x " << mk_ismt2_pp(spec_for_concrete_x, m, 3) << std::endl;
            }


            /*
             * [+] getting model for coefficients
             * */

            slv_for_coeff->push();
            slv_for_coeff->assert_expr(spec_for_concrete_x);
            lbool res_spec_for_x = slv_for_coeff->check_sat();
            expr_ref spec_for_concrete_coeff(m);

            if (res_spec_for_x == lbool::l_true)
            {
                model_ref mdl;
                slv_for_coeff->get_model(mdl);
                slv_for_coeff->pop(1);
                std::cout << "SAT res_spec_for_x!! " << *mdl << std::endl;
                spec_for_concrete_coeff = m_utils.replace_vars_according_to_model(spec_with_coeff, mdl, m_coeff_decl_vec);
                std::cout << "spec_for_concrete_coeff " << mk_ismt2_pp(spec_for_concrete_coeff, m, 3) << std::endl;
                expr_ref branch = generate_branch(synth_funs, mdl);
                m_branches.push_back(branch);
            }
            else
            {
                std::cout << "WARNING!!! There are several branches. " << std::endl;
                return false;
            }


            /*[-] */



            /*[+] Find a precondition*/
            last_precond = find_precondition(synth_funs, spec_for_concrete_coeff);
            m_precs.push_back(last_precond);


            /*[-] */
            if (DEBUG_MODE)
            {
                std::cout << "-------------" << std::endl;
                std::cout << mk_ismt2_pp(last_precond, m, 0) << "  ==> " << mk_ismt2_pp(m_branches.back(), m, 0) << std::endl;
            }

        }

        return false;
    }

    expr_ref misynth_solver::find_precondition(func_decl_ref_vector &synth_funs, expr_ref &spec_for_concrete_coeff)
    {

        //simplify
        expr_ref th_res(m);
        proof_ref pr(m);

        params_ref th_solv_params;
        th_rewriter s(m, th_solv_params);
        th_solver solver(m_cmd);
        s.set_solver(alloc(th_solver, m_cmd));
        s(spec_for_concrete_coeff, th_res, pr);
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

        args_t *synth_fun_args = get_args_decl_for_synth_fun(synth_funs.get(0));

        expr_ref res(m);

        if (DEBUG_MODE)
        {
            // std::cout << " args.size()" << args->size() << std::endl;

        }

        if (used_vars.size() <= synth_fun_args->size())
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
            res = m_abducer.nonlinear_abduce(m_ops, expr_ref(m.mk_true(), m), th_res, *synth_fun_args);

            //lit(x1) /\ lit(x2) => phi(x1, x2)
            //try_to_separate_into_disjoint_sets();


        }

        return res;
    }

    args_t *misynth_solver::get_args_decl_for_synth_fun(func_decl *f)
    {
        return m_synth_fun_args_decl[f];
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
