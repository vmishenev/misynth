#ifndef SEARCH_SIMULTANEOUSLY_BRANCHES_H
#define SEARCH_SIMULTANEOUSLY_BRANCHES_H

#include "cmd_context/cmd_context.h"
#include "smt_utils.h"
#include "rewriter_coefficients.h"
#include "collector_invocation_operands.h"
#include "ast/ast_pp.h"
#include "misynth/multi_abducer.h"
#include "misynth/function_utils.h"
#include "misynth/ite_function.h"

#include "misynth/combinators.h"

#include <iostream>
#define DEBUG(x) std::cout<< x << std::endl;

namespace misynth
{
    extern bool DEBUG_MODE;
    class search_simultaneously_branches
    {
        private:
            cmd_context &m_cmd;
            ast_manager &m;
            arith_util m_arith;
            smt_utils m_utils;
            function_utils m_futils;
            vector<func_decl_ref_vector> m_coeff_decl_vec;
            multi_abducer m_abducer;
            synth_params m_params;
            ref<solver> m_coeff_solver;
        public:
            search_simultaneously_branches(cmd_context &cmd_ctx, ast_manager &m)
                : m_cmd(cmd_ctx)
                , m(m)
                , m_arith(m)
                , m_utils(cmd_ctx, m)
                , m_futils(cmd_ctx, m)
                , m_abducer(cmd_ctx, m)
            {
                params_ref params;
                m_coeff_solver = m_cmd.get_solver_factory()(m, params, false, true, false, symbol::null);
            }

            void generate_coeff_decl(func_decl_ref_vector &synth_funs, unsigned int n)
            {
                m_coeff_decl_vec.reset();

                // for function synth_funs.get(0)
                unsigned num_of_coeff = synth_funs.get(0)->get_arity();
                std::string coeff_prefix = "C";
                std::string separator = "_";
                for (unsigned int i = 0; i < n; ++i)
                {
                    func_decl_ref_vector current_coeff_tuple(m);
                    for (unsigned int j = 0; j < num_of_coeff + 1; ++j)
                    {
                        func_decl_ref coef(
                            m.mk_const_decl(coeff_prefix + std::to_string(j) + separator + std::to_string(i),
                                            synth_funs.get(0)->get_range()), m);
                        current_coeff_tuple.push_back(coef);
                    }
                    m_coeff_decl_vec.push_back(current_coeff_tuple);
                }
            }

            expr_ref replace_invocations(expr_ref spec, vector<app_ref_vector> &distinct_invocation)
            {
                expr_ref new_spec(m);

                app2expr_map  term_subst;
                expr_ref_vector accumulator_terms(m);
                invocations_rewriter inv_rwr(m_cmd, m);

                for (unsigned int i = 0; i < distinct_invocation.size(); ++i)
                {
                    //replace i-th invocations group on i-th m_coeff_decl_vec[i]
                    func_decl_ref_vector &current_coeff_tuple = m_coeff_decl_vec.get(i);
                    app_ref_vector & current_invocation = distinct_invocation.get(i);
                    for (unsigned int j = 0; j < current_invocation.size(); ++j)
                    {

                        expr_ref res = inv_rwr.rewrite_app(current_invocation.get(j), current_coeff_tuple);
                        accumulator_terms.push_back(res);
                        term_subst.insert(current_invocation.get(j), res);
                    }
                }
                inv_rwr.rewrite_expr(spec, new_spec, term_subst);
                return new_spec;
            }

            expr_ref generate_constraints()
            {
                if (m_coeff_decl_vec.size() <= 1)
                    return expr_ref(m.mk_true(), m);

                expr_ref_vector v(m);
                for (unsigned int i = 0; i < m_coeff_decl_vec.size(); ++i)
                {
                    //expr_ref_vector& crnt_tuple = m_coeff_decl_vec.get(i);
                    for (unsigned int j = 0; j < i; ++j)
                    {
                        v.push_back(m.mk_not(m_utils.mk_eq(m_coeff_decl_vec.get(i), m_coeff_decl_vec.get(j))));
                    }
                }
                return m_utils.dis_join(v);
            }
            void collects_single_conjuncts(expr_ref_vector & constraints, func_decl_ref_vector & synth_funs, model_ref mdl_for_x, expr_ref_vector & res)
            {
                for (auto it = constraints.begin(); it != constraints.end(); it++)
                {
                    if (m.is_and(*it))
                    {
                        app* ap = to_app(*it);
                        for (unsigned int i = 0; i < ap->get_num_args(); ++i)
                        {
                            if (is_single_invocation(ap->get_arg(i), synth_funs, mdl_for_x))
                                res.push_back(ap->get_arg(i));

                        }
                    }
                    else
                    {
                        if (is_single_invocation(*it, synth_funs, mdl_for_x))
                            res.push_back(*it);
                    }
                }
            }
            bool is_single_invocation(expr *e, func_decl_ref_vector & synth_funs, model_ref mdl_for_x)
            {
                vector<app_ref_vector> distinct_invocation;
                collect_distinct_invocation(e, synth_funs, mdl_for_x, distinct_invocation);
                return  distinct_invocation.size() <= 1;
            }

            void collect_used_variables(expr_ref spec,  func_decl_ref_vector &exclude, func_decl_ref_vector &res)
            {
                decl_collector decls(m);
                decls.visit(spec);

                for (func_decl *fd :  decls.get_func_decls())
                {
                    if (!exclude.contains(fd))
                    {
                        res.push_back(fd);
                    }
                }


            }

            model_ref get_coeff_model_from_slv(ref<solver> &slv, expr_ref spec_for_concrete_x, expr_ref heuristic)
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
                            slv->pop(1);//remove spec
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


                return mdl_for_coeff;

            }
            void operator()(func_decl_ref_vector & synth_funs, expr_ref_vector & constraints, model_ref mdl_for_x, func_decl_ref_vector &synth_fun_args, ite_function &fn, ite_function &result_fn, int is_added_heuristic = 0)
            {
                expr_ref_vector precs(fn.get_precs());
                expr_ref_vector branches(fn.get_branches());
                std::cout << "Search simulteneosly "  << std::endl;
                std::cout << "for current partial-fn:" <<  mk_ismt2_pp(fn.generate_clia_fun_body(true), m, 0) << std::endl;
                expr_ref spec = m_utils.con_join(constraints);
                invocations_rewriter inv_rwr(m_cmd, m);

                expr_ref spec_and_reused_branches(spec, m);
                vector<unsigned int> used_branches;
                if (m_params.reused_brances())
                {
                    inv_rwr.rewrite_app_with_branch(spec, synth_funs, precs, branches, synth_fun_args, spec_and_reused_branches, mdl_for_x, used_branches);
                    std::cout << "Reused spec_and_reused_branches: " << mk_ismt2_pp(spec_and_reused_branches, m, 3)  << std::endl;
                }

                vector<app_ref_vector> distinct_invocation;
                //for (auto it = constraints.begin(); it != constraints.end(); it++)
                collect_distinct_invocation(spec_and_reused_branches, synth_funs, mdl_for_x, distinct_invocation);
                std::cout << "distinct_invocation.size() : " << distinct_invocation.size()  << std::endl;
                if (distinct_invocation.size() < 1)
                {
                    std::cout << "WARNING!!! This spec isn't multiinvocation " << std::endl;
                    if (used_branches.size() == 0)
                        return;
                    std::cout << "Try to remove reused branches " << std::endl;
                    fn.remove_branches(used_branches);
                    /*for (unsigned int i : used_branches)
                    {
                        precs.set(i, m.mk_false());
                    }*/
                    (*this)(synth_funs, constraints, mdl_for_x, synth_fun_args, fn, result_fn, is_added_heuristic);
                    return;
                }
                generate_coeff_decl(synth_funs, distinct_invocation.size());

                func_decl_ref_vector used_vars(m);
                collect_used_variables(spec, synth_funs, used_vars);

                expr_ref spec_with_coeffs = replace_invocations(spec_and_reused_branches, distinct_invocation);

                std::cout << "spec_with_coeffs: " << mk_ismt2_pp(spec_with_coeffs, m, 3)  << std::endl;
                expr_ref spec_with_x_coeffs =  m_utils.replace_vars_according_to_model(spec_with_coeffs, mdl_for_x, used_vars, true);
                std::cout << "spec_with_x_coeffs: " << mk_ismt2_pp(spec_with_x_coeffs, m, 3)  << std::endl;
                expr_ref constraint = generate_constraints();
                std::cout << "constraint: " << mk_ismt2_pp(constraint, m, 3)  << std::endl;






                expr_ref spec_with_x_coeffs_and_reused_branches_constrainted = expr_ref(m.mk_and(spec_with_x_coeffs, constraint), m);
                /* m_coeff_solver->push();
                 m_coeff_solver->assert_expr(m.mk_and(spec_with_x_coeffs_and_reused_branches, constraint));
                 if (is_added_heuristic)
                 {
                     expr_ref heuristic = generate_heuristic(is_added_heuristic);
                     m_coeff_solver->push();
                     m_coeff_solver->assert_expr(heuristic);
                     std::cout << "added heuristic: " << mk_ismt2_pp(heuristic, m, 3)  << std::endl;
                 }

                 model_ref mdl_for_coeff;

                 if (m_coeff_solver->check_sat() != lbool::l_true)
                 {

                     if (is_added_heuristic)
                     {
                         is_added_heuristic = false;
                         m_coeff_solver->pop(1);
                         if (m_coeff_solver->check_sat() != lbool::l_true)
                         {
                             std::cout << "WARNING!!!!  search_simultaneously_branches is unsat" << std::endl;

                         }
                     }
                     else
                         std::cout << "WARNING!!!!  search_simultaneously_branches is unsat" << std::endl;
                 }
                 m_coeff_solver->get_model(mdl_for_coeff);
                 m_coeff_solver->pop(1);
                 if (is_added_heuristic)
                     m_coeff_solver->pop(1);
                 //model_ref mdl_for_coeff = m_utils.get_model(expr_ref(m.mk_and(spec_with_x_coeffs, constraint), m));
                 if (!mdl_for_coeff.get())
                 {
                     std::cout << "WARNING!!!!  search_simultaneously_branches is unsat" << std::endl;
                     return;
                 }
                 */



                model_ref mdl_for_coeff =  get_coeff_model_from_slv(m_coeff_solver, spec_with_x_coeffs_and_reused_branches_constrainted, is_added_heuristic ? generate_heuristic(is_added_heuristic) : expr_ref(m));
                if (!mdl_for_coeff)
                {
                    std::cout << "Reused mdl_for_coeff have not found " << std::endl;

                    if (used_branches.size() == 0)
                        return;
                    std::cout << "Remove used branches" << std::endl;
                    // remove used branches
                    fn.remove_branches(used_branches);
                    /*for (unsigned int i : used_branches)
                    {
                        precs.set(i, m.mk_false());
                    }*/
                    (*this)(synth_funs, constraints, mdl_for_x, synth_fun_args, fn, result_fn, is_added_heuristic);
                    return;
                }



                std::cout << "mdl_for_coeff : " << (*mdl_for_coeff) << std::endl;

                add_coeff_to_blacklist(mdl_for_coeff);


                //permutatiom for distinct_invocation.size()

                expr_ref_vector new_branches(m);

                for (unsigned int i = 0; i < distinct_invocation.size(); ++i)
                {
                    func_decl_ref_vector & crnt_coeffs = m_coeff_decl_vec.get(i);
                    expr_ref branch = m_futils.generate_branch(crnt_coeffs, synth_fun_args, synth_funs, mdl_for_coeff);
                    new_branches.push_back(branch);
                    std::cout << "  Branch: "  << mk_ismt2_pp(branch, m) << std::endl;
                }
                expr_ref_vector new_precs = incremental_multiabduction(fn, synth_fun_args, synth_funs, spec, new_branches);
                if (!new_precs.size())
                {

                    std::cout << "  NEW PRECS ARE NOT FOUND"   << std::endl;
                    return;

                }

                result_fn.clear();
                result_fn.add_branches(new_precs, new_branches);

                //what does it deal with unused branches?
                result_fn.unite(fn);

                return;


                //////////////////////// [Unused]
                // after 9
                expr_ref_vector res_single_conjuncts(m);
                collects_single_conjuncts(constraints, synth_funs, mdl_for_x, res_single_conjuncts);

                expr_ref single_conjuncts = m_utils.con_join(res_single_conjuncts);
                std::cout << "single_conjuncts: " << mk_ismt2_pp(single_conjuncts, m, 3)  << std::endl;


                vector<invocation_operands> current_ops;
                collect_invocation_operands(single_conjuncts, synth_funs, current_ops);

                expr_ref_vector precs_temp(m), branches_temp(m);

                for (unsigned int i = 0; i < distinct_invocation.size(); ++i)
                {
                    func_decl_ref_vector & crnt_coeffs = m_coeff_decl_vec.get(i);

                    expr_ref single_conjuncts_with_coeff(m);

                    inv_rwr.rewriter_functions_to_linear_term(crnt_coeffs, synth_funs, single_conjuncts, single_conjuncts_with_coeff);


                    //model_ref mdl = m_utils.get_model(single_conjuncts_with_coeff);
                    //std::cout << "mdl : " << (*mdl) << std::endl;
                    expr_ref single_conjuncts_with_concrete_coeff = m_utils.replace_vars_according_to_model(single_conjuncts_with_coeff, mdl_for_coeff, crnt_coeffs, true);
                    std::cout << "single_conjuncts_with_concrete_coeff : " << mk_ismt2_pp(single_conjuncts_with_concrete_coeff, m, 3)  << std::endl;
                    single_conjuncts_with_concrete_coeff = m_utils.simplify_context(single_conjuncts_with_concrete_coeff);

                    ////
                    func_decl_ref_vector used_vars_prec(m);
                    collect_used_variables(single_conjuncts_with_concrete_coeff, synth_funs, used_vars_prec);

                    std::cout << "used_vars_prec : " << used_vars_prec.size() << std::endl;

                    expr_ref crnt_pre(m);
                    if (used_vars_prec.size() == 0
                            || (used_vars_prec.size() == 1  && synth_fun_args.size() == 1))
                    {
                        crnt_pre = m_utils.replace_vars_decl(single_conjuncts_with_concrete_coeff, used_vars_prec, synth_fun_args);
                    }
                    else
                        crnt_pre = m_abducer.nonlinear_abduce(current_ops, expr_ref(m.mk_true(), m), single_conjuncts_with_concrete_coeff, synth_fun_args);
                    ///



                    if (m_utils.is_unsat(crnt_pre))
                    {
                        std::cout << "prec is unsat : " << mk_ismt2_pp(crnt_pre, m, 0) << std::endl;
                        continue;
                    }
                    expr_ref crnt_branch = m_futils.generate_branch(crnt_coeffs, synth_fun_args, synth_funs, mdl_for_coeff);
                    if (DEBUG_MODE)
                    {
                        std::cout << "-------------" << std::endl;
                        std::cout << mk_ismt2_pp(crnt_pre, m, 0) << "  ==> " << mk_ismt2_pp(crnt_branch, m, 0) << std::endl;
                    }

                    precs_temp.push_back(crnt_pre);
                    branches_temp.push_back(crnt_branch);
                }

                bool is_single_true = true;
                for (unsigned int i = 0; i < precs_temp.size(); ++i)
                {
                    if (m_utils.is_true(precs_temp.get(i)))
                    {
                        if (!is_single_true)
                        {
                            std::cout << "WARNING!!!  Several true-branches exist" << std::endl;
                            return; //several true-branches exist
                        }
                        if (i > 0) precs_temp.set(i, m.mk_not(precs_temp.get(i - 1)));
                        else if (i < precs_temp.size() - 1) precs_temp.set(i, m.mk_not(precs_temp.get(i + 1)));
                        else
                        {
                            std::cout << "WARNING!!!  True-branch is only one" << std::endl;
                        }
                        is_single_true = false;

                    }

                }
                precs.append(precs_temp);
                branches.append(branches_temp);

                //fn.clear();
                //fn.add_branches(precs_temp, branches_temp);
                result_fn.clear();
                result_fn.add_branches(precs_temp, branches_temp);

                //what does it deal with unused branches?
                result_fn.unite(fn);
            }


            void add_coeff_to_blacklist(model_ref mdl_for_coeff)
            {
                //flatting

                func_decl_ref_vector v(m);
                for (unsigned int i = 0; i < m_coeff_decl_vec.size(); ++i)
                {
                    v.append(m_coeff_decl_vec.get(i));

                }
                //////

                m_coeff_solver->push();
                m_coeff_solver->assert_expr(m.mk_not(m_utils.get_logic_model_with_default_value(mdl_for_coeff, v)));
            }

            void collect_distinct_invocation(expr * n, func_decl_ref_vector &   fun_list, model_ref mdl,  vector<app_ref_vector> &l)
            {
                invocation_collector collector(fun_list);
                collector(n);
                obj_hashtable<app > set = collector.get_invocation();
                for (auto it = set.begin(); it != set.end(); it++)
                {
                    app * ap_f = (*it);
                    // search needed equalance group
                    bool is_found = false;
                    for (unsigned int i = 0; i < l.size(); i++)
                    {
                        app *group = l.get(i).get(0);
                        if (is_leq_app(ap_f, group, mdl))
                        {
                            is_found = true;
                            l.get(i).push_back(ap_f);
                            break;
                        }
                    }
                    if (!is_found)
                    {
                        app_ref_vector v(fun_list.get_manager());
                        v.push_back(ap_f);
                        l.push_back(v);
                    }
                    //
                }
            }

            bool is_leq_app(app * a, app * b, model_ref mdl)
            {
                if (a->get_decl() != b->get_decl())
                    return false;
                if (a->get_num_args() != a->get_num_args())
                    return false;

                expr_ref_vector ops_a(m), ops_b(m);
                for (unsigned int i = 0; i < a->get_num_args(); i++)
                {
                    //std::cout << "is equal: " << mk_ismt2_pp((a->get_arg(i)), m, 3)   << mk_ismt2_pp((*mdl)(a->get_arg(i)), m, 3)  << std::endl;
                    //std::cout << "is equal: " << mk_ismt2_pp((b->get_arg(i)), m, 3)   << mk_ismt2_pp((*mdl)(b->get_arg(i)), m, 3)  << std::endl;

                    if (!m_utils.is_unsat(m.mk_not(m.mk_eq((*mdl)(a->get_arg(i)), (*mdl)(b->get_arg(i))))))
                        return false;
                }

                return true;
            }

            expr_ref generate_heuristic_constaraint_coeff(vector<func_decl_ref_vector> &coeff_decls)
            {
                expr_ref_vector v(m);
                for (auto & a : coeff_decls)
                    for (func_decl * fd : a)
                    {
                        expr_ref e(m.mk_const(fd), m);
                        v.push_back(m.mk_or(
                                        m.mk_eq(e, m_arith.mk_int(-1)),
                                        m.mk_eq(e, m_arith.mk_int(0)),
                                        m.mk_eq(e, m_arith.mk_int(1))
                                    ));
                    }
                return m_utils.con_join(v);
            }

            expr_ref generate_heuristic(int num)
            {
                expr_ref_vector v(m);
                if (num == 1)
                {
                    for (unsigned int i = 0; i < m_coeff_decl_vec.size() - 1; ++i)
                    {
                        expr * c0_i = m.mk_const(m_coeff_decl_vec.get(i).get(0));
                        expr * c0_i1 = m.mk_const(m_coeff_decl_vec.get(i + 1).get(0));
                        v.push_back(m.mk_eq(c0_i, c0_i1));

                    }
                }
                else if (num == 2)
                {
                    for (unsigned int i = 0; i < m_coeff_decl_vec.size(); ++i)
                    {
                        expr * c0_i = m.mk_const(m_coeff_decl_vec.get(i).get(0));
                        v.push_back(m.mk_eq(c0_i, m_arith.mk_int(0)));

                    }
                }
                else if (num == 3)
                {
                    for (unsigned int i = 0; i < m_coeff_decl_vec.size(); ++i)
                    {
                        expr * c0_i = m.mk_const(m_coeff_decl_vec.get(i).get(0));
                        v.push_back(m.mk_eq(c0_i, m_arith.mk_int(1)));

                    }
                }
                v.push_back(generate_heuristic_constaraint_coeff(m_coeff_decl_vec));
                return m_utils.con_join(v);
            }









            bool check_abduction_for_comb(vector<unsigned int> &comb, ite_function &fn, func_decl_ref_vector &synth_fun_args,  func_decl_ref_vector & synth_funs, expr_ref & spec, app_ref_vector &invocations, expr_ref_vector & new_precs, expr_ref_vector & new_branches)
            {

                SASSERT(invocations.size() == comb.size());
                DEBUG("check_abduction_for_comb")
                if (new_precs.size() != new_branches.size())
                    return false;

                app2expr_map  term_subst;

                unsigned int k = invocations.size();
                unsigned int n = fn.get_incompact_depth();

                vector<invocation_operands> current_ops;
                collect_invocation_operands(invocations, current_ops);
                //args_t *synth_fun_args = get_args_decl_for_synth_fun(synth_funs.get(0));

                expr_ref_vector preds(m), temp(m);

                for (unsigned int i = 0; i < invocations.size(); ++i)
                {

                    if (comb[i] >= n)
                    {
                        expr_ref concrete_prec =  m_utils.replace_vars_decl(new_precs.get(comb[i] - n), synth_fun_args, current_ops[i]);
                        preds.push_back(concrete_prec);
                        expr_ref concrete_branch =  m_utils.replace_vars_decl(new_branches.get(comb[i] - n), synth_fun_args, current_ops[i]);
                        temp.push_back(concrete_branch);

                        term_subst.insert(invocations[i].get(), concrete_branch);

                    }
                    else
                    {
                        expr_ref concrete_prec =  m_utils.replace_vars_decl(fn.get_precs()[comb[i]].get(), synth_fun_args, current_ops[i]);
                        preds.push_back(concrete_prec);
                        expr_ref concrete_branch =  m_utils.replace_vars_decl(fn.get_branches()[comb[i]].get(), synth_fun_args, current_ops[i]);
                        temp.push_back(concrete_branch);
                        term_subst.insert(invocations[i].get(), concrete_branch);
                    }
                }
                invocations_rewriter inv_rwr(m_cmd, m);
                expr_ref spec_with_branches(m);
                inv_rwr.rewrite_expr(spec, spec_with_branches, term_subst);
                expr_ref premise = m_utils.con_join(preds);
                std::cout << "check_abduction_for_comb " << mk_ismt2_pp(premise, m) << " ==> " << mk_ismt2_pp(spec_with_branches, m) << std::endl;
                return m_utils.implies(premise, spec_with_branches);
            }


            expr_ref_vector  solve_abduction_for_comb(vector<unsigned int> &comb, ite_function &fn, func_decl_ref_vector &synth_fun_args, func_decl_ref_vector & synth_funs, expr_ref & spec, app_ref_vector &invocations, expr_ref_vector & new_branches)
            {
                SASSERT(invocations.size() == comb.size());

                // generate predicate symbols for unknown precs
                func_decl_ref_vector unknown_symbols_preds(m);
                std::string prefix = "R_";

                sort_ref_vector parameters(m);
                for (unsigned int i = 0; i < synth_fun_args.size(); ++i)
                {
                    parameters.push_back(m_arith.mk_int());
                }

                for (unsigned int i = 0; i < new_branches.size(); ++i)
                {
                    func_decl_ref pred(m.mk_func_decl(symbol((prefix + std::to_string(i)).c_str()), parameters.size(), parameters.c_ptr(), m.mk_bool_sort()),  m);
                    unknown_symbols_preds.push_back(pred);
                }

                //

                app2expr_map  term_subst;
                vector<invocation_operands> current_ops;
                collect_invocation_operands(invocations, current_ops);

                //args_t *synth_fun_args = get_args_decl_for_synth_fun(synth_funs.get(0));

                expr_ref_vector unknown_pred(m);
                unsigned int n = fn.get_incompact_depth();
                expr_ref_vector known_pred(m), temp(m);
                for (unsigned int i = 0; i < invocations.size(); ++i)
                {
                    //std::cout << "comb[i] " << comb[i] << std::endl;
                    //std::cout << "inv[i] " << mk_ismt2_pp(invocations[i].get(), m)  << std::endl;
                    if (comb[i] >= n)
                    {
                        func_decl *r = unknown_symbols_preds.get(comb[i] - n);
                        unknown_pred.push_back(m.mk_app(r, current_ops[i].size(), current_ops[i].c_ptr()));
                        //unknown_pred.push_back(current_ops[i]);
                        expr_ref concrete_branch =  m_utils.replace_vars_decl(new_branches.get(comb[i] - n), synth_fun_args, current_ops[i]);
                        temp.push_back(concrete_branch);
                        term_subst.insert(invocations[i].get(), concrete_branch);

                    }
                    else
                    {
                        expr_ref concrete_prec =  m_utils.replace_vars_decl(fn.get_precs()[comb[i]].get(), synth_fun_args, current_ops[i]);
                        known_pred.push_back(concrete_prec);
                        expr_ref concrete_branch =  m_utils.replace_vars_decl(fn.get_branches()[comb[i]].get(), synth_fun_args, current_ops[i]);
                        temp.push_back(concrete_branch);
                        term_subst.insert(invocations[i].get(), concrete_branch);
                    }

                }

                invocations_rewriter inv_rwr(m_cmd, m);
                expr_ref spec_with_branches(m);
                inv_rwr.rewrite_expr(spec, spec_with_branches, term_subst);
                // std::cout << "spec_with_branches " << mk_ismt2_pp(spec_with_branches, m) << std::endl;
                //expr_ref res = m_abducer.nonlinear_abduce(unknown_pred, m_utils.con_join(known_pred), spec_with_branches, synth_fun_args);

                expr_ref_vector unordered_res(m);
                decl2expr_map map;
                bool r = m_abducer.multi_abduce(unknown_pred, m_utils.con_join(known_pred), spec_with_branches, synth_fun_args, unordered_res, map);
                if (!r)
                {
                    return expr_ref_vector(m);
                }
                expr_ref_vector ordered_res(m);

                for (unsigned int i = 0; i < unknown_symbols_preds.size(); ++i)
                {
                    ordered_res.push_back(map[unknown_symbols_preds.get(i)]);

                }

                //[+] HEURISTIC R_2 = not(R_1)
                bool is_single_true = true;
                for (unsigned int i = 0; i < ordered_res.size(); ++i)
                {
                    if (m_utils.is_true(ordered_res.get(i)))
                    {
                        if (!is_single_true)
                        {
                            std::cout << "WARNING!!!  Several true-branches exist" << std::endl;
                            // return; //several true-branches exist
                        }
                        if (i > 0) ordered_res.set(i, m.mk_not(ordered_res.get(i - 1)));
                        else if (i < ordered_res.size() - 1) ordered_res.set(i, m.mk_not(ordered_res.get(i + 1)));
                        else
                        {
                            std::cout << "WARNING!!!  True-branch is only one" << std::endl;
                        }
                        is_single_true = false;

                    }
                }
                //[-]
                return ordered_res;
            }



            expr_ref_vector incremental_multiabduction(ite_function & fn, func_decl_ref_vector & synth_fun_args, func_decl_ref_vector & synth_funs, expr_ref & spec, expr_ref_vector & new_branches)
            {
                //args_t *synth_fun_args = get_args_decl_for_synth_fun(synth_funs.get(0));

                app_ref_vector invocations(m);
                collect_invocation(spec, synth_funs, invocations);

                unsigned int n2 =  new_branches.size();
                unsigned int k = invocations.size();
                unsigned int n = fn.get_incompact_depth() ;


                std::cout << "k = " << k << "; n = " << n << std::endl;
                /* if (n == 0)
                 {
                     vector<unsigned int> permutation(k - n2, n);
                     for (unsigned int i = 0; i < n2; ++i)
                     {
                         permutation.push_back(i + n);
                     }
                     DEBUG("n == 0")
                     print_vector(permutation);
                     return solve_abduction_for_comb(permutation, fn, synth_fun_args, synth_funs, spec, invocations, new_branches);
                 }*/


                //increase "complexity" multiabduction
                // i - number of unknown predicates

                // for (int i = 1; i <= k; ++i)
                {

                    std::cout << "k   "   << std::endl;
                    generator_combination_with_repetiton comb(k - n2, n);
                    while (comb.do_next())
                    {

                        //print_vector(comb.get_next());
                        vector<unsigned int> permutation = comb.get_next();
                        for (int i = 0; i < n2; ++i)
                        {
                            permutation.push_back(i + n);
                        }

                        //permutation.resize(k, n);
                        std::sort(permutation.begin(), permutation.end());
                        do
                        {
                            //todo
                            print_vector(permutation);
                            expr_ref_vector potential_precs = solve_abduction_for_comb(permutation, fn, synth_fun_args, synth_funs, spec, invocations, new_branches);
                            if (check_all_abductions(fn, synth_fun_args, synth_funs, spec, invocations, potential_precs, new_branches))
                            {
                                std::cout << "!!! a prec is FOUND (incremental abduction)" << std::endl;
                                return potential_precs;
                            }
                        }
                        while (std::next_permutation(permutation.begin(), permutation.end()));
                        std::cout << "---"  << std::endl;
                    }
                }
                std::cout << "------"  << std::endl;
                std::cout << "All abduction problems have been enumerated"  << std::endl;
                //[-]


                return expr_ref_vector(m);
            }






            bool check_all_abductions(ite_function & fn, func_decl_ref_vector & synth_fun_args, func_decl_ref_vector & synth_funs, expr_ref & spec, app_ref_vector & invocations, expr_ref_vector & new_precs, expr_ref_vector & new_branches)
            {
                unsigned int k = invocations.size();
                unsigned int n = fn.get_incompact_depth() + new_branches.size();

                //todo
                for (int i = 0; i < new_precs.size(); ++i)
                {
                    if (m_utils.is_unsat(new_precs.get(i)))
                    {
                        std::cout << "!!! NEW ONE PREC IS UNSAT" << std::endl;
                        return false;
                    }
                }

                DEBUG("check_all_abductions")
                // for (int i = 1; i <= k; ++i)
                {
                    generator_combination_with_repetiton comb(k, n);
                    while (comb.do_next())
                    {
                        vector<unsigned int> permutation = comb.get_next();
                        //permutation.resize(k, n);
                        std::sort(permutation.begin(), permutation.end());
                        do
                        {
                            //todo
                            print_vector(permutation);
                            if (!check_abduction_for_comb(permutation, fn, synth_fun_args, synth_funs, spec, invocations, new_precs, new_branches))
                            {
                                std::cout << "!!! ABDUCTION PROBLEM IS UNSAT" << std::endl;
                                return false;

                            }

                        }
                        while (std::next_permutation(permutation.begin(), permutation.end()));

                    }


                }
                return true;
            }

    };
}

#endif // SEARCH_SIMULTANEOUSLY_BRANCHES_H
