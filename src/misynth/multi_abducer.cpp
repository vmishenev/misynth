#include "ast/ast_pp.h"
#include "ast/rewriter/rewriter.h"
#include "ast/rewriter/rewriter_def.h"
#include "ast/rewriter/th_rewriter.h"
#include "util/symbol.h"
#include "muz/spacer/spacer_util.h"
#include "qe/qe_mbp.h"

#include "ast/used_vars.h"
#include "multi_abducer.h"
#include "qe/qe.h"
#include "qe/qe_tactic.h"
#include <set>
#include <ctime>
#include <iostream>

#define DEBUG_ABDUCE m_params.debug_abduce()
#define VERBOSE_ABDUCE true
#define DEBUG(x) std::cout<< x << std::endl;

namespace misynth
{

    multi_abducer::multi_abducer(cmd_context &cmd_ctx, ast_manager &m) : m_cmd(cmd_ctx), m(m), m_arith(m), m_utils(cmd_ctx, m)
    {
    }
    void multi_abducer::generate_fresh_constant(const func_decl_ref_vector &preds, const vector<vector<func_decl_ref_vector>> &decl_args_all, vector<vector<func_decl_ref_vector>> &fresh_constant_all)
    {
        std::string coeff_prefix = "m";
        std::string separator = "_";
        func_decl_ref_vector m_coeff_decl_vec(m);
        for (unsigned pred_ind = 0; pred_ind < decl_args_all.size(); ++pred_ind)
        {

            const vector<func_decl_ref_vector> &decl_args = decl_args_all.get(pred_ind);

            fresh_constant_all.push_back(vector<func_decl_ref_vector>());
            vector<func_decl_ref_vector> &fresh_constant = fresh_constant_all.back();

            for (unsigned i = 0; i < decl_args.size(); ++i)
            {
                const func_decl_ref_vector &invocation_decl = decl_args.get(i);
                func_decl_ref_vector current_fresh_constant_for_one_invocation(m);
                for (unsigned j = 0; j < invocation_decl.size(); ++j)
                {
                    //sort * range = m_arith.is_int(invocation.get(0)) ? m_arith.mk_int() : m_arith.mk_real();
                    sort * range = invocation_decl.get(0)->get_range();
                    func_decl_ref fresh_const(
                        m.mk_const_decl(coeff_prefix + std::to_string(i) + separator + std::to_string(j) + separator + preds.get(pred_ind)->get_name().str(),
                                        range), m);
                    current_fresh_constant_for_one_invocation.push_back(fresh_const);
                    m_coeff_decl_vec.push_back(fresh_const);
                }
                fresh_constant.push_back(current_fresh_constant_for_one_invocation);

            }
        }
    }

    void multi_abducer::generate_fresh_constant(vector<func_decl_ref_vector> &fresh_constant, vector<func_decl_ref_vector> &decl_args)
    {
        std::string coeff_prefix = "m";
        std::string separator = "_";
        func_decl_ref_vector m_coeff_decl_vec(m);

        for (unsigned i = 0; i < decl_args.size(); ++i)
        {
            func_decl_ref_vector &invocation_decl = decl_args.get(i);
            func_decl_ref_vector current_fresh_constant_for_one_invocation(m);
            for (unsigned j = 0; j < invocation_decl.size(); ++j)
            {
                //sort * range = m_arith.is_int(invocation.get(0)) ? m_arith.mk_int() : m_arith.mk_real();
                sort * range = invocation_decl.get(0)->get_range();
                func_decl_ref fresh_const(
                    m.mk_const_decl(coeff_prefix + std::to_string(i) + separator + std::to_string(j),
                                    range), m);
                current_fresh_constant_for_one_invocation.push_back(fresh_const);
                m_coeff_decl_vec.push_back(fresh_const);
            }
            fresh_constant.push_back(current_fresh_constant_for_one_invocation);

        }
    }
    /*
     * all preds are from the same pattern (template)
     * */
    bool multi_abducer::multi_abduce(expr_ref_vector &unknown_preds, expr_ref premise,
                                     expr_ref conclusion, func_decl_ref_vector &pattern,
                                     expr_ref_vector &res,  decl2expr_map &res_map)
    {
        DEBUG("MULTI ABDUCE" << mk_ismt2_pp(m_utils.con_join(unknown_preds), m) << "; " << mk_ismt2_pp(premise, m) << " ==> " << mk_ismt2_pp(conclusion, m))
        vector<vector<expr_ref_vector>> inv_args_vec; // for storing all inv arguments for each a predicator
        func_decl_ref_vector preds(m);
        obj_map<func_decl, unsigned>  preds2arguments;//maps preds to invocation arguments


        for (expr *e : unknown_preds)
        {
            if (is_app(e))
            {
                app* a = to_app(e);
                expr_ref_vector ops(m);
                ops.append(a->get_num_args(), a->get_args());
                //***OUTPUT***
                if (DEBUG_ABDUCE) {
                    std::cout<< "fill "<<  mk_ismt2_pp(a, m) << std::endl;
                  for(expr * e: ops) {
                      std::cout<< mk_ismt2_pp(e, m) << std::endl;

                    }
                }
                //***end***

                auto it = preds2arguments.find_iterator(a->get_decl());
                if (it == preds2arguments.end())
                {
                    vector<expr_ref_vector> v;
                    v.push_back(ops);
                    inv_args_vec.push_back(v);

                    preds2arguments.insert(a->get_decl(), inv_args_vec.size() - 1);
                    preds.push_back(a->get_decl());
                }
                else
                {
                    inv_args_vec[it->m_value].push_back(ops);
                }
            }
            else
            {
                std::cout << "ERROR! MultiAbduce try to treat no pred" << std::endl;
            }
        }

        if (pattern.empty())
        {
            func_decl * fd = preds.get(0);
            unsigned num = fd->get_arity();
            for (unsigned i = 0; i < num; ++i)
            {
                pattern.push_back(m.mk_const_decl("x_" + std::to_string(num), m_arith.mk_int()));
            }
        }

        vector<vector<func_decl_ref_vector>> decl_args;
        expr_ref flat_premise = to_flat_multi(preds, inv_args_vec, decl_args);

        func_decl_ref_vector all_vars(m);
        for (auto &a : decl_args)
            for (auto &aa : a)
            {

                all_vars.append(aa);
            }

        expr_ref flat_conclusion(m.mk_implies(flat_premise, conclusion), m);
        //expr_ref flat_conclusion(m.mk_and(flat_premise, conclusion), m);
        if (DEBUG_ABDUCE)
            std::cout << "Abduction flat_conclusion formula: " << mk_ismt2_pp(flat_conclusion, m, 3) << std::endl;

        expr_ref abduce_conclusion = simple_abduce(premise, flat_conclusion, all_vars);
        abduce_conclusion = m_utils.simplify_context(abduce_conclusion);
        //if (DEBUG_ABDUCE)
        std::cout << "Abduced flat_conclusion formula: " << mk_ismt2_pp(abduce_conclusion, m, 3) << std::endl;

        /// generate fresh constant \/ m_ki=xx_ij, k=0.. invocation number, i - component index
        ///
        /// decl_args.size() is invocation number
        ///


        vector<vector<func_decl_ref_vector>> fresh_constant;
        generate_fresh_constant(preds, decl_args, fresh_constant);

        expr_ref fresh_consts_equals_inv_args(m.mk_true(), m);
        /*
         * Code below generates /\ \/ x_ij = m_ik for R_i(x_ij)
         * */

        for (unsigned pred_ind = 0; pred_ind < decl_args.size(); ++pred_ind)
        {
            vector<func_decl_ref_vector>& decl_args_pred = decl_args.get(pred_ind);
            vector<func_decl_ref_vector>& fresh_constant_pred = fresh_constant.get(pred_ind);

            ///////////
            for (unsigned i = 0; i < decl_args_pred.size(); ++i)
            {
                auto& crnt_decl_args = decl_args_pred.get(i);
                expr_ref_vector crnt_fresh_consts_equals_inv_args(m);
                for (unsigned j = 0; j < fresh_constant_pred.size(); ++j)
                {

                    crnt_fresh_consts_equals_inv_args.push_back(m_utils.mk_eq(crnt_decl_args, fresh_constant_pred.get(j)));
                }
                fresh_consts_equals_inv_args = m.mk_and(fresh_consts_equals_inv_args, m_utils.dis_join(crnt_fresh_consts_equals_inv_args));
            }
            ///////
        }
        /// [-] generate fresh constant

        /// [+] quantifier vars
        ///
        /*decl_collector decls(m);
        decls.visit(abduce_conclusion);
        func_decl_ref_vector quantifier_vars(m);
        quantifier_vars.append(decls.get_num_decls(), decls.get_func_decls().c_ptr());
        */
        expr_ref implic(m_utils.universal_quantified(expr_ref(m.mk_implies(fresh_consts_equals_inv_args, abduce_conclusion), m), all_vars), m);

        //if (DEBUG_ABDUCE)
        std::cout << "INIT SOLN  abduction formula: " << mk_ismt2_pp(implic, m, 3) << std::endl;

        /// [-] quantifier vars
        ///

        params_ref params;
        ref<solver> slv = m_cmd.get_solver_factory()(m, params, false, true, false, symbol::null);

        slv->push();
        slv->assert_expr(implic);
        slv->push();
        slv->assert_expr(premise); // IMPORTANT TODO
        lbool r = slv->check_sat();
        //std::cout << "INIT SOLN  abduction formula result : " << r << std::endl;
        // decl2expr_map soln;
        expr_ref_vector soln_vec(m);
        if (r == lbool::l_true)
        {
            model_ref mdl;
            slv->get_model(mdl);
            expr_ref init_soln(m);
            // estimate pattern
            if (DEBUG_ABDUCE)
                std::cout << "INIT SOLN  result mdl: " << *mdl << std::endl;
            for (unsigned pred_ind = 0; pred_ind < decl_args.size(); ++pred_ind)
            {

                /*
                 *INIT SOLN
                 * R_i = \/_j x_i=Mdl(m_ij)
                 * */
                expr_ref initial_soln = get_soln_according_to_model(mdl, fresh_constant.get(pred_ind), pattern);
                res_map.insert(preds.get(pred_ind), initial_soln);
                DEBUG("INIT SOLN: "  << (preds.get(pred_ind)->get_name().str()) << " == " << mk_ismt2_pp(res_map[preds.get(pred_ind)], m))

                soln_vec.push_back(initial_soln);
                if (DEBUG_ABDUCE)
                    std::cout << "INIT SOLN  result formula: "  << (preds.get(pred_ind)->get_name().str()) << " " << mk_ismt2_pp(initial_soln, m, 3) << std::endl;
            }

            cart_decomp(implic, decl_args, fresh_constant, preds, pattern, abduce_conclusion, res, res_map);
            //res_map = soln;
            return true;
            //return iso_decomp(implic, res, abduce_conclusion, inv_args, fresh_constant, pattern, decl_args);

        }





        return false;
    }

    void multi_abducer::cart_decomp(expr_ref implic,
                                    vector<vector<func_decl_ref_vector>> &decl_args, vector<vector<func_decl_ref_vector>> &fresh_constant,
                                    func_decl_ref_vector &preds,
                                    func_decl_ref_vector &pattern, expr_ref conclusion, expr_ref_vector &res, decl2expr_map &soln)
    {
        for (unsigned pred_ind = 0; pred_ind < decl_args.size(); ++pred_ind)
        {
            expr_ref_vector concrete_preds(m);
            for (unsigned k = 0; k < decl_args.size(); ++k) // for every  predicate except pred_ind
            {
                if (k == pred_ind) continue;
                vector<func_decl_ref_vector> &occurrencies  = decl_args.get(k);
                for (unsigned j = 0; j < occurrencies.size(); ++j)   // for every occurrency
                {
                    expr_ref concrete_pred = m_utils.replace_vars_decl(soln[preds.get(k)], pattern, occurrencies.get(j));
                    concrete_preds.push_back(concrete_pred);
                }


            }

            expr_ref conj_all_preds = m_utils.con_join(concrete_preds); // line 8
            DEBUG("line 8 before (conj all preds except " << preds.get(pred_ind)->get_name() << "): "   << mk_ismt2_pp(conj_all_preds, m, 3))

            //TODO
            //ATTENTION
            //WHAT ARE VARIABLES need eliminate

            func_decl_ref_vector all_vars_pred_ind(m);
            vector<func_decl_ref_vector> &occurrencies  = decl_args.get(pred_ind);
            for (auto&& it : occurrencies)
            {
                all_vars_pred_ind.append(it);
                m_utils.print_sorted_var_list(std::cout, it);
            }
            std::cout << std::endl;
            DEBUG("Abduction problem for cart. decomp: "   << mk_ismt2_pp(m.mk_implies(conj_all_preds, conclusion), m))
            expr_ref phi_i = simple_abduce(conj_all_preds, conclusion, all_vars_pred_ind);
            phi_i = m_utils.simplify_context(phi_i);
            DEBUG("line 8 phi_i: "   << mk_ismt2_pp(phi_i, m, 3))
            expr_ref init_soln(soln[preds.get(pred_ind)], m);


            expr_ref res_pred = iso_decomp(implic, init_soln, phi_i, fresh_constant.get(pred_ind), pattern, decl_args.get(pred_ind));
            res.push_back(res_pred);
            soln.insert(preds.get(pred_ind), res_pred);
            DEBUG(preds.get(pred_ind)->get_name()  << " := "  << mk_ismt2_pp(res_pred, m))
        }
    }
    expr_ref multi_abducer::nonlinear_abduce(vector<expr_ref_vector> &inv_args, expr_ref premise, expr_ref conclusion, func_decl_ref_vector & pattern)
    {
        SASSERT(inv_args.size( ) > 0);
        //[+] debug output
        std::cout << "Abduction (nonlinear_abduce) ";
        std::cout << mk_ismt2_pp(premise, m, 3) << " ==>"  << mk_ismt2_pp(conclusion, m, 3) << std::endl;
        expr_ref_vector unknown_pred(m);

        sort_ref_vector parameters(m);
        for (unsigned int i = 0; i < inv_args.get(0).size(); ++i)
        {
            parameters.push_back(m_arith.mk_int());
        }
        func_decl_ref pred(m.mk_func_decl(symbol("R"), parameters.size(), parameters.c_ptr(), m.mk_bool_sort()),  m);
        for (expr_ref_vector &a : inv_args)
        {
            unknown_pred.push_back(m.mk_app(pred, a.size(), a.c_ptr()));

        }
        std::cout << mk_ismt2_pp(m_utils.con_join(unknown_pred), m, 3);

        //[-] debug output

        //TODO: check inv_args.size>1
        vector<func_decl_ref_vector> decl_args;
        expr_ref flat_premise = to_flat(inv_args, decl_args);
        func_decl_ref_vector all_vars(m);
        for (auto &a : decl_args)
        {
            all_vars.append(a);
        }
        expr_ref flat_conclusion(m.mk_and(flat_premise, conclusion), m);
        //expr_ref flat_conclusion(m.mk_and(flat_premise, conclusion), m);
        if (DEBUG_ABDUCE)
            std::cout << "Abduction flat_conclusion formula: " << mk_ismt2_pp(flat_conclusion, m, 3) << std::endl;

        expr_ref abduce_conclusion = simple_abduce_exist(premise, flat_conclusion, all_vars);
        abduce_conclusion = m_utils.simplify_context(abduce_conclusion);
        if (DEBUG_ABDUCE)
            std::cout << "Abduced flat_conclusion formula: " << mk_ismt2_pp(abduce_conclusion, m, 3) << std::endl;

        /// generate fresh constant \/ m_ki=xx_ij, k=0.. invocation number, i - component index
        ///
        /// decl_args.size() is invocation number
        ///


        vector<func_decl_ref_vector> fresh_constant;
        generate_fresh_constant(fresh_constant, decl_args);

        expr_ref fresh_consts_equals_inv_args(m.mk_true(), m);
        for (unsigned i = 0; i < decl_args.size(); ++i)
        {
            auto& crnt_decl_args = decl_args.get(i);
            expr_ref_vector crnt_fresh_consts_equals_inv_args(m);
            for (unsigned j = 0; j < fresh_constant.size(); ++j)
            {

                crnt_fresh_consts_equals_inv_args.push_back(m_utils.mk_eq(crnt_decl_args, fresh_constant.get(j)));
            }
            fresh_consts_equals_inv_args = m.mk_and(fresh_consts_equals_inv_args, m_utils.dis_join(crnt_fresh_consts_equals_inv_args));
        }
        /// [-] generate fresh constant

        /// [+] quantifier vars
        ///
        /*decl_collector decls(m);
        decls.visit(abduce_conclusion);
        func_decl_ref_vector quantifier_vars(m);
        quantifier_vars.append(decls.get_num_decls(), decls.get_func_decls().c_ptr());
        */
        expr_ref implic(m_utils.universal_quantified(expr_ref(m.mk_implies(fresh_consts_equals_inv_args, abduce_conclusion), m), all_vars), m);

        //if (DEBUG_ABDUCE)
        std::cout << "INIT SOLN  abduction formula: " << mk_ismt2_pp(implic, m, 3) << std::endl;

        /// [-] quantifier vars
        ///



        params_ref params;
        ref<solver> slv = m_cmd.get_solver_factory()(m, params, false, true, false, symbol::null);

        slv->push();
        slv->assert_expr(implic);
        slv->push();
        slv->assert_expr(premise);
        lbool r = slv->check_sat();
        //std::cout << "INIT SOLN  abduction formula result : " << r << std::endl;

        if (r == lbool::l_true)
        {
            model_ref mdl;
            slv->get_model(mdl);
            expr_ref init_soln(m);
            // estimate pattern
            if (DEBUG_ABDUCE)
                std::cout << "INIT SOLN  result mdl: " << *mdl << std::endl;

            expr_ref res = get_soln_according_to_model(mdl, fresh_constant, pattern);
            if (DEBUG_ABDUCE)
                std::cout << "INIT SOLN  result formula: " << mk_ismt2_pp(res, m, 3) << std::endl;

            if (m_params.mbp_abduce())
                return iso_decomp_mbp(implic, res, abduce_conclusion, fresh_constant, pattern, decl_args);
            else
                return iso_decomp(implic, res, abduce_conclusion, fresh_constant, pattern, decl_args);

        }

        return expr_ref(m.mk_false(), m);
    }

    expr_ref multi_abducer::to_flat_multi(const func_decl_ref_vector & preds, const vector<vector<expr_ref_vector>> &inv_args_all, vector<vector<func_decl_ref_vector>> &new_decl_args_all)
    {
        std::string coeff_prefix = "xx";
        std::string separator = "_";


        expr_ref_vector asserts(m);
        func_decl_ref_vector m_coeff_decl_vec(m);
        for (unsigned pred_ind = 0; pred_ind < inv_args_all.size(); ++pred_ind)
        {
            const vector<expr_ref_vector> &inv_args = inv_args_all.get(pred_ind);

            new_decl_args_all.push_back(vector<func_decl_ref_vector>());
            vector<func_decl_ref_vector> &new_decl_args = new_decl_args_all.back();

            for (unsigned i = 0; i < inv_args.size(); ++i)
            {
                const expr_ref_vector &invocation = inv_args.get(i);
                func_decl_ref_vector current_new_vars_for_one_invocation(m);
                for (unsigned j = 0; j < invocation.size(); ++j)
                {
                    //WARNIN!!! sort * range = m_arith.is_int(invocation.get(0)) ? m_arith.mk_int() : m_arith.mk_real();
                    sort * range =   m_arith.mk_int();
                    func_decl_ref coef(
                        m.mk_const_decl(coeff_prefix + std::to_string(i) + separator + std::to_string(j) + separator + preds.get(pred_ind)->get_name().str(),
                                        range), m);
                    current_new_vars_for_one_invocation.push_back(coef);
                    m_coeff_decl_vec.push_back(coef);
                }
                new_decl_args.push_back(current_new_vars_for_one_invocation);
                asserts.push_back(m_utils.mk_eq(current_new_vars_for_one_invocation, invocation));
            }
        }
        return m_utils.con_join(asserts);

    }

    expr_ref multi_abducer::to_flat(vector<expr_ref_vector> &inv_args, vector<func_decl_ref_vector> &new_decl_args)
    {
        std::string coeff_prefix = "xx";
        std::string separator = "_";


        expr_ref_vector asserts(m);
        func_decl_ref_vector m_coeff_decl_vec(m);

        for (unsigned i = 0; i < inv_args.size(); ++i)
        {
            expr_ref_vector &invocation = inv_args.get(i);
            func_decl_ref_vector current_new_vars_for_one_invocation(m);
            for (unsigned j = 0; j < invocation.size(); ++j)
            {
                //WARNIN!!! sort * range = m_arith.is_int(invocation.get(0)) ? m_arith.mk_int() : m_arith.mk_real();
                sort * range =   m_arith.mk_int();
                func_decl_ref coef(
                    m.mk_const_decl(coeff_prefix + std::to_string(i) + separator + std::to_string(j),
                                    range), m);
                current_new_vars_for_one_invocation.push_back(coef);
                m_coeff_decl_vec.push_back(coef);
            }
            new_decl_args.push_back(current_new_vars_for_one_invocation);
            asserts.push_back(m_utils.mk_eq(current_new_vars_for_one_invocation, invocation));
        }
        return m_utils.con_join(asserts);

    }


    expr_ref  multi_abducer::get_soln_according_to_model(model_ref mdl, vector<func_decl_ref_vector> &fresh_constant, func_decl_ref_vector & pattern)
    {

        expr_ref_vector exprs(m);

        for (unsigned i = 0; i < fresh_constant.size(); ++i)
        {
            //expr_ref_vector &invocation = inv_args.get(i);
            expr_ref crnt_expr(m.mk_true(), m);
            for (unsigned j = 0; j < pattern.size(); ++j)
            {
                //expr_ref value((*mdl)(invocation.get(j)), m);
                expr_ref value((*mdl)(m.mk_const(fresh_constant.get(i).get(j))), m);

                crnt_expr = m.mk_and(crnt_expr, m.mk_eq(m.mk_const(pattern.get(j)), value));
            }
            exprs.push_back(crnt_expr);
        }

        return m_utils.dis_join(exprs);
    }

    /*
     * generate /\(\/_j x_i=m_ij \/phi)
     * */
    expr_ref multi_abducer::build_conclusion_model(expr_ref phi, vector<func_decl_ref_vector> &decl_args, vector<func_decl_ref_vector> &fresh_constant, expr_ref abduce_conclusion, func_decl_ref_vector & pattern)   //phi_M
    {
        func_decl_ref_vector all_vars(m);
        expr_ref fresh_consts_equals_inv_args(m.mk_true(), m);
        for (unsigned i = 0; i < decl_args.size(); ++i)
        {
            auto& crnt_decl_args = decl_args.get(i);
            all_vars.append(crnt_decl_args);
            expr_ref_vector crnt_fresh_consts_equals_inv_args(m);
            // [] add phi
            crnt_fresh_consts_equals_inv_args.push_back(m_utils.replace_vars_decl(phi, pattern, crnt_decl_args));
            //
            for (unsigned j = 0; j < fresh_constant.size(); ++j)
            {

                crnt_fresh_consts_equals_inv_args.push_back(m_utils.mk_eq(crnt_decl_args, fresh_constant.get(j)));
            }
            fresh_consts_equals_inv_args = m.mk_and(fresh_consts_equals_inv_args, m_utils.dis_join(crnt_fresh_consts_equals_inv_args));
        }
        /// [-] generate fresh constant


        expr_ref implic(m_utils.universal_quantified(expr_ref(m.mk_implies(fresh_consts_equals_inv_args, abduce_conclusion), m), all_vars), m);

        return implic;
    }

    expr_ref  multi_abducer::iso_decomp(expr_ref conclusion_model/*unused*/, expr_ref init_soln, expr_ref conclusion, vector<func_decl_ref_vector> &fresh_constant, func_decl_ref_vector & pattern, vector<func_decl_ref_vector> &decl_args)
    {
        unsigned int num_iter = 0;

        expr_ref phi = init_soln;
        while (true)
        {
            if (VERBOSE_ABDUCE)
                std::cout << "------ iso_decomp iteration #" << num_iter << "  ------ " << std::endl;

            //   /\not phi[m_ij/x_i]

            expr_ref conclusion_m = build_conclusion_model(phi, decl_args, fresh_constant, conclusion, pattern);
            expr_ref not_phi_replaced(conclusion_m, m);
            for (unsigned i = 0; i < fresh_constant.size(); ++i)
            {
                expr_ref replaced = m_utils.replace_vars_decl(phi, pattern, fresh_constant.get(i));
                not_phi_replaced = m.mk_and(not_phi_replaced, m.mk_not(replaced));
            }
            /////////

            if (DEBUG_ABDUCE)
                std::cout << "iso_decomp  not_phi_replaced formula: " << mk_ismt2_pp(not_phi_replaced, m, 3) << std::endl;

            params_ref params;
            ref<solver> slv = m_cmd.get_solver_factory()(m, params, false, true, false, symbol::null);

            slv->push();
            slv->assert_expr(not_phi_replaced);
            lbool r = slv->check_sat();
            if (VERBOSE_ABDUCE)
                std::cout << "got model iso_decomp "  << r << std::endl;

            if (r != lbool::l_true)
            {
                max_iter_iso_mor = std::max(max_iter_iso_mor, num_iter);
                return phi;
            }
            if (num_iter >= m_params.theshold_iso_decomp())
            {
                if (VERBOSE_ABDUCE)
                    std::cout << "!!! ISO_DECOMP_ITERS_TRESHOLD " << std::endl;
                return expr_ref(m.mk_false(), m);
            }
            model_ref mdl;
            slv->get_model(mdl);
            slv->pop(1);
            expr_ref res = get_soln_according_to_model(mdl, fresh_constant, pattern);
            phi = m.mk_or(phi, res);
            if (DEBUG_ABDUCE)
                std::cout << "new phi(line 23) "  << mk_ismt2_pp(phi, m, 3) << std::endl;

            expr_ref_vector phi_i(m);
            for (unsigned i = 0; i < decl_args.size(); ++i)
            {
                phi_i.push_back(m_utils.replace_vars_decl(phi, pattern, decl_args.get(i)));
            }

            for (unsigned i = 0; i < decl_args.size(); ++i)
            {
                expr_ref phi_except_i(m.mk_true(), m);
                for (unsigned j = 0; j < decl_args.size(); ++j)
                {
                    if (j != i)
                        phi_except_i  = m.mk_and(phi_except_i, phi_i.get(j));
                }
                phi_except_i = m_utils.simplify_context(phi_except_i);
                if (DEBUG_ABDUCE)
                    std::cout << "phi_except_i " << i <<  mk_ismt2_pp(phi_except_i, m, 3) << std::endl;
                //expr_ref old_phi_i(phi_i[i].get(), m);

                phi_i[i] = simple_abduce(phi_except_i, conclusion, decl_args.get(i));
                if (VERBOSE_ABDUCE)
                {
                    //std::cout << "check either old phi_i implies abduced phi_i: " << m_utils.implies(old_phi_i, phi_i[i].get()) << std::endl;
                    //std::cout << m_utils.simplify_context(old_phi_i) << " ==>" << m_utils.simplify_context(expr_ref(phi_i[i].get(), m)) << std::endl;
                }
            }

            phi = m.mk_true();
            for (unsigned i = 0; i < decl_args.size(); ++i)
            {
                phi = m.mk_and(phi, m_utils.replace_vars_decl(expr_ref(phi_i[i].get(), m), decl_args.get(i), pattern));
            }

            //if (VERBOSE_ABDUCE)
            //    std::cout << "crnt phi (line after 27) "   << mk_ismt2_pp(phi, m, 3) << std::endl;
            phi = m_utils.simplify_context(phi);

            clock_t start = clock();
            if (VERBOSE_ABDUCE)
            {
                std::cout << "crnt phi-simplified (line after 27) "   << mk_ismt2_pp(phi, m, 3) << std::endl;
                std::cout << "time :" << ((double)(clock() - start) / CLOCKS_PER_SEC) << std::endl;;
            }
            num_iter++;
        }
        return expr_ref(m.mk_false(), m);
    }



    expr_ref  multi_abducer::iso_decomp_mbp(expr_ref conclusion_model, expr_ref init_soln, expr_ref conclusion, vector<func_decl_ref_vector> &fresh_constant, func_decl_ref_vector & pattern, vector<func_decl_ref_vector> &decl_args)
    {
        unsigned int num_iter = 0;

        expr_ref phi = init_soln;
        while (true)
        {
            if (VERBOSE_ABDUCE)
                std::cout << "------ iso_decomp iteration #" << num_iter << "  ------ " << std::endl;

            //   /\not phi[m_ij/x_i]
            expr_ref not_phi_replaced(conclusion_model, m);
            for (unsigned i = 0; i < fresh_constant.size(); ++i)
            {
                expr_ref replaced = m_utils.replace_vars_decl(phi, pattern, fresh_constant.get(i));
                not_phi_replaced = m.mk_and(not_phi_replaced, m.mk_not(replaced));
            }
            /////////

            if (DEBUG_ABDUCE)
                std::cout << "iso_decomp  not_phi_replaced formula: " << mk_ismt2_pp(not_phi_replaced, m, 3) << std::endl;

            params_ref params;
            ref<solver> slv = m_cmd.get_solver_factory()(m, params, false, true, false, symbol::null);

            slv->push();
            slv->assert_expr(not_phi_replaced);
            lbool r = slv->check_sat();
            if (VERBOSE_ABDUCE)
                std::cout << "got model iso_decomp "  << r << std::endl;

            if (r != lbool::l_true)
            {
                max_iter_iso_mor = std::max(max_iter_iso_mor, num_iter);
                return phi;
            }
            if (num_iter >= m_params.theshold_iso_decomp())
            {
                if (VERBOSE_ABDUCE)
                    std::cout << "!!! ISO_DECOMP_ITERS_TRESHOLD " << std::endl;
                return expr_ref(m.mk_false(), m);
            }
            model_ref mdl;
            slv->get_model(mdl);
            slv->pop(1);
            expr_ref res = get_soln_according_to_model(mdl, fresh_constant, pattern);
            phi = m.mk_or(phi, res);
            if (DEBUG_ABDUCE)
                std::cout << "new phi(line 23) "  << mk_ismt2_pp(phi, m, 3) << std::endl;

            expr_ref_vector phi_i(m);
            for (unsigned i = 0; i < decl_args.size(); ++i)
            {
                phi_i.push_back(m_utils.replace_vars_decl(phi, pattern, decl_args.get(i)));
            }

            for (unsigned i = 0; i < decl_args.size(); ++i)
            {
                expr_ref phi_except_i(m.mk_true(), m);
                for (unsigned j = 0; j < decl_args.size(); ++j)
                {
                    if (j != i)
                        phi_except_i  = m.mk_and(phi_except_i, phi_i.get(j));
                }
                phi_except_i = m_utils.simplify_context(phi_except_i);
                if (DEBUG_ABDUCE)
                    std::cout << "phi_except_i " << i <<  mk_ismt2_pp(phi_except_i, m, 3) << std::endl;
                //expr_ref old_phi_i(phi_i[i].get(), m);

                phi_i[i] = simple_abduce_mbp(phi_except_i, conclusion, decl_args.get(i));
                if (VERBOSE_ABDUCE)
                {
                    //std::cout << "check either old phi_i implies abduced phi_i: " << m_utils.implies(old_phi_i, phi_i[i].get()) << std::endl;
                    //std::cout << m_utils.simplify_context(old_phi_i) << " ==>" << m_utils.simplify_context(expr_ref(phi_i[i].get(), m)) << std::endl;
                }
            }

            phi = m.mk_true();
            for (unsigned i = 0; i < decl_args.size(); ++i)
            {
                phi = m.mk_and(phi, m_utils.replace_vars_decl(expr_ref(phi_i[i].get(), m), decl_args.get(i), pattern));
            }

            //if (VERBOSE_ABDUCE)
            //    std::cout << "crnt phi (line after 27) "   << mk_ismt2_pp(phi, m, 3) << std::endl;
            phi = m_utils.simplify_context(phi);

            clock_t start = clock();
            if (VERBOSE_ABDUCE)
            {
                std::cout << "crnt phi-simplified (line after 27) "   << mk_ismt2_pp(phi, m, 3) << std::endl;
                std::cout << "time :" << ((double)(clock() - start) / CLOCKS_PER_SEC) << std::endl;;
            }
            num_iter++;
        }
        return expr_ref(m.mk_false(), m);
    }
    expr_ref multi_abducer::simple_abduce_exist(expr_ref premise, expr_ref conclusion, func_decl_ref_vector vars)
    {
        expr_ref implic(m.mk_implies(premise, conclusion), m);
        decl_collector decls(m);
        decls.visit(implic.get());
        func_decl_ref_vector quantifier_vars(m);

        for (func_decl *fd :  decls.get_func_decls())
        {
            if (!vars.contains(fd))
            {
                quantifier_vars.push_back(fd);
            }
        }
        if (quantifier_vars.size() == 0)
        {
            return implic;
        }
        implic = m_utils.exist_quantified(implic, quantifier_vars);
        if (DEBUG_ABDUCE)
            std::cout << "Simple abduction : " << mk_ismt2_pp(implic, m, 3) << std::endl;

        //std::cout << "Simple abduction implic2: " << mk_ismt2_pp(implic, m, 3) << std::endl;
        smt_params params;
        expr_ref result(m);
        qe::expr_quant_elim      expr_qe(m, params);
        expr_qe(m.mk_true(), implic, result);

        //through tactic qe
        /* tactic_ref tct = mk_qe_tactic(m);
        goal_ref g = alloc(goal, m);

        g->assert_expr(implic);

        goal_ref_buffer result_goal;
        (*tct)(g, result_goal);
        goal *r = result_goal[0];
        expr_ref_vector res_fmls(m);
        r->get_formulas(res_fmls);
        expr_ref result(m_utils.con_join(res_fmls), m);*/
        if (DEBUG_ABDUCE)
            std::cout << "Simple EXIST abduction result: " << mk_ismt2_pp(result, m, 3) << std::endl;
        return result;
    }
    expr_ref multi_abducer::simple_abduce(expr_ref premise, expr_ref conclusion, func_decl_ref_vector vars)
    {
        expr_ref implic(m.mk_implies(premise, conclusion), m);
        decl_collector decls(m);
        decls.visit(implic.get());
        func_decl_ref_vector quantifier_vars(m);

        for (func_decl *fd :  decls.get_func_decls())
        {
            if (!vars.contains(fd))
            {
                quantifier_vars.push_back(fd);
            }
        }
        if (quantifier_vars.size() == 0)
        {
            return implic;
        }
        implic = m_utils.universal_quantified(implic, quantifier_vars);
        if (DEBUG_ABDUCE)
            std::cout << "Simple abduction : " << mk_ismt2_pp(implic, m, 3) << std::endl;

        //std::cout << "Simple abduction implic2: " << mk_ismt2_pp(implic, m, 3) << std::endl;
        smt_params params;
        expr_ref result(m);
        qe::expr_quant_elim      expr_qe(m, params);
        expr_qe(m.mk_true(), implic, result);

        //through tactic qe
        /* tactic_ref tct = mk_qe_tactic(m);
        goal_ref g = alloc(goal, m);

        g->assert_expr(implic);

        goal_ref_buffer result_goal;
        (*tct)(g, result_goal);
        goal *r = result_goal[0];
        expr_ref_vector res_fmls(m);
        r->get_formulas(res_fmls);
        expr_ref result(m_utils.con_join(res_fmls), m);*/
        if (DEBUG_ABDUCE)
            std::cout << "Simple abduction result: " << mk_ismt2_pp(result, m, 3) << std::endl;
        return result;
    }

    expr_ref multi_abducer::simple_abduce_mbp(expr_ref premise, expr_ref conclusion, func_decl_ref_vector vars)
    {
        expr_ref implic(m.mk_implies(premise, conclusion), m);
        decl_collector decls(m);
        decls.visit(implic.get());
        func_decl_ref_vector quantifier_vars(m);

        app_ref_vector quantifier_vars_apps(m);


        for (func_decl *fd :  decls.get_func_decls())
        {
            if (!vars.contains(fd))
            {
                quantifier_vars.push_back(fd);
                quantifier_vars_apps.push_back(m.mk_const(fd));
            }
        }


        smt_params params;
        expr_ref result_qe(m.mk_false(), m);
        expr_ref implic_q = m_utils.universal_quantified(implic, quantifier_vars);
        qe::expr_quant_elim      expr_qe(m, params);
        expr_qe(m.mk_true(), implic_q, result_qe);


        implic = mk_not(implic);
        if (DEBUG_ABDUCE)
            std::cout << "Simple abduction mbp : " << mk_ismt2_pp(implic, m, 3) << std::endl;
        params_ref params_slv;
        ref<solver> slv = m_cmd.get_solver_factory()(m, params_slv, false, true, false, symbol::null);

        slv->push();
        slv->assert_expr(implic);
        lbool r = slv->check_sat();

        if (r != lbool::l_true)
        {
            std::cout << "ERROR!!! Simple abduction(MBP) is unsat: " << mk_ismt2_pp(implic, m, 3) << std::endl;
            return expr_ref(m.mk_true(), m);
        }
        model_ref model;
        slv->get_model(model);
        if (DEBUG_ABDUCE)
            std::cout << "ERROR!!! Simple abduction(MBP) model " << *model << std::endl;
        expr_ref result_qembp(m.mk_false(), m);
        expr_ref_vector res_v(m);
        res_v.push_back(implic);
        qe::mbp mbp(m);
        mbp(true,  quantifier_vars_apps, *model, res_v);
        result_qembp = m.mk_not(m_utils.con_join(res_v));


        expr_ref result_spacer(implic, m);
        spacer::qe_project(m, quantifier_vars_apps, result_spacer, *model);
        result_spacer = m.mk_not(result_spacer);

        //[check]
        std::cout << "Simple abduction(MBP) checking: "  << m_utils.implies(result_qe, result_qembp) << std::endl;
        std::cout << "Simple abduction(MBP) checking for spacer: "  << m_utils.implies(result_qe, result_spacer) << std::endl;

        std::cout << "Simple abduction(MBP) checking: "  << m_utils.implies(implic_q, result_qembp) << std::endl;
        std::cout << "Simple abduction(MBP) checking for spacer: "  << m_utils.implies(implic_q, result_spacer) << std::endl;
        //
        if (DEBUG_ABDUCE)
        {
            std::cout << "Simple abduction(Full qe) result: " << mk_ismt2_pp(result_qe, m, 3) << std::endl;
            std::cout << "Simple abduction(MBP) result: " << mk_ismt2_pp(result_qembp, m, 3) << std::endl;
            std::cout << "Simple abduction(MBP spacer) result: " << mk_ismt2_pp(result_spacer, m, 3) << std::endl;
        }
        return result_qembp;
    }
}
