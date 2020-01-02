//#include "ast/decl_collector.h"
#include "ast/ast_pp.h"
#include "ast/rewriter/rewriter.h"
#include "ast/rewriter/rewriter_def.h"
#include <iomanip>
#include <iostream>
#include <set>

#include <ast/used_vars.h>
#include <ast/rewriter/th_rewriter.h>
#include "multi_abducer.h"
#include "ast/rewriter/expr_replacer.h"
#include "qe/qe.h"

#include <ctime>

#define DEBUG_ABDUCE false
#define VERBOSE_ABDUCE true

namespace misynth
{
    const int ISO_DECOMP_ITERS_TRESHOLD = 10;
    multi_abducer::multi_abducer(cmd_context &cmd_ctx, ast_manager &m) : m_cmd(cmd_ctx), m(m), m_arith(m), m_utils(cmd_ctx, m)
    {
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

    expr_ref multi_abducer::nonlinear_abduce(vector<expr_ref_vector> &inv_args, expr_ref premise, expr_ref conclusion, func_decl_ref_vector &pattern)
    {

        vector<func_decl_ref_vector> decl_args;
        expr_ref flat_premise = to_flat(inv_args, decl_args);
        func_decl_ref_vector all_vars(m);
        for (auto &a : decl_args)
        {
            all_vars.append(a);
        }
        expr_ref flat_conclusion(m.mk_implies(flat_premise, conclusion), m);
        if (DEBUG_ABDUCE)
            std::cout << "Abduction flat_conclusion formula: " << mk_ismt2_pp(flat_conclusion, m, 3) << std::endl;

        expr_ref abduce_conclusion = simple_abduce(premise, flat_conclusion, all_vars);
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

            return iso_decomp(implic, res, abduce_conclusion, inv_args, fresh_constant, pattern, decl_args);

        }

        return expr_ref(m.mk_false(), m);
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


    expr_ref  multi_abducer::get_soln_according_to_model(model_ref mdl, vector<func_decl_ref_vector> &fresh_constant, func_decl_ref_vector &pattern)
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

    expr_ref  multi_abducer::iso_decomp(expr_ref conclusion_model, expr_ref init_soln, expr_ref conclusion, vector<expr_ref_vector> &inv_args, vector<func_decl_ref_vector> &fresh_constant, func_decl_ref_vector &pattern, vector<func_decl_ref_vector> &decl_args)
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
                return phi;
            }
            if (num_iter >= ISO_DECOMP_ITERS_TRESHOLD)
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

                phi_i[i] = (simple_abduce(phi_except_i, conclusion, decl_args.get(i)));
            }

            phi = m.mk_true();
            for (unsigned i = 0; i < decl_args.size(); ++i)
            {
                phi = m.mk_and(phi, m_utils.replace_vars_decl(expr_ref(phi_i[i].get(), m), decl_args.get(i), pattern));
            }

            if (VERBOSE_ABDUCE)
                std::cout << "crnt phi (line after 27) "   << mk_ismt2_pp(phi, m, 3) << std::endl;
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

        if (DEBUG_ABDUCE)
            std::cout << "Simple abduction : " << mk_ismt2_pp(implic, m, 3) << std::endl;
        implic = m_utils.universal_quantified(implic, quantifier_vars);
        //std::cout << "Simple abduction implic2: " << mk_ismt2_pp(implic, m, 3) << std::endl;
        smt_params params;
        expr_ref result(m);
        qe::expr_quant_elim      expr_qe(m, params);
        expr_qe(m.mk_true(), implic, result);
        if (DEBUG_ABDUCE)
            std::cout << "Simple abduction result: " << mk_ismt2_pp(result, m, 3) << std::endl;
        return result;
    }


}
