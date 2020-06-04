#ifndef REWRITER_COEFFICIENTS_H
#define REWRITER_COEFFICIENTS_H

#include "cmd_context/cmd_context.h"
#include "ast/rewriter/rewriter.h"
#include "collector_invocation_operands.h"
namespace misynth
{

    typedef obj_map<app, expr * > app2expr_map;
    struct invocations_rewriter_cfg : public default_rewriter_cfg
    {

        private:
            ast_manager &m;
            obj_map<app, expr *> &m_synth_fun_sub_map;

        public:
            invocations_rewriter_cfg(ast_manager &m,

                                     obj_map<app, expr * > &sub_map)
                : m(m)
                , m_synth_fun_sub_map(sub_map)
            {
            }

            bool get_subst(expr *s, expr *&t, proof *&t_pr)
            {
                if (!is_app(s))
                {
                    return false;
                }

                app *a = to_app(s);

                expr *sub;

                if (!m_synth_fun_sub_map.find(a, sub))
                {
                    return false;
                }

                t = sub;

                /*if (DEBUG)
                {
                    std::cout << "\t get_subst: " << mk_ismt2_pp(s, m, 3) << std::endl;
                }*/

                return true;
            }



    };
    class invocations_rewriter
    {
        private:
            cmd_context &m_cmd;
            ast_manager &m;
            arith_util m_arith;
            smt_utils m_utils;

        public:
            invocations_rewriter(cmd_context &cmd_ctx, ast_manager &m)
                : m_cmd(cmd_ctx)
                , m(m)
                , m_arith(m)
                , m_utils(cmd_ctx, m)

            {
            }

            void rewrite_expr(expr *f, expr_ref &res, app2expr_map& subst)
            {
                invocations_rewriter_cfg inv_cfg(m, subst);
                rewriter_tpl<invocations_rewriter_cfg> rwr(m, false, inv_cfg);
                rwr(f, res);
            }
            expr_ref rewrite_app(app * ap_f, func_decl_ref_vector& coeff_decl_vec)
            {
                expr_ref_vector mult_terms(m);
                mult_terms.push_back(m.mk_const(coeff_decl_vec.get(0)));


                for (unsigned i = 0; i < ap_f->get_num_args(); ++i)
                {
                    expr *term = m_arith.mk_mul(m.mk_const(coeff_decl_vec.get(1 + i)), ap_f->get_arg(i));
                    mult_terms.push_back(term);
                }

                expr_ref linear_term = m_arith.mk_add_simplify(mult_terms);
                return linear_term;
            }
            void rewrite_app_with_branch(expr_ref e,  func_decl_ref_vector &synth_funs, expr_ref_vector & precs,   expr_ref_vector & branches, func_decl_ref_vector & pattern, expr_ref & res, model_ref mdl_for_x, vector<unsigned int> &used_branches)
            {
                invocation_collector collector(synth_funs);
                collector(e);
                obj_hashtable<app > set = collector.get_invocation();

                app2expr_map  term_subst;
                for (auto it = set.begin(); it != set.end(); it++)
                {
                    app *ap_f = (*it);

                    //[+] use founded precs
                    expr_ref_vector op(m, ap_f->get_num_args(), ap_f->get_args());
                    bool is_found = false;
                    for (unsigned i = 0; i < precs.size(); ++i)
                    {
                        expr_ref called_prec = (*mdl_for_x)(m_utils.replace_vars_decl(precs.get(i), pattern, op));
                        if (m_utils.is_true(called_prec))
                        {
                            std::cout << "Reused prec " << mk_ismt2_pp(precs.get(i), m, 0) << " for " << mk_ismt2_pp(called_prec, m, 0) << std::endl;
                            expr_ref called_branch = m_utils.replace_vars_decl(branches.get(i), pattern, op);
                            term_subst.insert(ap_f, called_branch);
                            std::cout << "Reused branch " << mk_ismt2_pp(branches.get(i), m, 0) << " for " << mk_ismt2_pp(called_branch, m, 0) << std::endl;
                            is_found = true;
                            used_branches.insert(i);
                            break;
                        }

                    }
                    if (is_found)
                        continue;
                    //[-]
                }
                rewrite_expr(e, res, term_subst);
            }

            void rewriter_functions_to_linear_term_with_prec(func_decl_ref_vector coeff_decl_vec, func_decl_ref_vector & synth_funs,
                    expr_ref spec, expr_ref & new_spec, func_decl_ref_vector & pattern, expr_ref_vector & precs, expr_ref_vector & branches)
            {
                invocation_collector collector(synth_funs);
                collector(spec);


                obj_hashtable<app > set = collector.get_invocation();

                app2expr_map  term_subst;
                expr_ref_vector accumulator_terms(m), accumulator_branches(m);
                for (auto it = set.begin(); it != set.end(); it++)
                {
                    app *ap_f = (*it);

                    //[+] use founded precs
                    expr_ref_vector op(m, ap_f->get_num_args(), ap_f->get_args());
                    bool is_found = false;
                    for (unsigned i = 0; i < precs.size(); ++i)
                    {
                        expr_ref called_prec = m_utils.replace_vars_decl(precs.get(i), pattern, op);
                        if (m_utils.is_true(called_prec))
                        {
                            std::cout << "Reused prec " << mk_ismt2_pp(precs.get(i), m, 0) << " for " << mk_ismt2_pp(called_prec, m, 0) << std::endl;
                            expr_ref called_branch = m_utils.replace_vars_decl(branches.get(i), pattern, op);
                            term_subst.insert(ap_f, called_branch);
                            accumulator_branches.push_back(called_branch);
                            std::cout << "Reused branch " << mk_ismt2_pp(branches.get(i), m, 0) << " for " << mk_ismt2_pp(called_branch, m, 0) << std::endl;
                            is_found = true;
                            break;
                        }

                    }
                    if (is_found)
                        continue;
                    //[-]

                    expr_ref_vector mult_terms(m);
                    mult_terms.push_back(m.mk_const(coeff_decl_vec.get(0)));


                    for (unsigned i = 0; i < ap_f->get_num_args(); ++i)
                    {
                        expr *term = m_arith.mk_mul(m.mk_const(coeff_decl_vec.get(1 + i)), ap_f->get_arg(i));
                        mult_terms.push_back(term);
                    }

                    expr_ref linear_term = m_arith.mk_add_simplify(mult_terms);
                    term_subst.insert(ap_f, linear_term);
                    accumulator_terms.push_back(linear_term);
                    //m_terms.push_back(linear_term);
                }

                rewrite_expr(spec, new_spec, term_subst);

            }

            void rewriter_functions_to_linear_term(func_decl_ref_vector &coeff_decl_vec, func_decl_ref_vector & synth_funs,
                                                   expr_ref spec, expr_ref & new_spec)
            {
                invocation_collector collector(synth_funs);
                collector(spec);


                obj_hashtable<app > set = collector.get_invocation();

                app2expr_map  term_subst;
                expr_ref_vector accumulator_terms(m);
                for (auto it = set.begin(); it != set.end(); it++)
                {
                    app *ap_f = (*it);
                    expr_ref_vector mult_terms(m);
                    mult_terms.push_back(m.mk_const(coeff_decl_vec.get(0)));


                    for (unsigned i = 0; i < ap_f->get_num_args(); ++i)
                    {
                        expr *term = m_arith.mk_mul(m.mk_const(coeff_decl_vec.get(1 + i)), ap_f->get_arg(i));
                        mult_terms.push_back(term);
                    }

                    expr_ref linear_term = m_arith.mk_add_simplify(mult_terms);
                    term_subst.insert(ap_f, linear_term);
                    accumulator_terms.push_back(linear_term);
                    //m_terms.push_back(linear_term);
                }

                rewrite_expr(spec, new_spec, term_subst);

            }
            void rewriter_functions_to_linear_term(expr_ref_vector &coeff_vec, func_decl_ref_vector & synth_funs,
                                                   expr_ref spec, expr_ref & new_spec)
            {
                invocation_collector collector(synth_funs);
                collector(spec);


                obj_hashtable<app > set = collector.get_invocation();

                app2expr_map  term_subst;
                expr_ref_vector accumulator_terms(m);
                for (auto it = set.begin(); it != set.end(); it++)
                {
                    app *ap_f = (*it);
                    expr_ref_vector mult_terms(m);
                    mult_terms.push_back(coeff_vec.get(0));//C0


                    for (unsigned i = 0; i < ap_f->get_num_args(); ++i)
                    {
                        if (m_arith.is_zero(coeff_vec.get(1 + i)))
                            continue;
                        expr *term = m_arith.mk_mul(coeff_vec.get(1 + i), ap_f->get_arg(i));
                        mult_terms.push_back(term);
                    }

                    expr_ref linear_term = m_arith.mk_add_simplify(mult_terms);
                    term_subst.insert(ap_f, linear_term);
                    accumulator_terms.push_back(linear_term);
                    //m_terms.push_back(linear_term);
                }

                rewrite_expr(spec, new_spec, term_subst);

            }
            void rewriter_fun_inv_to_var(expr_ref spec, func_decl_ref_vector & synth_funs,
                                         app2expr_map &map, func_decl_ref_vector &fresh_vars, expr_ref_vector& inv_replaced, expr_ref & new_spec)
            {
                invocation_collector collector(synth_funs);
                collector(spec);


                obj_hashtable<app > set = collector.get_invocation();

                app2expr_map  term_subst;
                expr_ref_vector accumulator_terms(m);
                std::string prefix = "y_";
                int i = 0;
                for (auto it = set.begin(); it != set.end(); it++)
                {

                    app *ap_f = (*it);

                    func_decl_ref fresh_var(m.mk_const_decl(prefix + std::to_string(i), m_arith.mk_int()), m);
                    fresh_vars.push_back(fresh_var);
                    inv_replaced.push_back(ap_f);
                    expr *y = m.mk_const(fresh_var);
                    term_subst.insert(ap_f, y);
                    accumulator_terms.push_back(y);
                    //m_terms.push_back(linear_term);
                    i++;
                }

                rewrite_expr(spec, new_spec, term_subst);

            }


    }; //invocations_rewriter
}
#endif // REWRITER_COEFFICIENTS_H
