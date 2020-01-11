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
            //smt_utils m_utils;

        public:
            invocations_rewriter(cmd_context &cmd_ctx, ast_manager &m)
                : m_cmd(cmd_ctx)
                , m(m)
                , m_arith(m)
                  // , m_utils(cmd_ctx, m)

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

            void rewriter_functions_to_linear_term(func_decl_ref_vector coeff_decl_vec, func_decl_ref_vector &synth_funs,
                                                   expr_ref spec, expr_ref &new_spec)
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
    }; //invocations_rewriter
}
#endif // REWRITER_COEFFICIENTS_H
