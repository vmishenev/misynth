#ifndef COLLECTOR_LITERALS_H
#define COLLECTOR_LITERALS_H

#include "ast/ast.h"
#include "ast/expr_delta_pair.h"

#include "util/hashtable.h"
#include "ast/ast_pp.h"
#include "cmd_context/cmd_context.h"
#include "model/model.h"
#include "smt_utils.h"

#include "misynth/rewriter_coefficients.h"

namespace misynth
{


    class literals_collector
    {
        private:
            //typedef hashtable<symbol, symbol_hash_proc, symbol_eq_proc> symbol_set;
            typedef obj_hashtable<app > app_set;

            func_decl_ref_vector&   m_fun_list;
            app_set                 m_literals;
            obj_hashtable<expr>     m_visited;
            ptr_vector<expr>        m_todo;
            ast_manager             &m;


            void visit(expr * n)
            {
                if (!m_visited.contains(n))
                {
                    m_visited.insert(n);
                    m_todo.push_back(n);
                }
            }

        public:
            literals_collector(func_decl_ref_vector&   fun_list):
                m_fun_list(fun_list), m(fun_list.m())
            {
            }

            void operator()(expr * n, bool ignore_quantifiers = false)
            {
                m_visited.reset();
                m_literals.reset();
                m_todo.reset();
                visit(n);
                while (!m_todo.empty())
                {
                    n = m_todo.back();
                    m_todo.pop_back();
                    unsigned j;
                    switch (n->get_kind())
                    {
                        case AST_APP:
                            {

                                if (m.is_eq(n))
                                {
                                    app *app_qe = to_app(n);
                                    //todo check f
                                    app *left = to_app(app_qe->get_arg(0));
                                    app *right = to_app(app_qe->get_arg(1));
                                    if (m_fun_list.contains(left->get_decl()) || m_fun_list.contains(right->get_decl()))
                                    {
                                        m_literals.insert(app_qe);
                                    }
                                }
                                else
                                {
                                    j = to_app(n)->get_num_args();
                                    while (j > 0)
                                    {
                                        --j;
                                        visit(to_app(n)->get_arg(j));
                                    }
                                }
                                break;
                            }
                        case AST_QUANTIFIER:
                            if (!ignore_quantifiers)
                            {

                                //unsigned num_decls = to_quantifier(n)->get_num_decls();
                                //for (unsigned i = 0; i < num_decls; i++)
                                //found(to_quantifier(n)->get_decl_name(i));
                                unsigned num_pats = to_quantifier(n)->get_num_patterns();
                                for (unsigned i = 0; i < num_pats; i++)
                                    visit(to_quantifier(n)->get_pattern(i));
                                unsigned num_no_pats = to_quantifier(n)->get_num_no_patterns();
                                for (unsigned i = 0; i < num_no_pats; i++)
                                    visit(to_quantifier(n)->get_no_pattern(i));
                                visit(to_quantifier(n)->get_expr());
                            }
                            break;
                        default:
                            break;
                    }
                }
            }

            app_set &get_literals()
            {
                return m_literals;
            }


    };
    class vars_collector_except_funs
    {
        private:
            //typedef hashtable<symbol, symbol_hash_proc, symbol_eq_proc> symbol_set;
            typedef obj_hashtable<func_decl > decl_set;

            func_decl_ref_vector&   m_fun_list;
            decl_set                 m_vars;
            obj_hashtable<expr>     m_visited;
            ptr_vector<expr>        m_todo;
            ast_manager             &m;


            void visit(expr * n)
            {
                if (!m_visited.contains(n))
                {
                    m_visited.insert(n);
                    m_todo.push_back(n);
                }
            }

        public:
            vars_collector_except_funs(func_decl_ref_vector&   fun_list):
                m_fun_list(fun_list), m(fun_list.m())
            {
            }

            void operator()(expr * n, bool ignore_quantifiers = false)
            {
                m_visited.reset();
                m_vars.reset();
                m_todo.reset();
                visit(n);
                while (!m_todo.empty())
                {
                    n = m_todo.back();
                    m_todo.pop_back();
                    unsigned j;
                    switch (n->get_kind())
                    {
                        case AST_APP:
                            {

                                app * ap =  to_app(n);
                                if (m_fun_list.contains(ap->get_decl()))
                                    break;
                                j = ap->get_num_args();
                                if (j == 0)
                                    m_vars.insert(ap->get_decl());
                                while (j > 0)
                                {
                                    --j;
                                    visit(ap->get_arg(j));
                                }

                                break;
                            }
                        case AST_QUANTIFIER:
                            if (!ignore_quantifiers)
                            {

                                //unsigned num_decls = to_quantifier(n)->get_num_decls();
                                //for (unsigned i = 0; i < num_decls; i++)
                                //found(to_quantifier(n)->get_decl_name(i));
                                unsigned num_pats = to_quantifier(n)->get_num_patterns();
                                for (unsigned i = 0; i < num_pats; i++)
                                    visit(to_quantifier(n)->get_pattern(i));
                                unsigned num_no_pats = to_quantifier(n)->get_num_no_patterns();
                                for (unsigned i = 0; i < num_no_pats; i++)
                                    visit(to_quantifier(n)->get_no_pattern(i));
                                visit(to_quantifier(n)->get_expr());
                            }
                            break;
                        default:
                            break;
                    }
                }
            }

            decl_set &get_vars()
            {
                return m_vars;
            }


    };
    void collect_coeff_from_lits(cmd_context &cmd_ctx, ast_manager &m, arith_util &arith, smt_utils &utils, expr * n,
                                 func_decl_ref_vector&   fun_list, func_decl_ref_vector &coeff_decl_vec,
                                 func_decl_ref_vector &used_vars, std::vector<model_ref> &models)
    {



        params_ref m_params;

        expr_ref res_n(m);
        proof_ref pr2(m);

        th_rewriter s(m, m_params);
        th_solver solver(cmd_ctx);
        s.set_solver(alloc(th_solver, cmd_ctx));
        s(n, res_n, pr2);

        literals_collector collector(fun_list);
        collector(res_n);
        obj_hashtable<app > set = collector.get_literals();
        std::cout << "collect_coeff_from_lits size  " << set.size() << std::endl;
        std::cout << "res_n" << mk_smt_pp(res_n, m) << std::endl;
        for (auto it = set.begin(); it != set.end(); it++)
        {
            app * ap_f = (*it);
            expr_ref lit(m);
            invocations_rewriter rwr(cmd_ctx, m);

            rwr.rewriter_functions_to_linear_term(coeff_decl_vec, fun_list, expr_ref(ap_f, m), lit);
            std::cout << "lit " << mk_smt_pp(lit, m) << std::endl;

            expr_ref r(m);
            proof_ref pr(m);

            th_rewriter s(m, m_params);
            th_solver solver(cmd_ctx);
            s.set_solver(alloc(th_solver, cmd_ctx));
            s(lit, r, pr);
            std::cout << "Lit in nf2 " << mk_smt_pp(r, m) << std::endl;
            if (is_app(lit))
            {

                //app* a = to_app(r);
                expr* left = ap_f->get_arg(0);
                expr* right = ap_f->get_arg(1);

                if (arith.is_numeral(right))
                {
                    model_ref mdl = utils.get_model(expr_ref(m.mk_eq(m.mk_const(coeff_decl_vec.get(0)), right), m));
                    models.push_back(mdl);
                    continue;
                }
                /*[+] collect all vars*/
                vars_collector_except_funs collector_vars(fun_list);
                collector_vars(ap_f);
                obj_hashtable<func_decl > varset = collector_vars.get_vars();
                func_decl_ref_vector used_vars(m);
                for (auto itv = varset.begin(); itv != varset.end(); itv++)
                {
                    used_vars.push_back(*itv);
                    func_decl *fd = *itv;
                    std::cout << "add used var2: " << fd->get_name() << "  " << mk_ismt2_pp(fd, m, 3)  << std::endl;
                }
                /**/

                decl_collector decls(m);
                decls.visit(ap_f);
                func_decl_ref_vector used_vars_right(m);
                //arith_util arith(m);
                expr_ref_vector zeros(m);
                for (func_decl *fd :  decls.get_func_decls())
                {
                    if (!used_vars.contains(fd) && !fun_list.contains(fd))
                    {
                        used_vars_right.push_back(fd);
                        zeros.push_back(arith.mk_int(0));
                        std::cout << "add used var3: " << fd->get_name() << "  " << mk_ismt2_pp(fd, m, 3)  << std::endl;

                    }
                }

                std::cout << "model lit0 " << mk_smt_pp(lit, m) << std::endl;
                //func_decl_ref_vector used_vars_right(m, decls.get_num_decls(), decls.get_func_decls().c_ptr());
                expr_ref res_lit(m.mk_and(utils.universal_quantified(lit, used_vars), utils.mk_eq(used_vars_right, zeros)), m);
                std::cout << "model lit2 " << mk_smt_pp(res_lit, m) << std::endl;
                model_ref mdl = utils.get_model(res_lit);
                if (mdl)
                {
                    std::cout << "model lit3 " << *mdl << std::endl;
                    models.push_back(mdl);
                    continue;
                }
            }

            expr_ref res_lit = utils.universal_quantified(lit, used_vars);
            std::cout << "model lit " << mk_smt_pp(res_lit, m) << std::endl;
            model_ref mdl = utils.get_model(res_lit);
            if (mdl)
            {
                std::cout << "model lit " << *mdl << std::endl;
                models.push_back(mdl);
            }
        }//
    }



} //misynth



#endif // COLLECTOR_LITERALS_H
