#ifndef MISYNTH_SOLVER_H
#define MISYNTH_SOLVER_H

#include "cmd_context/cmd_context.h"
#include "misynth/multi_abducer.h"

#include "smt_utils.h"


namespace misynth
{

    extern bool DEBUG_MODE;
    typedef func_decl_ref_vector  args_t;//svector<func_decl>
    typedef expr_ref_vector invocation_operands;
    typedef obj_map<app, expr * > app2expr_map;
    typedef obj_hashtable<expr> expr_set;
    typedef obj_map<func_decl, expr *> decl2expr_map;
    typedef obj_map<func_decl, expr_ref_vector> decl2expr_ref_vec;

    class misynth_solver
    {

        private:
            cmd_context &m_cmd;
            ast_manager &m;
            ref<solver> m_solver;

            smt_utils m_utils;
            arith_util m_arith;

            func_decl_ref_vector m_coeff_decl_vec;
            func_decl_ref_vector m_used_vars;
            expr_ref_vector m_precs, m_branches;
            expr_ref_vector m_terms;
            app2expr_map m_term_subst;


            vector<invocation_operands> m_ops;
            obj_map<func_decl, args_t *> m_synth_fun_args_decl;
            multi_abducer m_abducer;
        public:
            misynth_solver(cmd_context &cmd_ctx, ast_manager &m, solver *solver);

            expr_ref generate_clia_fun_body();
            void print_def_fun(std::ostream &out, func_decl * f, func_decl_ref_vector &args, expr_ref body);
            void print_sorted_var_list(std::ostream &out,  func_decl_ref_vector & sorted_var);


            bool solve(func_decl_ref_vector &synth_funs, expr_ref_vector &constraints,  obj_map<func_decl, args_t *> &synth_fun_args_decl);


            void generate_coeff_decl(func_decl_ref_vector &synth_funs);
            void rewriter_functions_to_linear_term(func_decl_ref_vector &synth_funs,
                                                   expr_ref spec, expr_ref &new_spec);

            void rewrite_expr(expr *f, expr_ref &res);

            void init_used_variables(func_decl_ref_vector &synth_funs, expr_ref spec);
            expr_ref find_precondition(func_decl_ref_vector &synth_funs,  expr_ref &spec_for_concrete_coeff);
            args_t *get_args_decl_for_synth_fun(func_decl *f);
            expr_ref generate_branch(func_decl_ref_vector &synth_funs, model_ref mdl);

            /* [+] Unrealizability Algorithm*/

            bool prove_unrealizability(expr_ref spec);

            bool check_assumptions(expr_ref spec, expr_ref_vector &assumptions);

            /*
             *
             * @Return either unrealizability
             *
             * */
            bool subsets_backtracking(expr_ref_vector &assump, expr *spec,
                                      solver *slv, unsigned int index);
            void generate_assumptions_from_operands(expr_ref_vector &assumptions);
            /* [-] Unrealizability Algorithm*/
    };
}


#endif // MISYNTH_SOLVER_H
