#ifndef MISYNTH_SOLVER_H
#define MISYNTH_SOLVER_H

#include "cmd_context/cmd_context.h"
#include "misynth/multi_abducer.h"
#include "misynth/synth_task.h"

#include "smt_utils.h"
#include "function_utils.h"
#include "misynth/synth_params.hpp"
#include "misynth/ite_function.h"


namespace misynth
{

    extern bool DEBUG_MODE;
    typedef func_decl_ref_vector  args_t;//svector<func_decl>
    typedef expr_ref_vector invocation_operands;
    typedef obj_map<app, expr * > app2expr_map;
    //typedef obj_hashtable<expr> expr_set;
    typedef obj_map<func_decl, expr *> decl2expr_map;
    typedef obj_map<func_decl, expr_ref_vector> decl2expr_ref_vec;


    enum struct result_incremental_abd
    {
        false_v = 0,
        true_v,
        total_false

    };

    class misynth_solver
    {

        private:
            cmd_context &m_cmd;
            ast_manager &m;
            synth_params m_params;
            ref<solver> m_solver;

            smt_utils m_utils;
            arith_util m_arith;
            function_utils m_futils;

            func_decl_ref_vector m_coeff_decl_vec;
            func_decl_ref_vector m_used_vars;
            expr_ref_vector m_assumptions;
            expr_ref_vector assms;
            expr_ref_vector assms2;

            vector<invocation_operands> m_ops;
            obj_map<func_decl, args_t *> m_synth_fun_args_decl;
            multi_abducer m_abducer;

            vector<model_ref> m_models_from_assumptions;
            ref<solver> m_slv_for_x_prec;
            ref<solver> m_slv_for_coeff;

            vector<ref<solver> > m_slv_for_coeff_vec;
            unsigned int m_current_slv_for_coeff;
            ite_function fn;
            synth_task task;
        public:

            misynth_solver(cmd_context &cmd_ctx, ast_manager &m, solver *solver);

            /* [+]  Getting X model*/
            void init_x_solver();
            model_ref get_model_x(synth_task &task, expr_ref heuristic);
            /* [-]  Getting X model*/


            /* [+]  Getting model of coeff*/
            model_ref get_coeff_model_from_slv(ref<solver> &slv, expr_ref spec_for_concrete_x, expr_ref heuristic);
            void init_coeff_solver(func_decl_ref_vector & synth_funs);
            model_ref get_coeff_model(expr_ref spec_for_concrete_x, expr_ref heuristic);
            /* [-]  Getting model of coeff*/


            /* [+] incremental multiabduction*/
            result_incremental_abd incremental_multiabduction(func_decl_ref_vector & synth_funs, expr_ref & simplified_spec, expr_ref & new_branch, app_ref_vector &invocations, expr_ref &result);
            expr_ref solve_abduction_for_comb(vector<unsigned int> &comb, func_decl_ref_vector & synth_funs, expr_ref & spec, app_ref_vector &invocations, expr_ref & new_branch);

            result_incremental_abd check_all_abductions(func_decl_ref_vector & synth_funs, expr_ref & spec, app_ref_vector &invocations, expr_ref & new_prec, expr_ref & new_branch);
            result_incremental_abd check_abduction_for_comb(vector<unsigned int> &comb, func_decl_ref_vector & synth_funs, expr_ref & spec, app_ref_vector &invocations, expr_ref & new_prec, expr_ref & new_branch);
            /* [-] incremental multiabduction*/

            expr_ref generate_heuristic_constaraint_coeff(expr_ref spec, func_decl_ref_vector &coeff_decls);
            bool try_find_simultaneously_branches(func_decl_ref_vector &synth_funs, expr_ref_vector &constraints, model_ref mdl, bool is_infinity_loop = false);
            void print_def_fun(std::ostream &out, func_decl * f, func_decl_ref_vector &args, expr_ref body);

            bool multi_solve(func_decl_ref_vector & synth_funs, expr_ref_vector & constraints,
                             obj_map<func_decl, args_t *> &synth_fun_args_decl);
            expr_ref_vector collect_constraints(func_decl_ref target, func_decl_ref_vector & synth_funs, expr_ref_vector & constraints);
            bool solve(func_decl_ref_vector &synth_funs, expr_ref_vector &constraints,  obj_map<func_decl, args_t *> &synth_fun_args_decl);
            // for test using several sinult. model x
            bool solve_simult_model_x(func_decl_ref_vector &synth_funs, expr_ref_vector &constraints,  obj_map<func_decl, args_t *> &synth_fun_args_decl);

            void generate_coeff_decl(func_decl_ref_vector &synth_funs);
            void init_used_variables(func_decl_ref_vector const& synth_funs, expr_ref spec, func_decl_ref_vector &out);
            bool find_precondition(func_decl_ref_vector &synth_funs,  expr_ref &spec, model_ref mdl_for_coeff, expr_ref &result, model_ref mdl_for_x = 0);
            args_t *get_args_decl_for_synth_fun(func_decl *f);
            expr_ref generate_heuristic_concrete_coef_from_literals(synth_task &task);

            /* [+] Unrealizability Algorithm*/
            bool prove_unrealizability_with_mdl(expr_ref spec, model_ref & mdl);
            bool prove_unrealizability_simple(expr_ref spec);
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


            expr_ref_vector encode_asserts(func_decl_ref_vector & synth_funs, expr_ref_vector & constraints);
            expr_ref normalize(expr *e, func_decl_ref_vector &vars,  func_decl_ref_vector &eliminate, expr_ref_vector &exprs);

        private:
            bool completed_solving(func_decl_ref_vector &synth_funs, expr_ref_vector &constraints, expr_ref fun_body);

    };
}


#endif // MISYNTH_SOLVER_H
