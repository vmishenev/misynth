/*++
Copyright (c) Vadim Mishenev

Module Name:

    aeval_cmds.h

Abstract:
    Non-linear multi abduction for one predicate symbol


Notes:


    I introduce new vars for operands arguments to flat .
    R(x1+x2) is replaced to R(y) /\ y=x1+x2

--*/
#ifndef MULTI_ABDUCER_H
#define MULTI_ABDUCER_H

#include "cmd_context/cmd_context.h"
#include "misynth/synth_params.hpp"
#include "smt_utils.h"


namespace misynth
{


    class multi_abducer
    {
        private:
            cmd_context &m_cmd;
            ast_manager &m;
            synth_params m_params;
            arith_util m_arith;
            smt_utils m_utils;

        public:
            multi_abducer(cmd_context &cmd_ctx, ast_manager &m);
            /*
             * simple abduction problem R(x) ∧ χ ⇒ C
             * QE (∀x. χ ⇒ C)
             * */

            expr_ref simple_abduce(expr_ref premise, expr_ref conclusion, func_decl_ref_vector vars);


            /*
             *
             * For one predicate symbol with different invocation arguments.
             *
             * */

            expr_ref nonlinear_abduce(vector<expr_ref_vector> &inv_args, expr_ref premise, expr_ref conclusion, func_decl_ref_vector &pattern);
            expr_ref to_flat(vector<expr_ref_vector> &inv_args, vector<func_decl_ref_vector> &new_decl_args);

        private:
            expr_ref  iso_decomp(expr_ref conclusion_model, expr_ref init_soln, expr_ref conclusion, vector<expr_ref_vector> &inv_args,
                                 vector<func_decl_ref_vector> &fresh_constant, func_decl_ref_vector &pattern, vector<func_decl_ref_vector> &decl_args);
            expr_ref  get_soln_according_to_model(model_ref mdl,   vector<func_decl_ref_vector> &fresh_constant,
                                                  func_decl_ref_vector &pattern);
            void generate_fresh_constant(vector<func_decl_ref_vector> &fresh_constant, vector<func_decl_ref_vector> &decl_args);
            //expr_ref get_phi_except_i(unsigned int i, expr_ref phi, vector<expr_ref_vector> &inv_args,  func_decl_ref_vector &pattern);
    };

}
#endif // MULTI_ABDUCER_H
