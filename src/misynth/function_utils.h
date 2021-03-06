#ifndef FUNCTION_UTILS_H
#define FUNCTION_UTILS_H

#include "cmd_context/cmd_context.h"
#include "misynth/smt_utils.h"

namespace misynth
{

    struct function_utils
    {
        cmd_context &m_cmd;
        ast_manager &m;
        arith_util m_arith;
        smt_utils m_utils;
        //params_ref m_params;
        //ref<solver> m_solver;

        function_utils(cmd_context &cmd_ctx, ast_manager &m)
            : m_cmd(cmd_ctx)
            , m(m)
            , m_arith(m)
            , m_utils(cmd_ctx, m)
        {
        }
        expr_ref generate_branch(func_decl_ref_vector coeff_decl_vec, func_decl_ref_vector &synth_fun_args, func_decl_ref_vector &synth_funs, model_ref mdl)
        {
            //func_decl_ref_vector *args_decl = get_args_decl_for_synth_fun(synth_funs.get(0));

            //get coeeficients
            expr_ref_vector  mult_terms(m);

            for (unsigned i = 0; i < coeff_decl_vec.size(); ++i)
            {

                expr_ref val = (*mdl)(m.mk_const(coeff_decl_vec.get(i)));



                if (m_arith.is_numeral(val) && !m_arith.is_zero(val))
                {
                    if (i == 0)
                    {
                        mult_terms.push_back(val);
                        continue;
                    }
                    else
                    {
                        mult_terms.push_back(m_arith.mk_mul(val, m.mk_const(synth_fun_args.get(i - 1))));
                    }
                }
                else
                {
                    //mult_terms.push_back(m_arith.mk_mul(m_arith.mk_int(0), m.mk_const(args_decl.get(i))));

                }
            }

            return m_arith.mk_add_simplify(mult_terms);
        }

        expr_ref generate_fun_macros(expr_ref body_fun, func_decl_ref_vector & synth_funs, func_decl_ref_vector args)
        {
            func_decl *fd = synth_funs.get(0);

            expr_ref_vector args_app(m);
            for (auto &fd : args)
            {
                args_app.push_back(m.mk_const(fd));
            }
            expr_ref fd_eq_body_fun(m.mk_eq(m.mk_app(fd, args_app.size(), args_app.c_ptr()), body_fun), m);
            expr_ref macros(m_utils.universal_quantified(fd_eq_body_fun, args));

            return macros;
        }
    };



}//amespace misynth
#endif // FUNCTION_UTILS_H
