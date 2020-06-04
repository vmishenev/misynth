#ifndef MISYNTH_SYNTH_TASK_H
#define MISYNTH_SYNTH_TASK_H
#include "ast/decl_collector.h"
#include "cmd_context/cmd_context.h"
#include "smt_utils.h"

namespace misynth
{
    typedef func_decl_ref_vector  args_t;

    class synth_task
    {
        private:


            func_decl_ref_vector m_synth_funs;
            obj_map<func_decl, args_t *> m_synth_fun_args_decl;
            func_decl_ref_vector m_used_vars;
            expr_ref m_spec;
            expr_ref_vector m_constraints;

            void init_used_variables(ast_manager &m, func_decl_ref_vector & synth_funs, expr_ref spec)
            {
                decl_collector decls(m);
                decls.visit(spec);

                for (func_decl *fd :  decls.get_func_decls())
                {
                    if (!synth_funs.contains(fd))
                    {
                        m_used_vars.push_back(fd);
                    }
                }
            }


        public:
            synth_task(cmd_context &cmd_ctx, ast_manager &m) :
                m_synth_funs(m),
                m_synth_fun_args_decl(),
                m_used_vars(m),
                m_spec(m),
                m_constraints(m)
            {

            }

            synth_task(cmd_context &cmd_ctx, ast_manager &m, expr_ref_vector &constraints, func_decl_ref_vector &synth_funs,
                       obj_map<func_decl, args_t *> &synth_fun_args_decl) :
                m_synth_funs(synth_funs),
                m_synth_fun_args_decl(synth_fun_args_decl),
                m_used_vars(m),
                m_spec(m),
                m_constraints(constraints)
            {
                smt_utils utils(cmd_ctx, m);
                std::cout << "constraints " << constraints.size() << std::endl;
                std::cout << "constraints " << m_constraints.size() << std::endl;
                m_spec = utils.con_join(m_constraints);
                init_used_variables(m, m_synth_funs, m_spec);
            }
            expr_ref_vector &constarints()
            {
                return m_constraints;
            }
            expr_ref& spec()
            {
                return m_spec;
            }
            func_decl_ref_vector& synth_funs()
            {
                return m_synth_funs;
            }
            func_decl_ref_vector& used_vars()
            {
                return m_used_vars;
            }
            args_t &get_args_decl_for_synth_fun(func_decl * f)
            {
                return *m_synth_fun_args_decl[f];
            }

            synth_task(synth_task && other) noexcept :

                m_synth_funs(std::move(other.m_synth_funs)),
                m_synth_fun_args_decl(std::move(other.m_synth_fun_args_decl)),
                m_used_vars(std::move(other.m_used_vars)),
                m_spec(std::move(other.m_spec)),
                m_constraints(std::move(other.m_constraints))

            {

            }
            synth_task& operator=(synth_task && other) noexcept
            {
                m_constraints.swap(other.m_constraints);
                m_spec = std::move(other.m_spec);
                m_synth_funs.swap(other.m_synth_funs);
                m_synth_fun_args_decl = std::move(other.m_synth_fun_args_decl);
                m_used_vars.swap(other.m_used_vars);
                return *this;
            }

            synth_task & operator=(synth_task const & other) = delete;


    };
}

#endif // MISYNTH_SYNTH_TASK_H
