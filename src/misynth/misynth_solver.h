#ifndef MISYNTH_SOLVER_H
#define MISYNTH_SOLVER_H

#include "cmd_context/cmd_context.h"


#include "smt_utils.h"

namespace misynth
{



    typedef expr_ref_vector invocation_operands;

    class misynth_solver
    {
        typedef obj_hashtable<expr> expr_set;
        typedef obj_map<func_decl, expr *> decl2expr_map;
        typedef obj_map<func_decl, expr_ref_vector> decl2expr_ref_vec;
        //obj_map<expr, expr_set*> m_hypmap;
    private:
        cmd_context &m_cmd;
        ast_manager &m;
        ref<solver> m_solver;

        smt_utils m_utils;
        arith_util m_arith;

        expr_ref m_constraints;


        vector<decl2expr_map> m_subst;

        vector<invocation_operands> m_ops;


    public:
        misynth_solver(cmd_context &cmd_ctx, ast_manager &m, solver *solver);

        bool solve(func_decl_ref_vector &synth_funs, expr_ref spec);

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

    };
}


#endif // MISYNTH_SOLVER_H
