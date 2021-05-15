/*++
Copyright (c) 2019

Module Name:

    synthlib_cmds.cpp

Abstract:
    Synth-Lib commands for SMT2 front-end.

Author:

    ---

Notes:

--*/
#include "misynth/synthlib_cmds.h"
#include "misynth/misynth_solver.h"

#include "cmd_context/cmd_context.h"

#include "ast/ast_pp.h"

#include "cmd_context/parametric_cmd.h"
#include "muz/base/fp_params.hpp"
#include "util/cancel_eh.h"
#include "util/scoped_ctrl_c.h"
#include "util/scoped_timer.h"
#include "util/trail.h"

#include "ast/for_each_expr.h"
#include "ast/rewriter/rewriter.h"
#include "ast/rewriter/rewriter_def.h"
#include <ast/rewriter/th_rewriter.h>
#include "muz/spacer/spacer_util.h"
#include "misynth/multi_abducer.h"
#include <iomanip>
#include <iostream>
#include <set>
#include <string>
#include <vector>

#define VERBOSE true
#define DEBUG true

namespace misynth
{

    class misynth_solver_context
    {
            cmd_context &m_cmd;
            ast_manager &m;
            expr_ref_vector m_constraints_list;
            func_decl_ref_vector m_synth_fun_list;

            obj_map<func_decl, func_decl *> m_synth_fun_sub_map;
            obj_map<func_decl, args_t *> m_synth_fun_args_decl;
            //obj_map<func_decl, args_t > m_synth_fun_args_decl2;
            params_ref m_params;
            ref<solver> m_solver;
            std::vector<args_t> args_vector;
            func_decl_ref_vector all_args_garbage_collection;
            synth_params m_synth_params;
        public:
            misynth_solver_context(cmd_context &cmd_ctx)
                : m_cmd(cmd_ctx)
                , m(cmd_ctx.m())
                , m_constraints_list(m)
                , m_synth_fun_list(m),
                  m_synth_fun_args_decl(),
                  all_args_garbage_collection(m)

            {
            }
            ~misynth_solver_context()
            {
                m_synth_fun_args_decl.reset();
                //args_vector.reset();
            }
            void register_synth_fun(func_decl *pred, svector<sorted_var> args)
            {
                if (DEBUG)
                {
                    std::cout << "register_synth_fun: " << pred->get_name() << "(" << pred->get_arity() << "):" << pred->get_range()->get_name() << std::endl;
                }

                func_decl_ref_vector args_decl(m);

                for (sorted_var it : args)
                {
                    args_decl.push_back(m.mk_const_decl(it.first, it.second));
                }

                args_vector.push_back(args_decl);
                // m_synth_fun_args_decl.insert_if_not_there(pred, &args_vector[args_vector.size() - 1]);
                // m_synth_fun_args_decl2.insert_if_not_there(pred, args_decl);
                m_synth_fun_list.push_back(pred);
            }

            void add_constraint(expr *constraint)
            {
                if (DEBUG)
                {
                    std::cout << "add_constraint: " << mk_ismt2_pp(constraint, m, 2) << std::endl;
                }
                if (m_synth_params.debug_abduction())
                {
                    multi_abducer abducer(m_cmd, m);
                    expr_ref_vector unordered_res(m);
                    decl2expr_map map;
                    if (m.is_implies(constraint))
                    {
                        app *ap = to_app(constraint);
                        // expr_ref unknown_pred(ap->get_arg(0), m);
                        expr_ref_vector unknown_pred(m);
                        app *premise = to_app(ap->get_arg(0));
                        unknown_pred.append(premise->get_num_args(), premise->get_args());
                        expr_ref conclusion(ap->get_arg(1), m);
                        func_decl_ref_vector synth_fun_args(m);

                        bool r = abducer.multi_abduce(unknown_pred,  expr_ref(m.mk_true(), m), conclusion, synth_fun_args, unordered_res, map);
                    }
                }
                m_constraints_list.push_back(constraint);
            }

            bool check_synth()
            {
                std::cout << "(check synth) " << std::endl;

                if (m_synth_fun_list.size() == 0)
                {
                    std::cerr << "None synth_fun is appeared " << std::endl;
                    return false;
                }

                //fill m_synth_fun_args_decl
                for (unsigned i = 0; i < m_synth_fun_list.size(); ++i)
                {
                    m_synth_fun_args_decl.insert_if_not_there(m_synth_fun_list.get(i), &args_vector[i]);
                }
                if (!m_solver)
                {
                    m_solver = m_cmd.get_solver_factory()(m, m_params, false, true, false, symbol::null);
                }
                misynth_solver tool(m_cmd, m, m_solver.get());
                if (m_synth_fun_list.size() > 1)
                {
                    //std::cerr << "Only one synth_fun is expected " << std::endl;
                    if (tool.multi_solve(m_synth_fun_list, m_constraints_list, m_synth_fun_args_decl))
                      std::cout << "###Complete "  << std::endl;
                    return false;
                }
                else
                {
                  if (tool.solve(m_synth_fun_list, m_constraints_list, m_synth_fun_args_decl))
                    std::cout << "###Complete "  << std::endl;
                  return false;
                }
            }

    };
}

struct misynth_context
{
    //smt_params                    m_fparams;
    params_ref m_params_ref;
    fp_params m_params;
    cmd_context &m_cmd;


    unsigned m_ref_count;
    scoped_ptr<misynth::misynth_solver_context> m_context;
    trail_stack<misynth_context> m_trail;

    /*fp_params const& get_params() {
        init();
        return m_context->get_params();
    }*/

    misynth_context(cmd_context &ctx)
        : m_params(m_params_ref)
        , m_cmd(ctx)
        , m_ref_count(0)
        , m_trail(*this)
    {
    }

    void inc_ref()
    {
        ++m_ref_count;
    }

    void dec_ref()
    {
        --m_ref_count;

        if (0 == m_ref_count)
        {
            dealloc(this);
        }
    }

    void init()
    {
        ast_manager &m = m_cmd.m();

        if (!m_context)
        {
            m_context = alloc(misynth::misynth_solver_context, m_cmd);
        }

        /*if (!m_decl_plugin) {
            symbol name("datalog_relation");
            if (m.has_plugin(name)) {
                m_decl_plugin = static_cast<datalog::dl_decl_plugin*>(m_cmd.m().get_plugin(m.mk_family_id(name)));
            }
            else {
                m_decl_plugin = alloc(datalog::dl_decl_plugin);
                m.register_plugin(symbol("datalog_relation"), m_decl_plugin);
            }
        }*/
    }

    void reset()
    {
        m_context = nullptr;
    }

    void push()
    {
        m_trail.push_scope();
        //dlctx().push();
    }

    void pop()
    {
        m_trail.pop_scope(1);
        // dlctx().pop();
    }

    misynth::misynth_solver_context &aectx()
    {
        init();
        return *m_context;
    }
};

/**
   \brief constraint command. It is also the owner of dl_context object.
*/
class sl_constraint_cmd : public cmd
{
        ref<misynth_context> m_aeval_ctx;
        mutable unsigned m_arg_idx;
        expr *m_t;

    public:
        sl_constraint_cmd(misynth_context *aeval_ctx)
            : cmd("constraint")
            , m_aeval_ctx(aeval_ctx)
            , m_arg_idx(0)
            , m_t(nullptr)
        {
        }
        char const *get_usage() const override
        {
            return "(constraint <expr>)";
        }
        char const *get_descr(cmd_context &ctx) const override
        {
            return "add a constraint";
        }
        unsigned get_arity() const override
        {
            return 1;
        }
        cmd_arg_kind next_arg_kind(cmd_context &ctx) const override
        {
            return CPK_EXPR;
        }
        void set_next_arg(cmd_context &ctx, expr *t) override
        {
            m_t = t;
            m_arg_idx++;
        }

        void reset(cmd_context &ctx) override
        {
            m_aeval_ctx->reset();
            prepare(ctx);
            m_t = nullptr;
        }
        void prepare(cmd_context &ctx) override
        {
            m_arg_idx = 0;
        }
        void finalize(cmd_context &ctx) override
        {
        }
        void execute(cmd_context &ctx) override
        {
            if (!m_t)
            {
                throw cmd_exception("invalid constraint, expected formula");
            }

            m_aeval_ctx->aectx().add_constraint(m_t);
        }
};

class sl_check_synth_cmd : public cmd
{
        ref<misynth_context> m_aeval_ctx;

    public:
        sl_check_synth_cmd(misynth_context *aeval_ctx)
            : cmd("check-synth")
            , m_aeval_ctx(aeval_ctx)
        {
        }

        char const *get_usage() const override
        {
            return "(check-synth)";
        }
        char const *get_descr(cmd_context &ctx) const override
        {
            return "initializes synthesis";
        }
        unsigned get_arity() const override
        {
            return 0;
        }

        void prepare(cmd_context &ctx) override
        {
            ctx.m(); // ensure manager is initialized.
        }
        cmd_arg_kind next_arg_kind(cmd_context &ctx) const override
        {
            return CPK_UINT;
        }

        void execute(cmd_context &ctx) override
        {
            m_aeval_ctx->aectx().check_synth();
        }
};

class sl_synth_fun_cmd : public cmd
{
        ref<misynth_context> m_aeval_ctx;
        unsigned m_arg_idx;
        mutable unsigned m_query_arg_idx;
        symbol m_fun_name;
        svector<sorted_var> m_sorted_var_list;

        sort *m_var_sort;

    public:
        sl_synth_fun_cmd(misynth_context *aeval_ctx)
            : cmd("synth-fun")
            , m_aeval_ctx(aeval_ctx)
        {
        }

        char const *get_usage() const override
        {
            return "<symbol> (<arg1 sort> ...) <representation>*";
        }
        char const *get_descr(cmd_context &ctx) const override
        {
            return "declare new relation";
        }
        unsigned get_arity() const override
        {
            return 3;
        }

        void prepare(cmd_context &ctx) override
        {
            ctx.m(); // ensure manager is initialized.
            m_arg_idx = 0;
            m_query_arg_idx = 0;
            m_sorted_var_list.reset();
        }
        cmd_arg_kind next_arg_kind(cmd_context &ctx) const override
        {
            switch (m_query_arg_idx++)
            {
                case 0:
                    return CPK_SYMBOL; // fun name

                case 1:
                    return CPK_SORTED_VAR_LIST; // arguments

                case 2:
                    return CPK_SORT; // sort of fun

                default:
                    return CPK_SORT; // sort of fun
            }
        }
        void set_next_arg(cmd_context &ctx, unsigned num, sorted_var const *slist) override
        {
            m_sorted_var_list.reset();
            m_sorted_var_list.append(num, slist);
            m_arg_idx++;
        }
        void set_next_arg(cmd_context &ctx, symbol const &s) override
        {
            if (m_arg_idx == 0)
            {
                m_fun_name = s;
            }
            else
            {
                //SASSERT(m_arg_idx>1);
                //m_kinds.push_back(s);
            }

            m_arg_idx++;
        }

        void set_next_arg(cmd_context &ctx, sort *s) override
        {
            m_var_sort = s;
            ++m_arg_idx;
        }

        void execute(cmd_context &ctx) override
        {
            if (m_arg_idx < 3)
            {
                throw cmd_exception("at least 3 arguments expected");
            }

            ast_manager &m = ctx.m();
            sort_ref_vector domain(m);

            for (unsigned int i = 0; i < m_sorted_var_list.size(); ++i)
            {
                domain.push_back(m_sorted_var_list[i].second);
            }

            func_decl_ref sf(
                m.mk_func_decl(m_fun_name, domain.size(), domain.c_ptr(), m_var_sort), m);
            ctx.insert(sf);
            m_aeval_ctx->aectx().register_synth_fun(sf, m_sorted_var_list);
        }
};

class sl_declare_var_cmd : public cmd
{
        unsigned m_arg_idx;
        symbol m_var_name;
        sort *m_var_sort;
        ref<misynth_context> m_aeval_ctx;

    public:
        sl_declare_var_cmd(misynth_context *sl_ctx)
            : cmd("declare-var")
            , m_arg_idx(0)
            , m_aeval_ctx(sl_ctx)
        {
        }

        char const *get_usage() const override
        {
            return "<symbol> <sort>";
        }
        char const *get_descr(cmd_context &ctx) const override
        {
            return "declare constant as variable";
        }
        unsigned get_arity() const override
        {
            return 2;
        }

        void prepare(cmd_context &ctx) override
        {
            ctx.m(); // ensure manager is initialized.
            m_arg_idx = 0;
        }
        cmd_arg_kind next_arg_kind(cmd_context &ctx) const override
        {
            SASSERT(m_arg_idx <= 1);

            if (m_arg_idx == 0)
            {
                return CPK_SYMBOL;
            }

            return CPK_SORT;
        }

        void set_next_arg(cmd_context &ctx, sort *s) override
        {
            m_var_sort = s;
            ++m_arg_idx;
        }

        void set_next_arg(cmd_context &ctx, symbol const &s) override
        {
            m_var_name = s;
            ++m_arg_idx;
        }

        void execute(cmd_context &ctx) override
        {
            ast_manager &m = ctx.m();
            func_decl_ref var(m.mk_func_decl(m_var_name, 0, static_cast<sort *const *>(nullptr), m_var_sort), m);
            ctx.insert(var);
            //m_aeval_ctx->dlctx().register_variable(var);
        }
};

static void install_synthlib_cmds_aux(cmd_context &ctx)
{
    misynth_context *sl_ctx = alloc(misynth_context, ctx);
    ctx.insert(alloc(sl_constraint_cmd, sl_ctx));
    ctx.insert(alloc(sl_check_synth_cmd, sl_ctx));
    ctx.insert(alloc(sl_synth_fun_cmd, sl_ctx));
    ctx.insert(alloc(sl_declare_var_cmd, sl_ctx));
}

void install_synthlib_cmds(cmd_context &ctx)
{
    install_synthlib_cmds_aux(ctx);
}
