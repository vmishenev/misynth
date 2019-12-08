#ifndef REWRITER_COEFFICIENTS_H
#define REWRITER_COEFFICIENTS_H

#include "cmd_context/cmd_context.h"
#include "ast/rewriter/rewriter.h"

struct invocations_rewriter_cfg : public default_rewriter_cfg {

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

#endif // REWRITER_COEFFICIENTS_H
