#ifndef COLLECTOR_CONSTANTS_H
#define COLLECTOR_CONSTANTS_H

#include "ast/for_each_expr.h"

#include "ast/arith_decl_plugin.h"

namespace misynth {


typedef obj_hashtable<expr > expr_set;

struct collector_constant_proc {
    arith_util m_arith;
    ast_manager & m;
    expr_set &s;


    collector_constant_proc(expr_set &s, ast_manager & m): m_arith(m), m(m), s(s) {}
    void operator()(var const * n) { }
    void operator()(app const * n) {
        if(m_arith.is_numeral(n)) {
            s.insert(const_cast<expr*>(to_expr(n)));
        }
    }
    void operator()(quantifier const * n) { }

};





    void collect_consts(expr * e, expr_set &r, ast_manager & m) {
        collector_constant_proc p(r, m);
        quick_for_each_expr(p, e);

    }

}

#endif // COLLECTOR_CONSTANTS_H
