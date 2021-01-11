#ifndef HUMAN_PRINT_H
#define HUMAN_PRINT_H

#include "ast/ast_pp.h"
#include "ast/ast_pp.h"

#include <ostream>
namespace misynth
{
struct human_print {
    ast *              m_ast;
    ast_manager &      m_m;
    unsigned           m_indent;
    arith_util         m_arith;
    human_print(ast *t, ast_manager & m, unsigned indent = 0)
      : m_ast(t),
        m_m(m),
        m_indent(indent),
        m_arith(m)
    {

    }
};

void print(std::ostream& out, const char * op, app *ap, ast_manager &m, bool is_braced = false ) ;

std::ostream& operator<<(std::ostream& out, human_print const & p);
}
#endif // HUMAN_PRINT_H
