#include "human_print.h"

std::ostream &misynth::operator<<(std::ostream &out, const misynth::human_print &p) {
  if (p.m_ast == nullptr) {
      out << "null";
  }

  ast_manager &m  = p.m_m;
  const arith_util  &au = p.m_arith;
  ast* a = p.m_ast;

  if(is_app(a)) {

    // to_app(p.m_ast.get());
      app_ref ap(to_app(p.m_ast), p.m_m);
     if( m.is_or( ap->get_decl() ) ) {
      print(out, " \\/ ", ap, m, true );
     } else if( m.is_and( ap->get_decl() ) ) {
        print(out, " /\\ ", ap, m, true );
     } else if( m.is_eq( ap->get_decl() ) ) {
        print(out, " = ", ap, m );
     } else if( m.is_implies( ap->get_decl() ) ) {
        print(out, " => ", ap, m );
     } else if( m.is_not( ap->get_decl() ) ) {
        out << "not( "<< human_print(ap->get_arg(0), m, 0) << " )";
     } else if( au.is_lt( ap->get_decl() ) ) {
         print(out, " < ", ap, m );
     } else if( au.is_le( ap->get_decl() ) ) {
         print(out, " <= ", ap, m );
     } else if( au.is_gt( ap->get_decl() ) ) {
           print(out, " > ", ap, m );
     } else if( au.is_ge( ap->get_decl() ) ) {
           print(out, " >= ", ap, m );
     } else if( au.is_add( ap ) ) {
           print(out, " + ", ap, m );
     } else if( au.is_mul( ap ) ) {
           print(out, " * ", ap, m );
     } else if( !au.is_numeral( ap ) ) {
         out << ap->get_decl()->get_name();
         print(out, " , ", ap, m, true );
     } else {
         out <<  mk_ismt2_pp(p.m_ast,  p.m_m);
     }

  } else if( is_quantifier( a ) ) {
      quantifier *q = to_quantifier( a );
      out << "forall (";
      for( unsigned i = 0; i < q->get_num_decls(); ++i) {
        out << q->get_decl_name( i );
        if(q->get_num_decls() != i + 1) {
            out << ", ";
          }
      }
      out << ") (";
      out << human_print( q->get_expr(), m, 0 ) << ")";
  }  else {
      out <<  mk_ismt2_pp(p.m_ast,  p.m_m);
  }
  return out;
}

void misynth::print(std::ostream &out, const char *op, app *ap, ast_manager &m, bool is_braced ) {
  if( ap->get_num_args() == 0 ) return;
  if( is_braced ) out << "( ";
  for( unsigned i = 0; i < ap->get_num_args(); ++i) {
      out << human_print(ap->get_arg(i), m, 0);

      if(ap->get_num_args() != i + 1) {
          out << op;
        }

    }
  if( is_braced ) out << " )";
}
