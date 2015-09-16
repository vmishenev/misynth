/*++
Copyright (c) 2015 Microsoft Corporation

Module Name:

    special_relations_decl_plugin.cpp

Abstract:

    <abstract>

Author:

    Nikolaj Bjorner (nbjorner) 2015-15-9.

Revision History:

--*/

#include<sstream>
#include"ast.h"
#include"special_relations_decl_plugin.h"



special_relations_decl_plugin::special_relations_decl_plugin():
    m_special_relation("special-relation")
{}
    
func_decl * special_relations_decl_plugin::mk_func_decl(
    decl_kind k, unsigned num_parameters, parameter const * parameters, 
    unsigned arity, sort * const * domain, sort * range)    
{
    SASSERT(k == OP_SPECIAL_RELATION);
    if (arity != 2) {
        m_manager->raise_exception("special relations should have arity 2");
        return 0;
    }
    if (domain[0] != domain[1]) {
        m_manager->raise_exception("argument sort missmatch");
        return 0;
    }
    func_decl_info info(m_family_id, k, num_parameters, parameters);
    return m_manager->mk_func_decl(m_special_relation, arity, domain, m_manager->mk_bool_sort(), info);
}

void special_relations_decl_plugin::get_op_names(svector<builtin_name> & op_names, symbol const & logic) {
    if (logic == symbol::null) {
        op_names.push_back(builtin_name("special-relation", OP_SPECIAL_RELATION));
    }
}

sr_property special_relations_util::get_property(func_decl* f) const {
    unsigned p = 0;
    unsigned sz = f->get_num_parameters();
    for (unsigned i = 0; i < sz; ++i) {
        parameter const& pa = f->get_parameter(i);
        if (!pa.is_symbol()) {
            m.raise_exception("Unexpected non-symbol parameter to special relation");
        }
        symbol const& s = pa.get_symbol();
        if (symbol("transitive") == s) {
            p |= sr_transitive;
        }
        else if (symbol("reflexive") == s) {
            p |= sr_reflexive;
        }
        else if (symbol("antisymmetric") == s) {
            p |= sr_antisymmetric;
        }
        else if (symbol("lefttree") == s) {
            p |= sr_lefttree;
        }
        else if (symbol("rightttree") == s) {
            p |= sr_righttree;
        }
        else {
            std::ostringstream strm;
            strm << s << " was not recognized as a special relations attribute";
            m.raise_exception(strm.str().c_str());
        }
    }
    return (sr_property)p;
}
