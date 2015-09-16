/*++
Copyright (c) 2015 Microsoft Corporation

Module Name:

    special_relations_decl_plugin.h

Abstract:

    <abstract>

Author:

    Nikolaj Bjorner (nbjorner) 2015-15-9.

Revision History:

--*/
#ifndef SPECIAL_RELATIONS_DECL_PLUGIN_H_
#define SPECIAL_RELATIONS_DECL_PLUGIN_H_

#include"ast.h"



enum special_relations_op_kind {
    OP_SPECIAL_RELATION,
    LAST_SPECIAL_RELATIONS_OP
};

class special_relations_decl_plugin : public decl_plugin {
    symbol m_special_relation;
public:
    special_relations_decl_plugin();
    virtual ~special_relations_decl_plugin() {}

    virtual decl_plugin * mk_fresh() {
        return alloc(special_relations_decl_plugin);
    }

    
    virtual func_decl * mk_func_decl(decl_kind k, unsigned num_parameters, parameter const * parameters, 
                                     unsigned arity, sort * const * domain, sort * range);

    virtual void get_op_names(svector<builtin_name> & op_names, symbol const & logic);


    virtual sort * mk_sort(decl_kind k, unsigned num_parameters, parameter const * parameters) { return 0; }
};

enum sr_property {
    sr_transitive    = 0x01,
    sr_reflexive     = 0x02,
    sr_antisymmetric = 0x04,
    sr_lefttree      = 0x08,
    sr_righttree     = 0x10,    
};

class special_relations_util {
    ast_manager& m;
    family_id    m_fid;
public:
    special_relations_util(ast_manager& m) : m(m), m_fid(m.get_family_id("special-relations")) {}
    
    bool is_special_relation(func_decl* f) const { return is_decl_of(f, m_fid, OP_SPECIAL_RELATION); }
    bool is_special_relation(app* e) const { return is_special_relation(e->get_decl()); }
    sr_property get_property(func_decl* f) const;
    sr_property get_property(app* e) const { return get_property(e->get_decl()); }
};


#endif /* SPECIAL_RELATIONS_DECL_PLUGIN_H_ */

