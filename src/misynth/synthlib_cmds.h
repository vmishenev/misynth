/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    aeval_cmds.h

Abstract:
    Synth-Lib commands for SMT2 front-end.

Author:

    Nikolaj Bjorner (nbjorner) 2012-11-17

Notes:

--*/
#ifndef AEVAL_CMDS_H_
#define AEVAL_CMDS_H_

#include "ast/ast.h"

class cmd_context;
/*
struct dl_collected_cmds {
    expr_ref_vector m_rules;
    svector<symbol> m_names;
    expr_ref_vector m_queries;
    func_decl_ref_vector m_rels;
    dl_collected_cmds(ast_manager& m) : m_rules(m), m_queries(m), m_rels(m) {}    
};*/

void install_synthlib_cmds(cmd_context & ctx);
//void install_dl_collect_cmds(dl_collected_cmds& collected_cmds, cmd_context& ctx);


#endif
