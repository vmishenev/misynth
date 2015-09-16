/*++
Copyright (c) 2015 Microsoft Corporation

Module Name:

    theory_special_relations.cpp

Abstract:

    Special Relations theory plugin.

Author:

    Nikolaj Bjorner (nbjorner) 2015-9-16

Notes:

--*/

#include "theory_special_relations.h"
#include "smt_context.h"


namespace smt {
    theory_special_relations::theory_special_relations(ast_manager& m):
        theory(m.mk_family_id("special-relations")),
        m_util(m)
    {}

    theory_special_relations::~theory_special_relations() {}
    
    theory * theory_special_relations::mk_fresh(context * new_ctx) {
        return alloc(theory_special_relations, new_ctx->get_manager());
    }

    bool theory_special_relations::internalize_atom(app * atm, bool gate_ctx) {
        SASSERT(m_util.is_special_relation(atm));
        context& ctx = get_context();
        expr* arg0 = atm->get_arg(0);
        expr* arg1 = atm->get_arg(1);
        if (!ctx.e_internalized(arg0)) 
            ctx.internalize(arg0, false);
        if (!ctx.e_internalized(arg1)) 
            ctx.internalize(arg1, false);
        enode * e0 = ctx.get_enode(arg0);
        enode * e1 = ctx.get_enode(arg1);
        if (null_theory_var == e0->get_th_var(get_id())) 
            ctx.attach_th_var(e0, this, theory::mk_var(e0));
        if (null_theory_var == e1->get_th_var(get_id()))
            ctx.attach_th_var(e1, this, theory::mk_var(e1));
        bool_var v = ctx.mk_bool_var(atm);
        ctx.set_var_theory(v, get_id());
        sr_property p = m_util.get_property(atm);
        atom* a = alloc(atom, v, p, e0->get_th_var(get_id()), e1->get_th_var(get_id()));
        m_atoms.push_back(a);
        m_bool_var2atom.insert(v, a);
        return true;
    }

    void theory_special_relations::new_eq_eh(theory_var v1, theory_var v2) {
        NOT_IMPLEMENTED_YET();
    }

    void theory_special_relations::new_diseq_eh(theory_var v1, theory_var v2) {
        NOT_IMPLEMENTED_YET();
    }

    final_check_status theory_special_relations::final_check_eh() {
        NOT_IMPLEMENTED_YET();
        return FC_DONE;
    }

    void theory_special_relations::reset_eh() {
        NOT_IMPLEMENTED_YET();
    }

    void theory_special_relations::assign_eh(bool_var v, bool is_true) {
        NOT_IMPLEMENTED_YET();
    }

    void theory_special_relations::init_search_eh() {
        NOT_IMPLEMENTED_YET();
    }

    void theory_special_relations::push_scope_eh() {
        NOT_IMPLEMENTED_YET();
    }

    void theory_special_relations::pop_scope_eh(unsigned num_scopes) {
        NOT_IMPLEMENTED_YET();
    }

    void theory_special_relations::restart_eh() {
        NOT_IMPLEMENTED_YET();
    }

    void theory_special_relations::collect_statistics(::statistics & st) const {
        NOT_IMPLEMENTED_YET();
    }

    model_value_proc * theory_special_relations::mk_value(enode * n, model_generator & mg) {
        NOT_IMPLEMENTED_YET();
        return 0;
    }

    void theory_special_relations::init_model(model_generator & m) {
        NOT_IMPLEMENTED_YET();
    }
}
