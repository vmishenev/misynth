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

    void theory_special_relations::relation::push() {
        m_scopes.push_back(scope());
        scope& s = m_scopes.back();
        s.m_asserted_atoms_lim = m_asserted_atoms.size();
        s.m_asserted_qhead_old = m_asserted_qhead;       
        m_graph.push();
        m_ufctx.get_trail_stack().push_scope();
    }

    void theory_special_relations::relation::pop(unsigned num_scopes) {
        unsigned new_lvl = m_scopes.size() - num_scopes;
        scope& s = m_scopes[new_lvl];
        m_asserted_atoms.shrink(s.m_asserted_atoms_lim);
        m_asserted_qhead = s.m_asserted_qhead_old;
        m_scopes.shrink(new_lvl);
        m_graph.pop(num_scopes);
        m_ufctx.get_trail_stack().pop_scope(num_scopes);
    }            

    void theory_special_relations::relation::ensure_var(theory_var v) {
        while ((unsigned)v > m_uf.mk_var());
        m_graph.init_var(v);
    }

    bool theory_special_relations::relation::new_eq_eh(literal l, theory_var v1, theory_var v2) {
        ensure_var(v1);
        ensure_var(v2);
        return 
            m_graph.enable_edge(m_graph.add_edge(v1, v2, s_integer(0), l)) &&
            m_graph.enable_edge(m_graph.add_edge(v2, v1, s_integer(0), l));            
    }

    theory_special_relations::theory_special_relations(ast_manager& m):
        theory(m.mk_family_id("special-relations")),
        m_util(m),
        m_nc_functor(*this)
    {}

    theory_special_relations::~theory_special_relations() {
        reset_eh();
    }
    
    theory * theory_special_relations::mk_fresh(context * new_ctx) {
        return alloc(theory_special_relations, new_ctx->get_manager());
    }

    bool theory_special_relations::internalize_atom(app * atm, bool gate_ctx) {
        SASSERT(m_util.is_special_relation(atm));
        relation* r = 0;
        if (!m_relations.find(atm->get_decl(), r)) {
            r = alloc(relation, m_util.get_property(atm)); 
            m_relations.insert(atm->get_decl(), r);
        }
        context& ctx = get_context();
        expr* arg0 = atm->get_arg(0);
        expr* arg1 = atm->get_arg(1);
        theory_var v0 = mk_var(arg0);
        theory_var v1 = mk_var(arg1);
        bool_var v = ctx.mk_bool_var(atm);
        ctx.set_var_theory(v, get_id());
        atom* a = alloc(atom, v, *r, v0, v1);
        m_atoms.push_back(a);
        m_bool_var2atom.insert(v, a);
        return true;
    }

    theory_var theory_special_relations::mk_var(expr* e) {
        context& ctx = get_context();
        if (!ctx.e_internalized(e)) {
            ctx.internalize(e, false);
        }        
        enode * n = ctx.get_enode(e);
        theory_var v = n->get_th_var(get_id());
        if (null_theory_var == v) {
            v = theory::mk_var(n);
            ctx.attach_th_var(n, this, v);
        }
        return v;
    }

    void theory_special_relations::new_eq_eh(theory_var v1, theory_var v2) {
        context& ctx = get_context();
        app_ref eq(get_manager());
        app* t1 = get_enode(v1)->get_owner();
        app* t2 = get_enode(v2)->get_owner();
        eq = get_manager().mk_eq(t1, t2);
        VERIFY(internalize_atom(eq, false));
        literal l(ctx.get_literal(eq));
        obj_map<func_decl, relation*>::iterator it = m_relations.begin(), end = m_relations.end();
        for (; !ctx.inconsistent() && it != end; ++it) {
            relation& r = *it->m_value;
            if (!r.new_eq_eh(l, v1, v2)) {
                set_neg_cycle_conflict(r);
                break;
            }
        }        
    }

    final_check_status theory_special_relations::final_check_eh() {
        obj_map<func_decl, relation*>::iterator it = m_relations.begin(), end = m_relations.end();
        lbool r = l_true;
        for (; it != end && r == l_true; ++it) {
            r = final_check(*it->m_value);
        }
        if (l_undef == r) {
            return FC_GIVEUP;
        }
        if (l_false == r) {
            return FC_DONE;
        }
        it = m_relations.begin();
        bool new_equality = false;
        for (; it != end; ++it) {
            if (extract_equalities(*it->m_value)) {
                new_equality = true;
            }
        }
        if (new_equality) {
            return FC_CONTINUE;
        }
        else {
            return FC_DONE;
        }
    }

    lbool theory_special_relations::final_check_lo(relation& r) {
        // all constraints are saturated by propagation.
        return l_true;
    }

    lbool theory_special_relations::final_check_po(relation& r) {
        NOT_IMPLEMENTED_YET();
        return l_undef;
    }

    lbool theory_special_relations::final_check_plo(relation& r) {
        //
        // ensure that !Rxy -> Ryx between connected components 
        // (where Rzx & Rzy or Rxz & Ryz for some z)
        // 
        lbool res = l_true;
        for (unsigned i = 0; res == l_true && i < r.m_asserted_atoms.size(); ++i) {
            atom& a = *r.m_asserted_atoms[i];
            if (!a.phase() && r.m_uf.find(a.v1()) == r.m_uf.find(a.v2())) {
                res = enable(a);
            }
        }        
        return res;
    }

    lbool theory_special_relations::final_check_to(relation& r, bool is_right) {
        NOT_IMPLEMENTED_YET();
        return l_undef;
    }

    lbool theory_special_relations::enable(atom& a) {
        if (!a.enable()) {
            relation& r = a.get_relation();
            set_neg_cycle_conflict(r);
            return l_false;
        }
        else {
            return l_true;
        }
    }

    void theory_special_relations::set_neg_cycle_conflict(relation& r) {
        m_nc_functor.reset();
        r.m_graph.traverse_neg_cycle2(false, m_nc_functor);
        literal_vector const& lits = m_nc_functor.get_lits();
        context & ctx = get_context(); 
        vector<parameter> params;   
        ctx.set_conflict(
            ctx.mk_justification(
                ext_theory_conflict_justification(
                    get_id(), ctx.get_region(), 
                    lits.size(), lits.c_ptr(), 0, 0, params.size(), params.c_ptr())));        
    }

    lbool theory_special_relations::final_check(relation& r) {
        lbool res = propagate(r);
        if (res != l_true) return res;
        switch (r.m_property) {
        case sr_lo:
            res = final_check_lo(r);
            break;
        case sr_po:
            res = final_check_po(r);
            break;
        case sr_plo:
            res = final_check_plo(r);
            break;
        case sr_rto:
            res = final_check_to(r, true);
            break;
        case sr_lto:
            res = final_check_to(r, false);            
            break;
        default:
            NOT_IMPLEMENTED_YET();
            res = l_undef;
        }        
        return res;
    }

    bool theory_special_relations::extract_equalities(relation& r) {
        bool new_eq = false;
        int_vector scc_id;
        u_map<unsigned> roots;
        context& ctx = get_context();
        r.m_graph.compute_zero_edge_scc(scc_id);
        for (unsigned i = 0, j = 0; i < scc_id.size(); ++i) {
            if (scc_id[i] == -1) {
                continue;
            }
            enode* n = get_enode(i);
            if (roots.find(scc_id[i], j)) {
                enode* m = get_enode(j);
                if (n->get_root() != m->get_root()) {
                    new_eq = true;
                    unsigned timestamp = r.m_graph.get_timestamp();
                    r.m_explanation.reset();
                    r.m_graph.find_shortest_zero_edge_path(i, j, timestamp, r);
                    r.m_graph.find_shortest_zero_edge_path(j, i, timestamp, r);
                    eq_justification js(ctx.mk_justification(theory_axiom_justification(get_id(), ctx.get_region(), r.m_explanation.size(), r.m_explanation.c_ptr())));
                    ctx.assign_eq(n, m, js);
                }
            }
            else {
                roots.insert(scc_id[i], i);
            }
        }
        return new_eq;
    }

    /*
      \brief Propagation for piecewise linear orders
    */
    lbool theory_special_relations::propagate_plo(atom& a) {
        lbool res = l_true;
        relation& r = a.get_relation();
        if (a.phase()) {
            r.m_uf.merge(a.v1(), a.v2());
            res = enable(a);
        }
        else if (r.m_uf.find(a.v1()) == r.m_uf.find(a.v2())) {
            res = enable(a);
        }
        return res;
    }

    lbool theory_special_relations::propagate(relation& r) {
        lbool res = l_true;
        while (res == l_true && r.m_asserted_qhead < r.m_asserted_atoms.size()) {
            atom& a = *r.m_asserted_atoms[r.m_asserted_qhead];
            switch (r.m_property) {
            case sr_lo:
                res = enable(a);
                break;
            case sr_plo:
                res = propagate_plo(a);
                break;
            default:
                if (a.phase()) {
                    res = enable(a);
                }
                break;
            }
            ++r.m_asserted_qhead;
        }
        return res;
    }

    void theory_special_relations::reset_eh() {
        obj_map<func_decl, relation*>::iterator it = m_relations.begin(), end = m_relations.end();
        for (; it != end; ++it) {
            dealloc(it->m_value);
        }
        m_relations.reset();    
        del_atoms(0);        
    }

    void theory_special_relations::assign_eh(bool_var v, bool is_true) {
        atom* a;
        VERIFY(m_bool_var2atom.find(v, a));
        a->set_phase(is_true);
        a->get_relation().m_asserted_atoms.push_back(a);
    }

    void theory_special_relations::init_search_eh() {
        // no-op
    }

    void theory_special_relations::push_scope_eh() {
        obj_map<func_decl, relation*>::iterator it = m_relations.begin(), end = m_relations.end();
        for (; it != end; ++it) {
            it->m_value->push();
        }
        m_atoms_lim.push_back(m_atoms.size());
    }

    void theory_special_relations::pop_scope_eh(unsigned num_scopes) {
        obj_map<func_decl, relation*>::iterator it = m_relations.begin(), end = m_relations.end();
        for (; it != end; ++it) {
            it->m_value->pop(num_scopes);
        }
        unsigned new_lvl = m_atoms_lim.size() - num_scopes;
        del_atoms(m_atoms_lim[new_lvl]);
    }

    void theory_special_relations::del_atoms(unsigned old_size) {
        atoms::iterator begin = m_atoms.begin() + old_size;
        atoms::iterator it    = m_atoms.end();
        while (it != begin) {
            --it;
            atom * a     = *it;
            m_bool_var2atom.erase(a->var());
            dealloc(a);
        }    
        m_atoms.shrink(old_size);
    }


    void theory_special_relations::restart_eh() {
        // no-op
    }

    void theory_special_relations::collect_statistics(::statistics & st) const {
        obj_map<func_decl, relation*>::iterator it = m_relations.begin(), end = m_relations.end();
        for (; it != end; ++it) {
            it->m_value->m_graph.collect_statistics(st);
        }
    }

    model_value_proc * theory_special_relations::mk_value(enode * n, model_generator & mg) {
        UNREACHABLE();
        return 0;
    }

    void theory_special_relations::init_model(model_generator & m) {
        obj_map<func_decl, relation*>::iterator it = m_relations.begin(), end = m_relations.end();
        for (; it != end; ++it) {
            switch (it->m_value->m_property) {
            case sr_lo:
                NOT_IMPLEMENTED_YET();
                break;
            case sr_plo:
                // pair of total assignment + equivalence class indicator.
                NOT_IMPLEMENTED_YET();
                break;
            case sr_rto:
            case sr_lto:
            case sr_po:
                NOT_IMPLEMENTED_YET();
                break;
            }
            
            // TODO ...
        }
    }
}
