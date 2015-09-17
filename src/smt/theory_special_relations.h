/*++
Copyright (c) 2015 Microsoft Corporation

Module Name:

    theory_special_relations.h

Abstract:

    Special Relations theory plugin.

Author:

    Nikolaj Bjorner (nbjorner) 2015-9-16

Notes:

--*/

#include "special_relations_decl_plugin.h"
#include "smt_theory.h"
#include "theory_diff_logic.h"
#include "union_find.h"

#ifndef THEORY_SPECIAL_RELATIONS_H_
#define THEORY_SPECIAL_RELATIONS_H_

namespace smt {
    class theory_special_relations : public theory {


        struct relation;

        class atom {
            bool_var    m_bvar;
            relation&   m_relation;
            bool        m_true;
            theory_var  m_v1;
            theory_var  m_v2;
            edge_id     m_pos;
            edge_id     m_neg;
        public:
            atom(bool_var b, relation& r, theory_var v1, theory_var v2):
                m_bvar(b), 
                m_relation(r),
                m_true(true),
                m_v1(v1),
                m_v2(v2)
            {
                r.ensure_var(v1);
                r.ensure_var(v2);
                m_pos = r.m_graph.add_edge(v1, v2, s_integer(0), literal(b, false));
                m_neg = r.m_graph.add_edge(v2, v1, s_integer(1), literal(b, true));
            }
            bool_var var() const { return m_bvar;}
            relation& get_relation() const { return m_relation; }
            bool phase() { return m_true; }
            void set_phase(bool b) { m_true = b; }
            theory_var v1() { return m_v1; }
            theory_var v2() { return m_v2; }
            literal explanation() { return literal(m_bvar, !m_true); }
            bool enable() {
                edge_id edge = phase()?m_pos:m_neg;
                return m_relation.m_graph.enable_edge(edge);
            }
        };
        typedef ptr_vector<atom> atoms;

        struct scope {
            unsigned m_asserted_atoms_lim;
            unsigned m_asserted_qhead_old;
        };
        
        struct int_ext : public sidl_ext {
            typedef literal explanation;
        };

        typedef union_find<union_find_default_ctx> union_find_t;

        struct relation {
            sr_property           m_property;
            atoms                 m_asserted_atoms;   // set of asserted atoms
            unsigned              m_asserted_qhead;   
            svector<scope>        m_scopes;
            dl_graph<int_ext>     m_graph;
            union_find_default_ctx m_ufctx;
            union_find_t           m_uf;
            literal_vector         m_explanation;

            relation(sr_property p): m_property(p), m_uf(m_ufctx) {}

            void push();
            void pop(unsigned num_scopes);
            void ensure_var(theory_var v);
            bool new_eq_eh(literal l, theory_var v1, theory_var v2);
            void operator()(literal l) { m_explanation.push_back(l); }
        };

        class nc_functor {
            literal_vector m_antecedents;
            theory_special_relations& m_super;
        public:
            nc_functor(theory_special_relations& s) : m_super(s) {}
            void reset() { m_antecedents.reset(); }
            literal_vector const& get_lits() const { return m_antecedents; }
            void operator()(literal const & ex) {
                if (ex != null_literal) {
                    m_antecedents.push_back(ex);
                }
            }
            void new_edge(dl_var src, dl_var dst, unsigned num_edges, edge_id const* edges) {
                m_super.new_edge(src, dst, num_edges, edges);
            }
        };



        typedef u_map<atom*>     bool_var2atom;

        special_relations_util         m_util;
        atoms                          m_atoms;
        unsigned_vector                m_atoms_lim;
        obj_map<func_decl, relation*>  m_relations;
        bool_var2atom                  m_bool_var2atom;
        nc_functor                     m_nc_functor;

        void del_atoms(unsigned old_size);
        lbool final_check(relation& r);
        lbool final_check_po(relation& r);
        lbool final_check_lo(relation& r);
        lbool final_check_plo(relation& r);
        lbool final_check_to(relation& r, bool is_right);
        lbool propagate(relation& r);
        lbool enable(atom& a);
        bool  extract_equalities(relation& r);
        void set_neg_cycle_conflict(relation& r);
        lbool  propagate_plo(atom& a);
        theory_var mk_var(expr* e);
        void new_edge(dl_var src, dl_var dst, unsigned num_edges, edge_id const* edges) {}

    public:
        theory_special_relations(ast_manager& m);
        virtual ~theory_special_relations();
        
        virtual theory * mk_fresh(context * new_ctx);
        virtual bool internalize_atom(app * atom, bool gate_ctx);
        virtual bool internalize_term(app * term) { UNREACHABLE(); return false; }
        virtual void new_eq_eh(theory_var v1, theory_var v2);
        virtual void new_diseq_eh(theory_var v1, theory_var v2) {}
        virtual bool use_diseqs() const { return false; }
        virtual bool build_models() const { return true; }
        virtual final_check_status final_check_eh();
        virtual void reset_eh();
        virtual void assign_eh(bool_var v, bool is_true);
        virtual void init_search_eh();
        virtual void push_scope_eh();
        virtual void pop_scope_eh(unsigned num_scopes);
        virtual void restart_eh();
        virtual void collect_statistics(::statistics & st) const;
        virtual model_value_proc * mk_value(enode * n, model_generator & mg);
        virtual void init_model(model_generator & m);        
        virtual bool can_propagate() { return false; }
        virtual void propagate() {}
    };
}

#endif
