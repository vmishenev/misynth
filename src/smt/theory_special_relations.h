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

#ifndef THEORY_SPECIAL_RELATIONS_H_
#define THEORY_SPECIAL_RELATIONS_H_

namespace smt {
    class theory_special_relations : public theory {

        class atom {
            bool_var    m_bvar;
            sr_property m_property;
            bool        m_true;
            theory_var  m_arg0;
            theory_var  m_arg1;
        public:
            atom(bool_var b, sr_property p, theory_var v1, theory_var v2):
                m_bvar(b), 
                m_property(p),
                m_true(true),
                m_arg0(v1),
                m_arg1(v2)
            {}
            bool_var var() const { return m_bvar;}
            sr_property get_property() const { return m_property; }
            bool get_phase() { return m_true; }
            void set_phase(bool b) { m_true = b; }
            theory_var v1() { return m_arg0; }
            theory_var v2() { return m_arg1; }
        };
        typedef u_map<atom*>     bool_var2atom;

        special_relations_util         m_util;
        ptr_vector<atom>               m_atoms;
        bool_var2atom                  m_bool_var2atom;

        //ptr_vector<atom>               m_asserted_atoms;   // set of asserted atoms
        //unsigned                       m_asserted_qhead;   
        //svector<scope>                 m_scopes;

    public:
        theory_special_relations(ast_manager& m);
        virtual ~theory_special_relations();
        
        virtual theory * mk_fresh(context * new_ctx);
        virtual bool internalize_atom(app * atom, bool gate_ctx);
        virtual bool internalize_term(app * term) { UNREACHABLE(); return false; }
        virtual void new_eq_eh(theory_var v1, theory_var v2);
        virtual void new_diseq_eh(theory_var v1, theory_var v2);
        virtual bool use_diseqs() const { return true; }
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
    };
}

#endif
