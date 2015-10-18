/*++
Copyright (c) 2015 Microsoft Corporation

Module Name:

    nlqsat.cpp

Abstract:

    Quantifier Satisfiability Solver for nlsat

Author:

    Nikolaj Bjorner (nbjorner) 2015-10-17

Revision History:


--*/

#include "nlqsat.h"
#include "nlsat_solver.h"
#include "nlsat_explain.h"
#include "nlsat_assignment.h"
#include "qsat.h"

namespace qe {

    class nlqsat : public tactic {

        typedef unsigned_vector assumption_vector;

        struct stats {
            unsigned m_num_rounds;        
            stats() { reset(); }
            void reset() { memset(this, 0, sizeof(*this)); }            
        };

        
        ast_manager&           m;
        params_ref             m_params;
        nlsat::solver          m_solver;
        nlsat::literal_vector  m_asms;
        nlsat::literal         m_is_true;
        nlsat::assignment      m_model;
        bool                   m_model_valid;
        vector<nlsat::var_vector> m_bound;
        volatile bool          m_cancel;
        unsigned               m_level;
        stats                  m_stats;
        statistics             m_st;
        
        lbool check_sat() {
            while (true) {
                ++m_stats.m_num_rounds;
                check_cancel();
                init_assumptions();   
                lbool res = m_solver.check(m_asms);
                switch (res) {
                case l_true:
                    m_model.reset();
                    m_model.swap(m_solver.get_assignment());
                    m_model_valid = true;
                    TRACE("qe", display(tout); );
                    push();
                    break;
                case l_false:
                    switch (m_level) {
                    case 0: return l_false;
                    case 1: return l_true;
                    default: 
                        if (m_model_valid) {
                            project(); 
                        }
                        else {
                            pop(1);
                        }
                        break;
                    }
                    break;
                case l_undef:
                    return res;
                }
            }
            return l_undef;
        }

        void init_assumptions() {
            m_asms.reset();
            m_asms.push_back(is_exists(m_level)?m_is_true:~m_is_true);
            
        }
        
        void get_core(unsigned level) {
            
        }

        void mbq(unsigned level) {
            nlsat::var_vector vars;
            for (unsigned i = level; i < m_bound.size(); ++i) {
                vars.append(m_bound[i]);
            }
            m_model.swap(m_solver.get_assignment());

            m_solver.project(
        }

        void get_level(max_level& level) {
            
        }
        
        void project() {
            SASSERT(m_level >= 2);
            max_level level;
            unsigned num_scopes;
            TRACE("qe", display(tout););
            get_core(m_level);
            TRACE("qe", display_assumptions(tout););
            mbq(m_level-1);            
            TRACE("qe", display_assumptions(tout););
            
            get_level(level);

            if (level.max() == UINT_MAX) {
                num_scopes = 2*(m_level/2);
            }
            else {
                SASSERT(level.max() + 2 <= m_level);
                num_scopes = m_level - level.max();
                SASSERT(num_scopes >= 2);
            }
            
            TRACE("qe", tout << "backtrack: " << num_scopes << "\n";);
            pop(num_scopes);             
            m_solver.mk_clause(m_asms.size(), m_asms.c_ptr());
        }

        bool is_exists(unsigned level) const {
            return (level % 2) == 0;
        }
        
        bool is_forall(unsigned level) const {
            return is_exists(level+1);
        }

        void check_cancel() {
            if (m_cancel) {
                throw tactic_exception(TACTIC_CANCELED_MSG);
            }
        }

        void reset() {
            m_st.reset();        
            m_solver.collect_statistics(m_st);        
            //m_solver.reset();
            m_level = 0;
            m_cancel = false;
            m_model_valid = false;
        }

        void push() {
            m_level++;
        }

        void pop(unsigned num_scopes) {
            m_model_valid = false;
            m_level -= num_scopes;
        }

        void display(std::ostream& out) {
            display_assumptions(out);
            m_solver.display(out);
        }

        void dispaly_assumptions(std::ostream& out) {

        }

    public:
        nlqsat(ast_manager& m, params_ref const& p):
            m(m),
            m_params(p),
            m_solver(m.limit(), p),
            m_model(m_solver.am()),
            m_cancel(false),
            m_level(0)
        {}

        virtual ~nlqsat() {
        }

        void updt_params(params_ref const & p) {
            m_solver.updt_params(p);
        }
        
        void collect_param_descrs(param_descrs & r) {
        }

        
        void operator()(/* in */  goal_ref const & in, 
                        /* out */ goal_ref_buffer & result, 
                        /* out */ model_converter_ref & mc, 
                        /* out */ proof_converter_ref & pc,
                        /* out */ expr_dependency_ref & core) {
            tactic_report report("nlqsat-tactic", *in);

        }

        void collect_statistics(statistics & st) const {
            st.copy(m_st);
            st.update("qsat num rounds", m_stats.m_num_rounds); 
        }

        void reset_statistics() {
            m_stats.reset();
            m_solver.reset_statistics();
        }

        void cleanup() {
            reset();
            set_cancel(false);
        }
        
        void set_logic(symbol const & l) {
        }
        
        void set_progress_callback(progress_callback * callback) {
        }
        
        tactic * translate(ast_manager & m) {
            return alloc(nlqsat, m, m_params);
        }
        
        virtual void set_cancel(bool f) {
            m_solver.set_cancel(f);      
            m_cancel = f;
        }


        
    };
};

tactic * mk_nlqsat_tactic(ast_manager & m, params_ref const& p) {
    return alloc(qe::nlqsat, m, p);
}


