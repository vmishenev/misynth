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
        nlsat::literal_vector  m_cached_asms;
        nlsat::literal         m_is_true;
        nlsat::assignment      m_model;
        bool                   m_model_valid;
        vector<nlsat::var_vector>            m_bound;
        vector<nlsat::scoped_literal_vector> m_preds;
        vector<svector<max_level> >          m_elevel;
        volatile bool          m_cancel;
        unsigned               m_level;
        stats                  m_stats;
        statistics             m_st;
        
        lbool check_sat() {
            while (true) {
                ++m_stats.m_num_rounds;
                check_cancel();
                init_assumptions();   
                clear_model();
                lbool res = m_solver.check(m_asms);
                switch (res) {
                case l_true:
                    TRACE("qe", display(tout); );
                    save_model();
                    push();
                    break;
                case l_false:
                    switch (m_level) {
                    case 0: return l_false;
                    case 1: return l_true;
                    default: project(); break;
                    }
                    break;
                case l_undef:
                    return res;
                }
            }
            return l_undef;
        }
        
        void init_assumptions() {
            unsigned level = m_level;
            m_asms.reset();
            m_asms.push_back(is_exists()?m_is_true:~m_is_true);
            if (level > m_preds.size()) {
                level = m_preds.size();
            }
            if (level == 0) {
                return;
            }
            if (!m_model_valid) {
                m_asms.append(m_cached_asms);
                return;
            }            
            unsave_model();
            for (unsigned j = 0; j < m_preds[level - 1].size(); ++j) {
                nlsat::literal l = m_preds[level-1][j];
                switch (m_solver.value(l)) {
                case l_true:
                    m_cached_asms.push_back(l);
                    break;
                case l_false:
                    m_cached_asms.push_back(~l);
                    break;
                default:
                    UNREACHABLE();
                    break;
                }
            }
            m_asms.append(m_cached_asms);
            
            for (unsigned i = level + 1; i < m_preds.size(); i += 2) {
                for (unsigned j = 0; j < m_preds[i].size(); ++j) {
                    nlsat::literal l = m_preds[i][j];
                    max_level lvl = m_elevel[i][j];
                    bool use = 
                        (lvl.m_fa == i && (lvl.m_ex == UINT_MAX || lvl.m_ex < level)) ||
                        (lvl.m_ex == i && (lvl.m_fa == UINT_MAX || lvl.m_fa < level));
                    if (use) {
                        switch (m_solver.value(l)) {
                        case l_true:
                            m_asms.push_back(l);
                            break;
                        case l_false:
                            m_asms.push_back(~l);
                            break;
                        default:
                            UNREACHABLE();
                            break;
                        }
                    }
                }
            }
        }
        
        void mbq(unsigned level, nlsat::scoped_literal_vector& result) {
            nlsat::var_vector vars;
            for (unsigned i = level; i < m_bound.size(); ++i) {
                vars.append(m_bound[i]);
            }
            unsave_model();
            nlsat::explain& ex = m_solver.get_explain();
            nlsat::scoped_literal_vector new_result(m_solver);
            new_result.append(m_asms.size(), m_asms.c_ptr());
            for (unsigned i = 0; i < vars.size(); ++i) {
                new_result.reset();
                ex.project(vars[i], result.size(), result.c_ptr(), new_result);
                result.swap(new_result);
            }
            for (unsigned i = 0; i < m_asms.size(); ++i) {
                result.set(i, ~result[i]);
            }
        }

        void save_model() {
            m_model.reset();
            m_model.swap(m_solver.get_assignment());
            m_model_valid = true;
        }

        void unsave_model() {
            SASSERT(m_model_valid);
            m_model.swap(m_solver.get_assignment());
            m_model_valid = false;
        }
         
        void clear_model() {
            m_model_valid = false;
            m_model.reset();
            m_model.swap(m_solver.get_assignment());
        }

        max_level get_level(unsigned n, nlsat::literal const* ls) {
            max_level level;

            return level;
        }

        max_level get_level(nlsat::literal l) {
            max_level level;

            return level;
        }
        
        void project() {
            if (!m_model_valid) {
                pop(1);
                return;
            }
            SASSERT(m_level >= 2);
            unsigned num_scopes;
            nlsat::scoped_literal_vector clause(m_solver);
            TRACE("qe", display(tout););
            TRACE("qe", display_assumptions(tout););
            mbq(m_level-1, clause);            
            TRACE("qe", display_assumptions(tout););
            
            max_level level = get_level(clause.size(), clause.c_ptr());

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
            nlsat::literal_vector lits(clause.size(), clause.c_ptr());
            m_solver.mk_clause(lits.size(), lits.c_ptr());
        }

        bool is_exists() const { return is_exists(m_level); }
        bool is_exists(unsigned level) const { return (level % 2) == 0; }        
        bool is_forall(unsigned level) const { return is_exists(level+1); }

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
            clear_model();
            m_level -= num_scopes;
        }

        void display(std::ostream& out) {
            display_assumptions(out);
            m_solver.display(out);
        }

        void display_assumptions(std::ostream& out) {

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


