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
#include "quant_hoist.h"
#include "tactic/goal2nlsat.h"
#include "expr2var.h"

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
        unsigned_vector        m_cached_asms_lim;
        nlsat::literal         m_is_true;
        nlsat::assignment      m_model;
        bool                   m_model_valid;
        vector<nlsat::var_vector>            m_bound;
        vector<nlsat::scoped_literal_vector> m_preds;
        svector<max_level>                   m_var_level;
        u_map<max_level>                     m_lit_level;
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
                    TRACE("qe", display(tout); );
                    save_model();
                    push();
                    break;
                case l_false:
                    if (0 == m_level) return l_false;
                    if (1 == m_level) return l_true;
                    project();
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
            if (!m_model_valid) {
                m_asms.append(m_cached_asms);
                return;
            }            
            unsave_model();
            if (level == 0) {
                return;
            }
            for (unsigned j = 0; j < m_preds[level - 1].size(); ++j) {
                add_literal(m_cached_asms, m_preds[level-1][j]);
            }
            m_asms.append(m_cached_asms);
            
            for (unsigned i = level + 1; i < m_preds.size(); i += 2) {
                for (unsigned j = 0; j < m_preds[i].size(); ++j) {
                    nlsat::literal l = m_preds[i][j];
                    max_level lvl = m_lit_level.find(l.var());
                    bool use = 
                        (lvl.m_fa == i && (lvl.m_ex == UINT_MAX || lvl.m_ex < level)) ||
                        (lvl.m_ex == i && (lvl.m_fa == UINT_MAX || lvl.m_fa < level));
                    if (use) {
                        add_literal(m_asms, l);
                    }
                }
            }
            save_model();
        }

        void add_literal(nlsat::literal_vector& lits, nlsat::literal l) {
            switch (m_solver.value(l)) {
            case l_true:
                lits.push_back(l);
                break;
            case l_false:
                lits.push_back(~l);
                break;
            default:
                UNREACHABLE();
                break;
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
            TRACE("qe", m_solver.display(tout, result.size(), result.c_ptr()););
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

        max_level mk_clause(unsigned n, nlsat::literal const* ls) {
            nlsat::literal_vector lits(n, ls);
            m_solver.mk_clause(n, lits.c_ptr());
            return get_level(n, ls);
        }

        max_level get_level(unsigned n, nlsat::literal const* ls) {
            max_level level;
            for (unsigned i = 0; i < n; ++i) {
                level.merge(get_level(ls[i]));
            }
            return level;
        }

        max_level get_level(nlsat::literal l) {
            max_level level;
            if (m_lit_level.find(l.var(), level)) {
                return level;
            }
            nlsat::var_vector vs;
            m_solver.vars(l, vs);
            for (unsigned i = 0; i < vs.size(); ++i) {
                level.merge(m_var_level[vs[i]]);
            }
            unsigned k = level.max();
            while (m_preds.size() <= k) {
                m_preds.push_back(nlsat::scoped_literal_vector(m_solver));
            }
            m_preds[k].push_back(l);
            m_lit_level.insert(l.var(), level);            
            return level;
        }
        
        void project() {
            TRACE("qe", display_assumptions(tout););
            if (!m_model_valid) {
                pop(1);
                return;
            }
            SASSERT(m_level >= 2);
            unsigned num_scopes;
            nlsat::scoped_literal_vector clause(m_solver);
            mbq(m_level-1, clause);            
            
            max_level level = mk_clause(clause.size(), clause.c_ptr());

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
            m_cached_asms_lim.push_back(m_cached_asms.size());
        }

        void pop(unsigned num_scopes) {
            clear_model();
            m_level -= num_scopes;
            m_cached_asms.shrink(m_cached_asms_lim[m_level]);
            m_cached_asms_lim.shrink(m_level);
        }

        void display(std::ostream& out) {
            display_preds(out);
            display_assumptions(out);
            m_solver.display(out);
        }

        void display_assumptions(std::ostream& out) {
            m_solver.display(out << "assumptions: ", m_asms.size(), m_asms.c_ptr());
            out << "\n";
        }

        void display_preds(std::ostream& out) {
            for (unsigned i = 0; i < m_preds.size(); ++i) {
                m_solver.display(out << i << ": ", m_preds[i].size(), m_preds[i].c_ptr());
                out << "\n";
            }
        }

        // expr -> nlsat::solver

        void hoist(expr_ref& fml) {
            quantifier_hoister hoist(m);
            vector<app_ref_vector> qvars;
            app_ref_vector vars(m);
            bool is_forall = false;   
            pred_abs abs(m);
            abs.get_free_vars(fml, vars);
            qvars.push_back(vars);
            vars.reset();
            hoist.pull_quantifier(is_forall, fml, vars);
            qvars.back().append(vars);            
            do {
                is_forall = !is_forall;
                vars.reset();
                hoist.pull_quantifier(is_forall, fml, vars);
                qvars.push_back(vars);
            }
            while (!vars.empty());
            SASSERT(qvars.back().empty()); 

            goal2nlsat g2s;
            expr2var a2b(m), t2x(m);
            expr_ref is_true(m);
            is_true = m.mk_fresh_const("is_true", m.mk_bool_sort());
            fml = m.mk_iff(is_true, fml);
            goal g(m);
            g.assert_expr(fml);
            g2s(g, m_params, m_solver, a2b, t2x);

            NOT_IMPLEMENTED_YET();
            TRACE("qe", tout << fml << "\n";);
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
            NOT_IMPLEMENTED_YET();

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


