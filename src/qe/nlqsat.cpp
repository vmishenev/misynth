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
#include "goal2nlsat.h"
#include "expr2var.h"
#include "uint_set.h"
#include "ast_util.h"

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
        vector<nlsat::var_vector>            m_bound_rvars;
        vector<svector<nlsat::bool_var> >    m_bound_bvars;
        vector<nlsat::scoped_literal_vector> m_preds;
        svector<max_level>                   m_rvar2level;
        u_map<max_level>                     m_bvar2level;
        expr2var               m_a2b, m_t2x;
        volatile bool          m_cancel;
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
                    if (0 == level()) return l_false;
                    if (1 == level()) return l_true;
                    project();
                    break;
                case l_undef:
                    return res;
                }
            }
            return l_undef;
        }
        
        void init_assumptions() {
            unsigned lvl = level();
            m_asms.reset();
            m_asms.push_back(is_exists()?m_is_true:~m_is_true);
            if (lvl > m_preds.size()) {
                lvl = m_preds.size();
            }
            if (!m_model_valid) {
                m_asms.append(m_cached_asms);
                return;
            }            
            unsave_model();
            if (lvl == 0) {
                return;
            }
            for (unsigned j = 0; j < m_preds[lvl - 1].size(); ++j) {
                add_literal(m_cached_asms, m_preds[lvl-1][j]);
            }
            m_asms.append(m_cached_asms);
            
            for (unsigned i = lvl + 1; i < m_preds.size(); i += 2) {
                for (unsigned j = 0; j < m_preds[i].size(); ++j) {
                    nlsat::literal l = m_preds[i][j];
                    max_level lv = m_bvar2level.find(l.var());
                    bool use = 
                        (lv.m_fa == i && (lv.m_ex == UINT_MAX || lv.m_ex < lvl)) ||
                        (lv.m_ex == i && (lv.m_fa == UINT_MAX || lv.m_fa < lvl));
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
            uint_set bvars;
            for (unsigned i = level; i < m_bound_rvars.size(); ++i) {
                vars.append(m_bound_rvars[i]);
                for (unsigned j = 0; j < m_bound_bvars[i].size(); ++j) {
                    bvars.insert(m_bound_bvars[i][j]);
                }
            }
            bvars.insert(m_is_true.var());
            unsave_model();
            nlsat::explain& ex = m_solver.get_explain();
            nlsat::scoped_literal_vector new_result(m_solver);
            result.reset();
            // project quantified Boolean variables.
            for (unsigned i = 0; i < m_asms.size(); ++i) {
                nlsat::literal lit = m_asms[i];
                if (!bvars.contains(lit.var())) {
                    result.push_back(lit);
                }
            }
            // project quantified real variables.
            for (unsigned i = 0; i < vars.size(); ++i) {
                new_result.reset();
                ex.project(vars[i], result.size(), result.c_ptr(), new_result);
                result.swap(new_result);
            }
            for (unsigned i = 0; i < result.size(); ++i) {
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

        unsigned level() const { 
            return m_cached_asms_lim.size();
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
            if (m_bvar2level.find(l.var(), level)) {
                return level;
            }
            nlsat::var_vector vs;
            m_solver.vars(l, vs);
            for (unsigned i = 0; i < vs.size(); ++i) {
                level.merge(m_rvar2level[vs[i]]);
            }
            set_level(l, level);
            return level;
        }

        void set_level(nlsat::literal l, max_level const& level) {
            unsigned k = level.max();
            while (m_preds.size() <= k) {
                m_preds.push_back(nlsat::scoped_literal_vector(m_solver));
            }
            m_preds[k].push_back(l);
            m_bvar2level.insert(l.var(), level);            
        }
        
        void project() {
            TRACE("qe", display_assumptions(tout););
            if (!m_model_valid) {
                pop(1);
                return;
            }
            SASSERT(level() >= 2);
            unsigned num_scopes;
            nlsat::scoped_literal_vector clause(m_solver);
            mbq(level()-1, clause);            
            
            max_level clevel = mk_clause(clause.size(), clause.c_ptr());

            if (clevel.max() == UINT_MAX) {
                num_scopes = 2*(level()/2);
            }
            else {
                SASSERT(clevel.max() + 2 <= level());
                num_scopes = level() - clevel.max();
                SASSERT(num_scopes >= 2);
            }
            
            TRACE("qe", tout << "backtrack: " << num_scopes << "\n";);
            pop(num_scopes); 
        }

        bool is_exists() const { return is_exists(level()); }
        bool is_exists(unsigned level) const { return (level % 2) == 0; }        
        bool is_forall(unsigned level) const { return is_exists(level+1); }

        void check_cancel() {
            if (m_cancel) {
                throw tactic_exception(TACTIC_CANCELED_MSG);
            }
        }

        void reset() {
            //m_solver.reset();
            m_asms.reset();
            m_cached_asms.reset();
            m_cached_asms_lim.reset();
            m_is_true = nlsat::null_literal;
            m_model.reset();
            m_model_valid = false;
            m_bound_rvars.reset();
            m_bound_bvars.reset();
            m_preds.reset();
            m_rvar2level.reset();
            m_bvar2level.reset();
            m_t2x.reset();
            m_a2b.reset();
            m_cancel = false;
            m_st.reset();        
            m_solver.collect_statistics(m_st);
        }

        void push() {
            m_cached_asms_lim.push_back(m_cached_asms.size());
        }

        void pop(unsigned num_scopes) {
            clear_model();
            unsigned new_level = level() - num_scopes;
            m_cached_asms.shrink(m_cached_asms_lim[new_level]);
            m_cached_asms_lim.shrink(new_level);
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

            expr_ref is_true(m);
            is_true = m.mk_fresh_const("is_true", m.mk_bool_sort());
            fml = m.mk_iff(is_true, fml);
            goal g(m);
            g.assert_expr(fml);
            g2s(g, m_params, m_solver, m_a2b, m_t2x);

            // insert variables and their levels.
            for (unsigned i = 0; i < qvars.size(); ++i) {
                m_bound_bvars.push_back(svector<nlsat::bool_var>());
                m_bound_rvars.push_back(nlsat::var_vector());
                max_level lvl;
                if (is_exists(i)) lvl.m_ex = i; else lvl.m_fa = i;
                for (unsigned j = 0; j < qvars[i].size(); ++j) {
                    app* v = qvars[i][j].get();

                    if (m_a2b.is_var(v)) {
                        SASSERT(m.is_bool(v));
                        nlsat::bool_var b = m_a2b.to_var(v);
                        m_bound_bvars.back().push_back(b);
                        set_level(nlsat::literal(b, false), lvl);
                    }
                    else if (m_t2x.is_var(v)) {
                        nlsat::var w = m_t2x.to_var(v);
                        m_bound_rvars.back().push_back(w);
                        m_rvar2level.setx(w, lvl, max_level());
                    }
                }
            }
            m_is_true = nlsat::literal(m_a2b.to_var(is_true), false);
            // insert literals from arithmetical sub-formulas
            nlsat::atom_vector const& atoms = m_solver.get_atoms();
            for (unsigned i = 0; i < atoms.size(); ++i) {
                if (atoms[i]) {
                    get_level(nlsat::literal(i, false));
                }
            }
            TRACE("qe", tout << fml << "\n";);
        }

        
        // Return false if nlsat assigned noninteger value to an integer variable.
        // [copied from nlsat_tactic.cpp]
        bool mk_model(model_converter_ref & mc) {
            bool ok = true;
            model_ref md = alloc(model, m);
            arith_util util(m);
            expr2var::iterator it = m_t2x.begin(), end = m_t2x.end();
            for (; it != end; ++it) {
                nlsat::var x = it->m_value;
                expr * t = it->m_key;
                if (!is_uninterp_const(t))
                    continue;
                expr * v;
                try {
                    v = util.mk_numeral(m_solver.value(x), util.is_int(t));
                }
                catch (z3_error & ex) {
                    throw ex;
                }
                catch (z3_exception &) {
                    v = util.mk_to_int(util.mk_numeral(m_solver.value(x), false));
                    ok = false;
                }
                md->register_decl(to_app(t)->get_decl(), v);
            }
            it = m_a2b.begin(), end = m_a2b.end();
            for (; it != end; ++it) {
                expr * a = it->m_key;
                nlsat::bool_var b = it->m_value;
                if (a == 0 || !is_uninterp_const(a))
                    continue;
                lbool val = m_solver.bvalue(b);
                if (val == l_undef)
                    continue; // don't care
                md->register_decl(to_app(a)->get_decl(), val == l_true ? m.mk_true() : m.mk_false());
            }
            mc = model2model_converter(md.get());
            return ok;
        }

    public:
        nlqsat(ast_manager& m, params_ref const& p):
            m(m),
            m_params(p),
            m_solver(m.limit(), p),
            m_model(m_solver.am()),
            m_a2b(m),
            m_t2x(m),
            m_cancel(false)
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

            ptr_vector<expr> fmls;
            expr_ref fml(m);
            mc = 0; pc = 0; core = 0;
            in->get_formulas(fmls);
            fml = mk_and(m, fmls.size(), fmls.c_ptr());
            
            // for now:
            // fail if cores.  (TBD)
            // fail if proofs. (TBD)
                            
            reset();
            TRACE("qe", tout << fml << "\n";);
            hoist(fml);
            TRACE("qe", tout << "ex: " << fml << "\n";);
            lbool is_sat = check_sat();
            
            switch (is_sat) {
            case l_false:
                in->reset();
                in->inc_depth();
                in->assert_expr(m.mk_false());                
                result.push_back(in.get());
                break;
            case l_true:
                in->reset();
                in->inc_depth();
                result.push_back(in.get());
                if (in->models_enabled()) {
                    VERIFY(mk_model(mc));
                }
                break;
            case l_undef:
                result.push_back(in.get());
                std::string s = "search failed";
                throw tactic_exception(s.c_str()); 
            }        
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


