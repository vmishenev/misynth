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
#include "tseitin_cnf_tactic.h"

namespace qe {

    enum qsat_mode_t {
        qsat_t,
        elim_t,
        interp_t
    };

    class nlqsat : public tactic {

        typedef unsigned_vector assumption_vector;

        struct stats {
            unsigned m_num_rounds;        
            stats() { reset(); }
            void reset() { memset(this, 0, sizeof(*this)); }            
        };
        
        ast_manager&           m;
        qsat_mode_t            m_mode;
        params_ref             m_params;
        nlsat::solver          m_solver;
        tactic_ref             m_nftactic;
        nlsat::literal_vector  m_asms;
        nlsat::literal_vector  m_cached_asms;
        unsigned_vector        m_cached_asms_lim;
        nlsat::literal         m_is_true;
        nlsat::assignment      m_rmodel;        
        svector<lbool>         m_bmodel;
        nlsat::assignment      m_rmodel0;        
        svector<lbool>         m_bmodel0;
        bool                   m_valid_model;
        vector<nlsat::var_vector>            m_bound_rvars;
        vector<svector<nlsat::bool_var> >    m_bound_bvars;
        vector<nlsat::scoped_literal_vector> m_preds;
        svector<max_level>                   m_rvar2level;
        u_map<max_level>                     m_bvar2level;
        expr2var                             m_a2b, m_t2x;
        u_map<expr*>                         m_b2a, m_x2t;
        volatile bool                        m_cancel;
        stats                                m_stats;
        statistics                           m_st;
        obj_hashtable<expr>                  m_free_vars;
        expr_ref_vector                      m_answer;
        nlsat::literal_vector                m_assumptions;
        u_map<expr*>                         m_asm2fml;
        expr_ref_vector                      m_trail;
        
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
                    if (1 == level() && m_mode == qsat_t) return l_true;
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
            m_asms.append(m_assumptions);
            TRACE("qe", tout << "model valid: " << m_valid_model << " level: " << lvl << " "; 
                  display_assumptions(tout););

            if (!m_valid_model) {
                m_asms.append(m_cached_asms);
                return;
            }            
            unsave_model();
            if (lvl == 0) {
                SASSERT(m_cached_asms.empty());
                return;
            }
            if (lvl <= m_preds.size()) {
                for (unsigned j = 0; j < m_preds[lvl - 1].size(); ++j) {
                    add_literal(m_cached_asms, m_preds[lvl - 1][j]);
                }
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
            TRACE("qe", display(tout););
            save_model();
        }

        void add_literal(nlsat::literal_vector& lits, nlsat::literal l) {
            lbool r = m_solver.value(l);
            TRACE("qe", m_solver.display(tout, l); tout << " := " << r << "\n";);
            switch (r) {
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

        template<class S, class T>
        void insert_set(S& set, T const& vec) {
            for (unsigned i = 0; i < vec.size(); ++i) {
                set.insert(vec[i]);
            }
        }
        
        void mbp(unsigned level, nlsat::scoped_literal_vector& result) {
            nlsat::var_vector vars;
            uint_set fvars;
            for (unsigned i = 0; i < m_bound_rvars.size(); ++i) {
                if (i < level) {
                    insert_set(fvars, m_bound_bvars[i]);
                }
                else {
                    vars.append(m_bound_rvars[i]);
                }
            }
            
            // 
            // Also project auxiliary variables from clausification.
            // 
            unsave_model();
            nlsat::explain& ex = m_solver.get_explain();
            nlsat::scoped_literal_vector new_result(m_solver);
            result.reset();
            // project quantified Boolean variables.
            for (unsigned i = 0; i < m_asms.size(); ++i) {
                nlsat::literal lit = m_asms[i];
                if (!m_b2a.contains(lit.var()) || fvars.contains(lit.var())) {
                    result.push_back(lit);
                }
            }
            TRACE("qe", m_solver.display(tout, result.size(), result.c_ptr()); tout << "\n";);
            // project quantified real variables.
            // They are sorted by size, so we project the largest variables first to avoid 
            // renaming variables. 
            for (unsigned i = vars.size(); i > 0;) {
                --i;
                new_result.reset();
                ex.project(vars[i], result.size(), result.c_ptr(), new_result);
                result.swap(new_result);
            }
            for (unsigned i = 0; i < result.size(); ++i) {
                result.set(i, ~result[i]);
            }
            TRACE("qe", m_solver.display(tout, result.size(), result.c_ptr()); tout << "\n";);
        }

        void save_model() {
            m_solver.get_rvalues(m_rmodel);
            m_solver.get_bvalues(m_bmodel);
            m_valid_model = true;
            if (is_exists(level())) {
                m_rmodel0.copy(m_rmodel);
                m_bmodel0.reset();
                m_bmodel0.append(m_bmodel);
            }
        }

        void unsave_model() {
            SASSERT(m_valid_model);
            m_solver.set_rvalues(m_rmodel);
            m_solver.set_bvalues(m_bmodel);
        }
         
        void clear_model() {
            m_valid_model = false;
            m_rmodel.reset();
            m_bmodel.reset();
            m_solver.set_rvalues(m_rmodel);
        }

        unsigned level() const { 
            return m_cached_asms_lim.size();
        }

        max_level mk_clause(unsigned n, nlsat::literal const* ls) {
            nlsat::literal_vector lits(n, ls);
            if (lits.empty()) {
                lits.push_back(~m_solver.mk_true()); 
            }
            m_solver.mk_clause(lits.size(), lits.c_ptr());
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
            TRACE("qe", m_solver.display(tout, l); tout << ": " << level << "\n";);
        }
        
        void project() {
            TRACE("qe", display_assumptions(tout););
            if (!m_valid_model) {
                pop(1);
                return;
            }
            if (m_mode == elim_t) {
                project_qe();
                return;
            }
            SASSERT(level() >= 2);
            unsigned num_scopes;
            nlsat::scoped_literal_vector clause(m_solver);
            mbp(level()-1, clause);            
            
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

        void project_qe() {
            SASSERT(level() >= 1 && m_mode == elim_t && m_valid_model);
            nlsat::scoped_literal_vector clause(m_solver);
            mbp(std::max(1u, level()-1), clause);            
            
            expr_ref fml(m);
            clause2fml(clause, fml);
            TRACE("qe", tout << level() << ": " << fml << "\n";);
            if (level() == 1) {
                m_answer.push_back(fml);
            }

            add_assumption_literal(clause, fml);            
            mk_clause(clause.size(), clause.c_ptr());                            

            if (level() == 1) {
                pop(1);
            }
            else {
                pop(2);
            }
        }

        void clause2fml(nlsat::scoped_literal_vector const& clause, expr_ref& fml) {
            expr_ref_vector fmls(m);
            expr* t;
            nlsat2goal n2g(m);
            for (unsigned i = 0; i < clause.size(); ++i) {
                nlsat::literal l = clause[i];
                if (m_asm2fml.find(l.var(), t)) {
                    SASSERT(l.sign());
                    fmls.push_back(l.sign()?m.mk_not(t):t);
                }
                else {
                    fmls.push_back(n2g(m_solver, m_b2a, m_x2t, l));
                }
            }
            fml = mk_or(fmls);
        }

        void add_assumption_literal(nlsat::scoped_literal_vector& clause, expr* fml) {
            nlsat::bool_var b = m_solver.mk_bool_var();
            clause.push_back(nlsat::literal(b, true));
            m_assumptions.push_back(nlsat::literal(b, false));
            m_asm2fml.insert(b, fml);
            m_trail.push_back(fml);            
            m_bvar2level.insert(b, max_level());
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
            m_rmodel.reset();
            m_valid_model = false;
            m_bound_rvars.reset();
            m_bound_bvars.reset();
            m_preds.reset();
            m_rvar2level.reset();
            m_bvar2level.reset();
            m_t2x.reset();
            m_a2b.reset();
            m_b2a.reset();
            m_x2t.reset();
            m_cancel = false;
            m_st.reset();        
            m_solver.collect_statistics(m_st);
            m_free_vars.reset();
            m_answer.reset();
            m_assumptions.reset();
            m_asm2fml.reset();
            m_trail.reset();
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
            m_solver.display(out << "solver:\n");
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
            insert_set(m_free_vars, vars);
            qvars.push_back(vars); 
            vars.reset();    
            if (m_mode == elim_t) {
                is_forall = true;
                hoist.pull_quantifier(is_forall, fml, vars);
                qvars.push_back(vars);
            }
            else {
                hoist.pull_quantifier(is_forall, fml, vars);
                qvars.back().append(vars);            
            }
            do {
                is_forall = !is_forall;
                vars.reset();
                hoist.pull_quantifier(is_forall, fml, vars);
                qvars.push_back(vars);
            }
            while (!vars.empty());
            SASSERT(qvars.back().empty()); 
            init_expr2var(qvars);

            goal2nlsat g2s;

            expr_ref is_true(m), fml1(m), fml2(m);
            is_true = m.mk_fresh_const("is_true", m.mk_bool_sort());
            fml = m.mk_iff(is_true, fml);
            goal_ref g = alloc(goal, m);
            g->assert_expr(fml);
            proof_converter_ref pc;
            expr_dependency_ref core(m);
            model_converter_ref mc;
            goal_ref_buffer result;
            (*m_nftactic)(g, result, mc, pc, core);
            SASSERT(result.size() == 1);
            TRACE("qe", result[0]->display(tout););
            g2s(*result[0], m_params, m_solver, m_a2b, m_t2x);

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
            init_var2expr();
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

        void init_expr2var(vector<app_ref_vector> const& qvars) {
            for (unsigned i = 0; i < qvars.size(); ++i) {
                init_expr2var(qvars[i]);
            }
        }

        void init_expr2var(app_ref_vector const& qvars) {
            for (unsigned i = 0; i < qvars.size(); ++i) {
                app* v = qvars[i];
                if (m.is_bool(v)) {
                    m_a2b.insert(v, m_solver.mk_bool_var());
                }
                else {
                    // TODO: assert it is of type Real.
                    m_t2x.insert(v, m_solver.mk_var(false));
                }
            }
        }

        void init_var2expr() {
            expr2var::iterator it = m_t2x.begin(), end = m_t2x.end();
            for (; it != end; ++it) {
                m_x2t.insert(it->m_value, it->m_key);
            }
            it = m_a2b.begin(), end = m_a2b.end();
            for (; it != end; ++it) {
                m_b2a.insert(it->m_value, it->m_key);
            }
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
                if (!is_uninterp_const(t) || !m_free_vars.contains(t))
                    continue;
                expr * v;
                try {
                    v = util.mk_numeral(m_rmodel0.value(x), util.is_int(t));
                }
                catch (z3_error & ex) {
                    throw ex;
                }
                catch (z3_exception &) {
                    v = util.mk_to_int(util.mk_numeral(m_rmodel0.value(x), false));
                    ok = false;
                }
                md->register_decl(to_app(t)->get_decl(), v);
            }
            it = m_a2b.begin(), end = m_a2b.end();
            for (; it != end; ++it) {
                expr * a = it->m_key;
                nlsat::bool_var b = it->m_value;
                if (a == 0 || !is_uninterp_const(a) || b == m_is_true.var() || !m_free_vars.contains(a))
                    continue;
                lbool val = m_bmodel0.get(b, l_undef);
                if (val == l_undef)
                    continue; // don't care
                md->register_decl(to_app(a)->get_decl(), val == l_true ? m.mk_true() : m.mk_false());
            }
            mc = model2model_converter(md.get());
            return ok;
        }

    public:
        nlqsat(ast_manager& m, qsat_mode_t mode, params_ref const& p):
            m(m),
            m_mode(mode),
            m_params(p),
            m_solver(m.limit(), p),
            m_nftactic(0),
            m_rmodel(m_solver.am()),
            m_rmodel0(m_solver.am()),
            m_valid_model(false),
            m_a2b(m),
            m_t2x(m),
            m_cancel(false),
            m_answer(m),
            m_trail(m)
        {
            m_nftactic = mk_tseitin_cnf_tactic(m);
        }

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
            if (m_mode == elim_t) {
                fml = m.mk_not(fml);
            }                         
            reset();
            TRACE("qe", tout << fml << "\n";);
            hoist(fml);
            TRACE("qe", tout << "ex: " << fml << "\n";);
            lbool is_sat = check_sat();
            
            switch (is_sat) {
            case l_false:
                in->reset();
                in->inc_depth();
                if (m_mode == elim_t) {
                    fml = mk_and(m_answer);
                }
                else {
                    fml = m.mk_false();
                }
                in->assert_expr(fml);
                result.push_back(in.get());
                break;
            case l_true:
                SASSERT(m_mode == qsat_t);
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
            return alloc(nlqsat, m, m_mode, m_params);
        }
        
        virtual void set_cancel(bool f) {
            m_solver.set_cancel(f);      
            m_cancel = f;
        }

        lbool interpolate(expr* a, expr* b, app_ref_vector const& vars, expr_ref& result) {
            SASSERT(m_mode == interp_t);
            
            reset();
            app_ref enableA(m), enableB(m);
            expr_ref A(m), B(m), fml(m);
            expr_ref_vector fmls(m);
            
            enableA = m.mk_const(symbol("#A"), m.mk_bool_sort());
            enableB = m.mk_const(symbol("#B"), m.mk_bool_sort());
            A = m.mk_implies(enableA, m.mk_not(a));
            B = m.mk_implies(enableB, m.mk_not(b));
            fml = m.mk_and(A, B);
            hoist(fml);

            while (true) {
                m_mode = qsat_t;
                // enable B
                lbool is_sat = check_sat();

                switch (is_sat) {
                case l_undef:
                    return l_undef;
                case l_true:                    
                    break;
                case l_false:
                    result = mk_and(m_answer);
                    return l_true;
                }

                NOT_IMPLEMENTED_YET();
                // disable B, enable A

                m_mode = elim_t;
                // enforce the model of not B.
                // compute one clause that rules out this model.

                // disable A
                // add blocking clause to solver.
            }
        }
        
    };
};

tactic * mk_nlqsat_tactic(ast_manager & m, params_ref const& p) {
    return alloc(qe::nlqsat, m, qe::qsat_t, p);
}

tactic * mk_nlqe_tactic(ast_manager & m, params_ref const& p) {
    return alloc(qe::nlqsat, m, qe::elim_t, p);
}


