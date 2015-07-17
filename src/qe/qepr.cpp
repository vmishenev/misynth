/*++
Copyright (c) 2015 Microsoft Corporation

Module Name:

    qepr.h

Abstract:

    EPR symbol elimination routine

Author:

    Nikolaj Bjorner (nbjorner) 2015-7-16

Revision History:


--*/

#include "qepr.h"

#include "smt_kernel.h"
#include "qe_mbp.h"
#include "smt_params.h"
#include "ast_util.h"
#include "quant_hoist.h"
#include "ast_pp.h" 
#include "model_v2_pp.h"
#include "filter_model_converter.h"
#include "array_decl_plugin.h"
#include "expr_abstract.h"
#include "qsat.h"

namespace qe {


    class qepr : public tactic  {

        struct stats {
            unsigned m_num_predicates;
            unsigned m_num_rounds;        
            stats() { reset(); }
            void reset() { memset(this, 0, sizeof(*this)); }
        };

        ast_manager&               m;
        params_ref                 m_params;
        pred_abs                   m_pred_abs;
        smt_params                 m_smtp;
        model_ref                  m_model;
        volatile bool              m_cancel;
        statistics                 m_st;
        qe::mbp                    m_mbp;
        smt::kernel                m_fa;
        smt::kernel                m_ex;
        unsigned                   m_level;
        stats                      m_stats;
        expr_ref_vector            m_answer;
        app_ref_vector             m_free_vars;   // free variables
        app_ref_vector             m_bound_vars;  // universally bound variables
        func_decl_ref_vector       m_free_preds;  // predicates to project
        func_decl_ref_vector       m_bound_preds; // predicates to project


        lbool check_sat() {
            while (true) {
                ++m_stats.m_num_rounds;
                check_cancel();
                expr_ref_vector asms(m);
                get_assumptions(asms);
                smt::kernel& k = get_kernel(m_level);
                lbool res = k.check(asms);
                switch (res) {
                case l_true:
                    k.get_model(m_model);
                    TRACE("qe", k.display(tout); display(tout << "\n", *m_model.get()); display(tout, asms); );
                    push();
                    break;
                case l_false:
                    if (m_level == 0) {
                        return l_false;
                    }
                    if (m_model.get()) {
                        project(asms); 
                    }
                    else {
                        pop(1);
                    }
                    break;
                case l_undef:
                    return res;
                }
            }
            return l_undef;
        }

        void check_cancel() {
            if (m_cancel) {
                throw tactic_exception(TACTIC_CANCELED_MSG);
            }
        }

        void pop(unsigned num_scopes) {
            m_model.reset();
            m_pred_abs.pop(num_scopes);
            SASSERT(num_scopes <= m_level);
            m_level -= num_scopes;
        }

        void push() {
            m_pred_abs.push();
            ++m_level;
        }

        typedef obj_map<func_decl, ptr_vector<app> > pred2occs;

        void project(expr_ref_vector& core) {
            expr_ref fml(m);
            SASSERT(m_level > 0);
            get_core(core, m_level);
            TRACE("qe", display(tout); display(tout << "core\n", core););
            if (m_level == 1) {
                fml = negate_core(core);
                m_ex.assert_expr(fml);
                m_answer.push_back(fml);
                pop(1);
                return;
            }

            model& mdl = *m_model.get();

            pred2occs pos, neg;

            if (m_level == 2) {
                expr_ref_vector new_core(m);
                for (unsigned i = 0; i < core.size(); ++i) {
                    expr* e = core[i].get(), *ne;
                    if (is_bound_predicate(e)) {
                        add_predicate(pos, e);
                    }
                    else if (m.is_not(e, ne) && is_bound_predicate(ne)) {
                        add_predicate(neg, ne);
                    }
                    else {
                        new_core.push_back(e);
                    }
                }
                
                // remove m_bound_preds
                // retain disequalities that are required by bound_preds.
                // e.g, if Q(z) and !Q(u), then z != u
                // 

            }

            // m_level = 3:
            // just create negated core.

            
            fml = negate_core(core);
            m_ex.assert_expr(fml);
            m_fa.assert_expr(fml);
            m_level -= 2;
        }

        void add_predicate(pred2occs& map, expr* p) {
            // TBD
        }

        void get_core(expr_ref_vector& core, unsigned level) {
            smt::kernel& k = get_kernel(level);
            unsigned sz = k.get_unsat_core_size();
            core.reset();
            for (unsigned i = 0; i < sz; ++i) {
                core.push_back(k.get_unsat_core_expr(i));
            }
            m_pred_abs.mk_concrete(core);
            TRACE("qe", tout << "core: " << core << "\n"; k.display(tout); tout << "\n";);
        }

        void get_assumptions(expr_ref_vector& asms) {
            switch (m_level) {
            case 0:
                break;
            case 1: 
            case 3: {
                // extract equalities between free variables (and bound vars).
                // evaluation of free predicates
                app_ref_vector vars(m);
                vars.append(m_free_vars);
                vars.append(m_bound_vars);
                extract_equalities(vars);
                break;
            }
            case 2:
                // evaluation of m_preds
                break;
            default:
                UNREACHABLE();
                break;
            }
            m_pred_abs.get_assumptions(m_model.get(), asms);
        }

        /**
           \brief Create fresh equality atoms for each equality that holds in current model among vars.
         */
        void extract_equalities(app_ref_vector const& vars) {
            expr_ref_vector trail(m), defs(m);
            expr_ref eq(m), val(m), pred(m);
            obj_map<expr, expr*> val2var;
            expr* var;
            model& mdl = *m_model.get();
            for (unsigned i = 0; i < vars.size(); ++i) {
                VERIFY(mdl.eval(vars[i], val));
                if (val2var.find(val, var)) {
                    max_level level;
                    eq = m.mk_eq(var, vars[i]);
                    m_pred_abs.abstract_atoms(eq, level, defs);
                }
                else {
                    val2var.insert(val, vars[i]);
                    trail.push_back(val);
                }
            }
            for (unsigned j = 0; j < defs.size(); ++j) {
                SASSERT(m.is_eq(defs[j].get()));
                app* p = to_app(to_app(defs[j].get())->get_arg(0));
                mdl.register_decl(p->get_decl(), m.mk_true());
                m_fa.assert_expr(defs[j].get());
                m_ex.assert_expr(defs[j].get());
            }
        }
     
        smt::kernel& get_kernel(unsigned l) {
            return ((l % 2) == 0)?m_ex:m_fa;
        }

        smt::kernel const& get_kernel(unsigned l) const {
            return ((l % 2) == 0)?m_ex:m_fa;
        }

        expr_ref negate_core(expr_ref_vector& core) {
            expr_ref fml(m);
            app_ref_vector bound(m_bound_vars);
            m_mbp.solve(*m_model.get(), bound, core);
            fml = ::push_not(::mk_and(core));
            fml = mk_forall(m, bound.size(), bound.c_ptr(), fml);
            return fml;
        }

        void hoist(expr_ref& fml) {
            m_free_vars.reset();
            m_bound_vars.reset();
            quantifier_hoister hoist(m);
            m_pred_abs.get_free_vars(fml, m_free_vars);
            hoist.pull_quantifier(true, fml, m_bound_vars);
            set_level(0, m_free_vars);
            set_level(2, m_bound_vars);
            collect_predicates(fml);
        }

        void set_level(unsigned l, app_ref_vector const& vars) {
            max_level lvl;
            lvl.m_ex = l;
            for (unsigned i = 0; i < vars.size(); ++i) {
                m_pred_abs.set_expr_level(vars[i], lvl);
            }
        }

        /**
           \brief Collect predicates to eliminate.
         */
        void collect_predicates(expr* fml) {
            m_free_preds.reset();
            m_bound_preds.reset();
            ast_fast_mark1 mark;
            ptr_vector<expr> todo;
            todo.push_back(fml);
            while (!todo.empty()) {
                expr* e = todo.back();
                if (mark.is_marked(e) || is_var(e)) continue;
                mark.mark(e);
                if (is_quantifier(e)) {
                    todo.push_back(to_quantifier(e)->get_expr());
                    continue;
                }
                app* a = to_app(e);
                func_decl* d = a->get_decl();
                if (!mark.is_marked(d) && is_bound_predicate(d)) {
                    m_bound_preds.push_back(d);
                }
                if (!mark.is_marked(d) && is_free_predicate(d)) {
                    m_free_preds.push_back(d);
                }
                mark.mark(d);
                for (unsigned i = 0; i < a->get_num_args(); ++i) {
                    todo.push_back(a->get_arg(i));
                }                    
            }            
        }

        bool is_bound_predicate(expr* e) {
            return 
                is_app(e) && 
                is_bound_predicate(to_app(e)->get_decl());
        }

        bool is_bound_predicate(func_decl* d) {
            return 
                is_predicate(m, d) && 
                d->get_family_id() == null_family_id &&
                to_eliminate(d->get_name());
        }

        bool is_free_predicate(func_decl* d) {
            return 
                is_predicate(m, d) && 
                d->get_family_id() == null_family_id && 
                !to_eliminate(d->get_name());
        }
        
        /*
          \brief at this point use and trust underscores to identify predicates to eliminate.
         */
        bool to_eliminate(symbol const& s) {
            return !s.is_numerical() && s.bare_str() && s.bare_str()[0] == '_';
        }

        void display(std::ostream& out) const {
            // TBD
        }

        void display(std::ostream& out, model& model) const {
            display(out);
            model_v2_pp(out, model);
        }

        void display(std::ostream& out, expr_ref_vector const& asms) const {
            // TBD
        }

    public:

        qepr(ast_manager& m, params_ref const& p): 
            m(m),            
            m_params(p),
            m_pred_abs(m),
            m_cancel(false),
            m_mbp(m),
            m_fa(m, m_smtp),
            m_ex(m, m_smtp),
            m_answer(m),
            m_free_preds(m),
            m_bound_preds(m),
            m_free_vars(m),
            m_bound_vars(m)
        {
            m_smtp.m_model = true;
            m_smtp.m_relevancy_lvl = 0;
        }

        virtual ~qepr() {
            reset();
        }

        virtual void set_cancel(bool f) {
            m_fa.set_cancel(f);        
            m_ex.set_cancel(f);        
            m_cancel = f;
        }
        
        virtual tactic* translate(ast_manager& m) {
            return alloc(qepr, m, m_params);
        }
        
        virtual void set_progress_callback(progress_callback* cb) {
        }

        void set_logic(symbol const& l) {
        }

        void cleanup() {
            reset();
            set_cancel(false);
        }

        void collect_statistics(statistics & st) const {
            st.copy(m_st);
            st.update("qsat num predicates", m_stats.m_num_predicates);
            st.update("qsat num rounds", m_stats.m_num_rounds); 
        }
        
        void reset_statistics() {
            m_stats.reset();
            m_fa.reset_statistics();
            m_ex.reset_statistics();        
        }

        virtual void operator()(
            /* in */  goal_ref const & in, 
            /* out */ goal_ref_buffer & result, 
            /* out */ model_converter_ref & mc, 
            /* out */ proof_converter_ref & pc,
            /* out */ expr_dependency_ref & core) {
            tactic_report report("qsat-tactic", *in);
            ptr_vector<expr> fmls;
            expr_ref fml(m);
            max_level level;
            mc = 0; pc = 0; core = 0;
            in->get_formulas(fmls);
            fml = mk_and(m, fmls.size(), fmls.c_ptr());
            fml = push_not(fml);

            // TBD
        }

        virtual void reset() {
            m_level = 0;
            m_answer.reset();
            m_free_vars.reset();
            m_bound_vars.reset();
            m_free_preds.reset();
            m_bound_preds.reset();
            m_model = 0;
            m_pred_abs.reset();
            m_st.reset();        
            m_fa.collect_statistics(m_st);
            m_ex.collect_statistics(m_st);
            m_fa.reset();
            m_ex.reset();        
            m_cancel = false;            
        }

    };

}


tactic * mk_epr_qe_tactic(ast_manager& m, params_ref const& p) {
    qe::qepr* qs = alloc(qe::qepr, m, p);
    return qs;
}

#if 0

            select_map::iterator it = selects.begin(), end = selects.end();
            for (; it != end; ++it) {
                partition_selects(it->m_value);
            }


        void partition_selects(ptr_vector<app> const& ps) {
            svector<bool> is_true;
            
            expr_ref val(m), fml(m), rhs(m);
            app_ref p(m);
            for (unsigned i = 0; i < ps.size(); ++i) {
                VERIFY (q.m_model->eval(ps[i], val));
                is_true.push_back(m.is_true(val));
            }
            for (unsigned i = 0; i < ps.size(); ++i) {
                app* lit = to_app(q.m_pred2lit.find(ps[i]));
                SASSERT(q.arr.is_select(lit));
                if (is_true[i]) {
                    m_asms.push_back(ps[i]);
                }
                else {
                    // p => ps[i] = args belong to arguments where f evaluates to true.
                    unsigned num_args = lit->get_num_args();
                    expr_ref_vector disjs(m);
                    for (unsigned j = 0; j < ps.size(); ++j) {
                        if (is_true[j]) {
                            expr_ref_vector eqs(m);
                            app* lit_j = to_app(q.m_pred2lit.find(ps[j]));
                            for (unsigned k = 1; k < num_args; ++k) {
                                eqs.push_back(m.mk_eq(lit_j->get_arg(k), lit->get_arg(k)));
                            }
                            disjs.push_back(mk_and(eqs));
                        }                        
                    }
                    rhs = mk_or(disjs);
                    if (m.is_false(rhs)) {
                        m_asms.push_back(m.mk_not(ps[i]));
                    }
                    else {
                        p = q.fresh_bool("q");
                        rhs = mk_iff(lit, rhs);
                        max_level l = q.compute_level(ps[i]);
                        q.m_elevel.insert(p, l);
                        q.m_moves.insert(p, l);
                        q.abstract_atoms(rhs, l);
                        fml = m.mk_iff(p, q.mk_abstract(rhs));
                        q.add_pred(p, to_app(rhs));
                        
                        TRACE("qe", tout << fml << " " << p << " = " << rhs << "\n";);
                        q.m_ex.assert_expr(fml);
                        q.m_fa.assert_expr(fml);
                        m_asms.push_back(p);
                    }
                }                
            }               
        }        

        typedef obj_map<expr, ptr_vector<app> > select_map;
            select_map selects;

                if (q.is_select(lit, f)) {
                    selects.insert_if_not_there2(f, ptr_vector<app>())->get_data().m_value.push_back(p);                    
                    continue;
                }

#endif
