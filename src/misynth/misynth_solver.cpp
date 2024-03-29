#include "misynth_solver.h"
#include "collector_invocation_operands.h"
#include "rewriter_coefficients.h"
#include "ast/ast_pp.h"
#include "ast/rewriter/rewriter.h"
#include "ast/rewriter/rewriter_def.h"
#include "qe/qe_mbp.h"

#include "ast/used_vars.h"
#include "ast/rewriter/th_rewriter.h"
#include "misynth/synth_params.hpp"
#include "sanity_checker.h"
#include "search_simultaneously_branches.h"
#include "misynth/function_utils.h"
#include "misynth/collector_constants.h"
#include "misynth/combinators.h"
#include "misynth/collector_literals.h"

#include "model/model2expr.h"

#include "muz/spacer/spacer_util.h"
#include "qe/qe.h"
#include "qe/qe_tactic.h"
#include "human_print.h"

#include <iomanip>
#include <iostream>
#include <set>



#define VERBOSE true
#define DEBUG true

namespace misynth
{
    unsigned int max_iter_iso_mor = 0;
    unsigned int iters_main_alg = 0;
    unsigned int alg3_run = 0;

    bool DEBUG_MODE = false;



    misynth_solver::misynth_solver(cmd_context &cmd_ctx, ast_manager &m, solver *solver)
        : m_cmd(cmd_ctx)
        , m(m)
        , m_solver(solver)
        , m_utils(cmd_ctx, m)
        , m_arith(m)
        , m_futils(cmd_ctx, m)
        , m_coeff_decl_vec(m),

          m_used_vars(m),
          m_assumptions(m),
          assms(m), assms2(m),
          m_abducer(cmd_ctx, m),
          fn(m_cmd, m),
          task(m_cmd, m)
    {
    }

    model_ref misynth_solver::get_coeff_model_from_slv(ref<solver> &slv, expr_ref spec_for_concrete_x, expr_ref heuristic)
    {
//        m_utils.print_slv(std::cout, m_slv_for_coeff);
        bool is_added_heuristic = heuristic.get();
        slv->push();
        slv->assert_expr(spec_for_concrete_x);

        if (is_added_heuristic)
        {
            slv->push();
            slv->assert_expr(heuristic);
//          std::cout << "  heuri: " <<  mk_ismt2_pp(heuristic, m, 3)<< std::endl;
//          std::cout << "  spec_for_concrete_x: " <<  mk_ismt2_pp(spec_for_concrete_x, m, 3)<< std::endl;
        }

        lbool res_spec_for_x = slv->check_sat();

        model_ref mdl_for_coeff;
        if (res_spec_for_x != lbool::l_true)
        {
            //TODO: take into account a heuristic
            if (is_added_heuristic)
            {
//                std::cout << "WARNING!!! Heuristic for this spec and model x is unsat. " << std::endl;
                is_added_heuristic = false;
                slv->pop(1); // remove a heuristic
                lbool res_spec_for_x = slv->check_sat();
                if (res_spec_for_x != lbool::l_true)
                {
                    slv->pop(1);//remove spec
                    return mdl_for_coeff;//not found
                }
            }
            else
            {
                return mdl_for_coeff;//not found
            }

        }
        if (is_added_heuristic)
        {
            slv->pop(1);
            is_added_heuristic = false;
        }

        slv->get_model(mdl_for_coeff);
        slv->pop(1);

        expr_ref logic_mdl = m_utils.get_logic_model_with_default_value(mdl_for_coeff, m_coeff_decl_vec);
        slv->assert_expr(m.mk_not(logic_mdl));
        return mdl_for_coeff;

    }

    model_ref misynth_solver::get_coeff_model(expr_ref spec_for_concrete_x, expr_ref heuristic)
    {
        if (m_params.fairness())
        {
            unsigned int i = 0;
            model_ref mdl;
            while (i <=  m_slv_for_coeff_vec.size())
            {
                ref<solver> &slv = m_slv_for_coeff_vec.get(m_current_slv_for_coeff);
                mdl = get_coeff_model_from_slv(slv, spec_for_concrete_x, heuristic);
                if (mdl.get()) break;
                if (++m_current_slv_for_coeff ==  m_slv_for_coeff_vec.size())
                {
                    m_current_slv_for_coeff = 0;
                }
                ++i;
            }
            if (!mdl.get()) return mdl;

            for (unsigned int i = 0; i < m_slv_for_coeff_vec.size(); ++i)
            {
                if (i == m_current_slv_for_coeff)
                    continue;
                expr_ref value_for_coeff = m_utils.get_default_value_from_mdl(mdl, m_coeff_decl_vec.get(i));
                m_slv_for_coeff_vec.get(i)->push();
                m_slv_for_coeff_vec.get(i)->assert_expr(m.mk_not(m.mk_eq(m.mk_const(m_coeff_decl_vec.get(i)), value_for_coeff)));
            }


            if (++m_current_slv_for_coeff ==  m_slv_for_coeff_vec.size())
            {
                m_current_slv_for_coeff = 0;
            }
            return mdl;

        }
        else return get_coeff_model_from_slv(m_slv_for_coeff, spec_for_concrete_x, heuristic);

    }

    void misynth_solver::init_coeff_solver(func_decl_ref_vector & synth_funs)
    {
        params_ref params;
        m_slv_for_coeff = m_cmd.get_solver_factory()(m, params, false, true, false, symbol::null);

        for (unsigned int i = 0; i < synth_funs.get(0)->get_arity() + 1; ++i)
        {
            m_slv_for_coeff_vec.push_back(m_cmd.get_solver_factory()(m, params, false, true, false, symbol::null));
        }
    }

    void misynth_solver::generate_coeff_decl(func_decl_ref_vector & synth_funs)
    {
        m_coeff_decl_vec.reset();

        // for function synth_funs.get(0)
        unsigned num_of_coeff = synth_funs.get(0)->get_arity();
        std::string coeff_prefix = "C";

        for (unsigned i = 0; i < num_of_coeff + 1; ++i)
        {
            func_decl_ref coef(
                m.mk_const_decl(coeff_prefix + std::to_string((i)),
                                synth_funs.get(0)->get_range()), m);
            m_coeff_decl_vec.push_back(coef);
        }
    }

    void misynth_solver::init_used_variables(func_decl_ref_vector const& synth_funs, expr_ref spec, func_decl_ref_vector &out)
    {

        out.reset();
        decl_collector decls(m);
        decls.visit(spec);

        for (func_decl *fd :  decls.get_func_decls())
        {
            if (!synth_funs.contains(fd) && fd->get_arity() == 0 && !assms.contains(m.mk_const(fd)))
            {
                out.push_back(fd);
//                if (VERBOSE)
//                {
//                    std::cout << "Add used var: " << fd->get_name() << "  " << mk_ismt2_pp(fd, m, 3)  << std::endl;
//                }
            }
        }
    }

    expr_ref_vector misynth_solver::collect_constraints(func_decl_ref target, func_decl_ref_vector & synth_funs, expr_ref_vector & constraints)
    {
        expr_ref_vector res(m);

        for (auto &c : constraints)
        {
            app_ref_vector invocations(m);
            collect_invocation(c, synth_funs, invocations);
            bool is_only_target = invocations.size() > 0;
            //only target symbols
            for (app *a : invocations)
            {
                if (a->get_decl() != target)
                {
                    is_only_target = false;
                    break;
                }
            }
            if (is_only_target)
                res.push_back(c);
        }
        return res;

    }

    expr_ref misynth_solver::normalize(expr *e, func_decl_ref_vector &vars,
                                       func_decl_ref_vector &eliminate, expr_ref_vector &exprs)
    {
      expr_ref_vector eqs(m);

      for (unsigned int i = 0; i < vars.size(); ++i) {
        eqs.push_back(m.mk_eq(m.mk_const(vars.get(i)), exprs.get(i)));
      }
      expr_ref all_eq = m_utils.con_join(eqs);
      expr_ref res( m.mk_and(all_eq, e), m);

      res = m_utils.exist_quantified(res, eliminate);

      std::cout<< "Normalize for asserts: " << mk_smt_pp(res, m) << std::endl;
      smt_params params;
      expr_ref result(m);
      qe::expr_quant_elim      expr_qe(m, params);
      expr_qe(m.mk_true(), res, result);
      std::cout<< "Result of normalizing for asserts: " << mk_smt_pp(result, m) << std::endl;
      return result;
    }

    expr_ref_vector misynth_solver::encode_asserts(func_decl_ref_vector & synth_funs, expr_ref_vector & constraints) {
      expr_ref_vector encoded_asserts(m);
      expr_ref_vector assert_zero_conj(m);

      expr_ref spec = m_utils.simplify(m_utils.con_join(constraints));
//      std::cout << "all constraints:    " << mk_smt_pp(spec, m) << std::endl;
      app_ref_vector apps(m);
      collect_invocation(spec, synth_funs, apps);

      expr_ref_vector all_out_vars(m);
      expr_substitution sub(m); //out2vars;

      func_decl_ref_vector all_fresh_var(m);
      //obj_map<app, obj_map<func_decl, func_decl*> > app2map_vars;
      obj_map<app, ptr_vector<func_decl> > app2vars;
      obj_map<app, expr* > app2fresh;

      int i_app = 0;
      for( app* it : apps) {
          i_app++;
          expr_ref e(m.mk_const(m.mk_const_decl(std::string("fo") + std::to_string((i_app)), m_arith.mk_int())), m );
          //out2vars.insert(it, e);
          app2fresh.insert(it, e);
          sub.insert(it, e);
          all_out_vars.push_back(e);

          assert_zero_conj.push_back(m.mk_eq(e, it));

          //////////
          //func_decl_ref_vector used_vars(m);
          //init_used_variables(synth_funs, spec, used_vars);
          ptr_vector<func_decl> current;
          //for(func_decl *fd: used_vars) {
          for(int i=0; i< it->get_num_args(); ++i) {
            obj_map<func_decl, func_decl*> map;

            func_decl_ref fresh(m.mk_const_decl(std::string("fi") + std::to_string((i_app)) + "_" + std::to_string((i)), m_arith.mk_int()), m);
            all_fresh_var.push_back(fresh);
            current.push_back(fresh);
            assert_zero_conj.push_back(m.mk_eq(m.mk_const(fresh), it->get_arg(i)));
            //app2map_vars.insert(fd, fresh);

          }
          //app2map_vars.insert(app, std::move(map));
          app2vars.insert(it,     std::move(current));
      }

      scoped_ptr<expr_replacer> rp = mk_default_expr_replacer(m);
      rp->set_substitution(&sub);

//      std::cout << "##### Encoded zero-assert: #####" << std::endl;
      expr_ref assert_zero = m_utils.con_join(assert_zero_conj);
//      std::cout << "# Encoded zero-assert: "<< mk_smt_pp(assert_zero, m) << std::endl;


      encoded_asserts.push_back(assert_zero);

      int i_constraint = 0;

      for(expr * it : constraints ) {
            auto tmp = m_utils.simplify(expr_ref(it, m));
            i_constraint++;
            func_decl_ref_vector universal_vars(m);

            app_ref_vector apps_constraint(m);
            collect_invocation(tmp, synth_funs, apps_constraint);


            expr_ref_vector aps_expr(m);
            expr_ref_vector aps_fresh(m);

            func_decl_ref_vector var_decl(m);
            expr_ref_vector      exprs(m);

            expr_ref_vector disjuncts(m);

            obj_map<app, ptr_vector<func_decl> > app2vars_constraint;
            int i_ap = 0;

            expr_ref_vector premise_premise_conjs(m);

            for( app *ap : apps_constraint ) {
              i_ap++;
              aps_expr.push_back(ap);
              func_decl_ref fresh_ap(m.mk_const_decl(std::string("freshout_") +  std::to_string((i_constraint)) + "_" +  std::to_string((i_ap)), m_arith.mk_int()), m);
              aps_fresh.push_back(m.mk_const(fresh_ap.get()));
              universal_vars.push_back(fresh_ap);
              ptr_vector<func_decl> vec;
              for(int i =0; i < ap->get_num_args(); ++i) {
                  func_decl_ref fresh_ap(m.mk_const_decl(std::string("freshin_") + std::to_string((i_constraint))+ "_" + std::to_string((i_ap))+"_"+ std::to_string((i)), m_arith.mk_int()), m);

                  universal_vars.push_back(fresh_ap);
                  premise_premise_conjs.push_back(m.mk_eq(m.mk_const(fresh_ap), ap->get_arg(i)));
                  vec.push_back(fresh_ap);

                  var_decl.push_back(vec.get(i));
                  exprs.push_back(ap->get_arg(i));
              }
              app2vars_constraint.insert(ap, std::move(vec));
            }
            int slots = apps_constraint.size();
            int values = app2fresh.size();
            generator_permutation_with_repetitions comb(slots, values);
            while (comb.do_next())
            {
                expr_ref_vector conjuncts(m);
                vector<unsigned int> v = comb.get_next();
                int num_app_constraint = 0;
                for( unsigned ind : v )  {
                    --ind;
                    app *ap = apps_constraint.get( num_app_constraint );
                    app *ap2 = apps.get( ind );
                    expr_ref conj(m.mk_eq(aps_fresh.get( num_app_constraint ), app2fresh[ap2]), m);
                    for(int i =0; i<ap2->get_num_args(); ++i) {
                        conj = m.mk_and(conj, m.mk_eq(m.mk_const(app2vars_constraint[ap].get(i)), m.mk_const(app2vars[ap2].get(i))));
                    }

                    conjuncts.push_back(conj);
                    num_app_constraint++;
                 }
                 disjuncts.push_back(m_utils.con_join(conjuncts));
            }

            expr_ref premise = m_utils.dis_join(disjuncts);

            func_decl_ref_vector used_vars(m);
            init_used_variables(synth_funs, spec, used_vars);


            expr_ref add_assm(m.mk_false(), m);
            if (m.is_or (tmp))
            {
              for (unsigned int i = 0; i < to_app(tmp)->get_num_args(); ++i)
              {
                expr_ref arg(to_app(tmp)->get_arg(i), m);

                app_ref_vector invs(m);
                collect_invocation(arg, synth_funs, invs);
                if (invs.size() > 0)
                {
                  func_decl_ref fresh_assm(m.mk_const_decl(std::string("fresh_assm_")
                                       + std::to_string((i_constraint))
                                       + "_" + std::to_string(i), m.mk_bool_sort()), m);
                  assms.push_back(m.mk_const(fresh_assm));
                  tmp = m_utils.replace_expr(tmp, arg, expr_ref(m.mk_implies(m.mk_const(fresh_assm), arg), m));
                  add_assm = m.mk_or(add_assm, m.mk_const(fresh_assm));
                }
              }
            }
            if (!m.is_false(add_assm))
            {
              assms2.push_back(add_assm);
            }

            expr_ref res = m_utils.replace_expr(tmp, aps_expr, aps_fresh);

            //std::cout << "After replacing of outs "<< mk_smt_pp(res, m) << std::endl;
            res = m.mk_implies(m_utils.con_join(premise_premise_conjs), res);

            //std::cout << "After replacing of outs with a premise: "<< mk_smt_pp(res, m) << std::endl;
            func_decl_ref_vector used_vars2(m);
            init_used_variables(universal_vars, res, used_vars2);
            universal_vars.append(used_vars2);
            //std::cout << "normalize "<< mk_smt_pp(res, m) << std::endl;


            res = m.mk_implies(premise, res);
            res = m_utils.universal_quantified(res, universal_vars);
//            std::cout << "# Encoded assert "<< mk_smt_pp(res, m) << std::endl;

            // premise


            //replace out var
           // expr_ref result(m);
           // (*rp)(it, result);
        encoded_asserts.push_back(res);
      }

//      std::cout << "################################" << std::endl;


      return encoded_asserts;
    }

    bool misynth_solver::multi_solve(func_decl_ref_vector & synth_funs, expr_ref_vector & constraints,
                                     obj_map<func_decl, args_t *> &synth_fun_args_decl)
    {

//        std::cout << "synth_fun_args_decl: " << synth_fun_args_decl.size() << std::endl;
        // [+] INITIALIZE
        m_current_slv_for_coeff = 0;
        params_ref params;
        expr_ref spec = m_utils.con_join(constraints);
        task = synth_task(m_cmd, m,  constraints, synth_funs, synth_fun_args_decl);
        // [-] INITIALIZE

        m_synth_fun_args_decl = synth_fun_args_decl; // COPY


        //collect_invocation_operands(spec, synth_funs, m_ops);
        std::cout << "multi_solve " << synth_funs.size() << std::endl;
        if (prove_unrealizability(spec))
        {
            std::cout << "Unrealizability!!! Specification is unsat \n. " << std::endl;
            return false;
        }
        std::cout << "Realizability!!" << std::endl;
        expr_ref_vector fun_bodies(m);
        for (unsigned i = 0; i < synth_funs.size(); ++i)
        {
            func_decl_ref current_fun(synth_funs.get(i), m);

            expr_ref_vector collected_constraints = collect_constraints(current_fun, synth_funs, constraints);
            args_t *synth_fun_args = get_args_decl_for_synth_fun(synth_funs.get(i));
            invocations_rewriter inv_rwr(m_cmd, m);
            if (collected_constraints.size() == 0)
            {

                //default
                expr_ref fun_body(m_arith.mk_int(0), m);

                for (unsigned i = 0; i < constraints.size(); ++i)
                {
                    expr_ref res(m);
                    inv_rwr.rewrite_app_with_fun(expr_ref(constraints.get(i), m), current_fun, fun_body, *synth_fun_args, res);
                    constraints[i] = res;
                }
                fun_bodies.push_back(fun_body);
//                std::cout << "--------NEW CONSTRAINTS----------" << std::endl;
//                for (auto &c : constraints)
//                    std::cout << mk_smt_pp(c, m) << std::endl;
//                std::cout << "------------------" << std::endl;
            }
            else
            {
                //non-zero
//                std::cout << "non_zero" << std::endl;
//                std::cout << "------------------" << std::endl;
//                for (auto &c : collected_constraints)
//                    std::cout << mk_smt_pp(c, m) << std::endl;
//                std::cout << "------------------" << std::endl;
                fn.clear();
                func_decl_ref_vector one_synth_funs(m);
                one_synth_funs.push_back(current_fun);
                if (!solve(one_synth_funs, collected_constraints, synth_fun_args_decl)) return false;
                expr_ref fun_body(fn.generate_clia_fun_body(true), m);
                fun_bodies.push_back(fun_body);
//                std::cout << "--------NEW CONSTRAINTS2----------" << std::endl;
                for (unsigned i = 0; i < constraints.size(); ++i)
                {
                    expr_ref res(m);
                    inv_rwr.rewrite_app_with_fun(expr_ref(constraints.get(i), m), current_fun, fun_body, *synth_fun_args, res);
//                    std::cout << mk_smt_pp(res, m) << std::endl;
                    constraints[i] = res;

                }
//                std::cout << "------------------" << std::endl;
            }
        }
        //print
        for (unsigned i = 0; i < synth_funs.size(); ++i)
        {
            args_t *synth_fun_args = get_args_decl_for_synth_fun(synth_funs.get(i));
            print_def_fun(std::cout, synth_funs.get(i), *synth_fun_args, expr_ref(fun_bodies.get(i), m));
        }
        return true;
    }



        void misynth_solver::init_x_solver()
    {
        params_ref params;
        m_slv_for_x_prec = m_cmd.get_solver_factory()(m, params, false, true, false, symbol::null);
    }

    model_ref misynth_solver::get_model_x(synth_task &task, expr_ref heuristic)
    {
        bool is_added_heuristic = heuristic.get();

        args_t &args_decl = task.get_args_decl_for_synth_fun(task.synth_funs().get(0));
        expr_ref_vector all_precs_for_ops(m);
        all_precs_for_ops.reset();
        for (unsigned int i = 0; i < m_ops.size(); ++i)
        {
            expr_ref_vector precs_for_one_op(m);
            invocation_operands &op = m_ops.get(i);
            for (unsigned int j = 0; j < fn.get_precs().size(); ++j)
            {
                expr_ref called_prec = m_utils.replace_vars_decl(fn.get_precs().get(j), args_decl, op);
                precs_for_one_op.push_back(m.mk_not(called_prec));

            }

            all_precs_for_ops.push_back(m_utils.con_join(precs_for_one_op));

            if (DEBUG_MODE)
            {
                //std::cout << "add to solver called precondition: " << mk_ismt2_pp(slv_for_prec->get_assertion(slv_for_prec->get_num_assertions() - 1), m, 0) << std::endl;
            }
        }



        m_slv_for_x_prec->pop(1);// pop previos precs
        m_slv_for_x_prec->push();
        m_slv_for_x_prec->assert_expr(m_utils.dis_join(all_precs_for_ops));
        if (is_added_heuristic)
        {
            m_slv_for_x_prec->push();
            m_slv_for_x_prec->assert_expr(heuristic);
        }
        lbool res_spec_for_x = m_slv_for_x_prec->check_sat();

        model_ref mdl_for_precs;

        if (res_spec_for_x != lbool::l_true)
        {
            //TODO: take into account a heuristic
            if (is_added_heuristic)
            {
                std::cout << "WARNING!!! Heuristic for precs x is unsat. " << std::endl;
                is_added_heuristic = false;
                m_slv_for_x_prec->pop(1); // remove a heuristic
                lbool res_spec_for_x = m_slv_for_x_prec->check_sat();
                if (res_spec_for_x != lbool::l_true)
                {
                    m_slv_for_x_prec->pop(1);//remove spec
                    return mdl_for_precs;//not found
                }
            }
            else
            {
                return mdl_for_precs;//not found
            }

        }
        if (is_added_heuristic)
        {
            m_slv_for_x_prec->pop(1);
            is_added_heuristic = false;
        }

        m_slv_for_x_prec->get_model(mdl_for_precs);
        m_slv_for_x_prec->pop(1);
        return mdl_for_precs;

    }


    expr_ref misynth_solver::generate_heuristic_concrete_coef_from_literals(synth_task &task) {
      std::vector<model_ref> models_vec;
      collect_coeff_from_lits(m_cmd, m, m_arith, m_utils,
                              task.spec(), task.synth_funs(), m_coeff_decl_vec, m_used_vars, models_vec);
      expr_ref_vector mdls(m);
      for (model_ref& mdl : models_vec)
      {
          mdls.push_back(m_utils.get_logic_model_with_default_value(mdl, m_coeff_decl_vec));
      }
      return m_utils.dis_join(mdls);
    }

//    double all_time_coeff_model = 0;
    bool zero_coeff = true;
    int heuri;

    bool misynth_solver::solve(func_decl_ref_vector & synth_funs, expr_ref_vector & constraints,  obj_map<func_decl, args_t *> &synth_fun_args_decl)
    {
        if (m_params.attempts_per_one_model_x() == 0)
          heuri = 3;
        else
          heuri = m_params.type_heuristic(); // heuristic

        if (m_params.simult_model_x())
        {
            return solve_simult_model_x(synth_funs, constraints, synth_fun_args_decl);
        }

        // [+] INITIALIZE
        m_ops.reset();
        m_current_slv_for_coeff = 0;
        params_ref params;
        expr_ref spec = m_utils.simplify(m_utils.con_join(constraints));
//        std::cout << "==== START SOLVING ==== " << std::endl;
        task = synth_task(m_cmd, m,  constraints, synth_funs, synth_fun_args_decl);
        // [-] INITIALIZE

        m_synth_fun_args_decl = synth_fun_args_decl; // COPY

        if (prove_unrealizability(spec))
        {
            std::cout << "Unrealizability!!! Specification is unsat \n. " << std::endl;
            return false;
        }

        expr_ref_vector encoded_asserts = encode_asserts(synth_funs, constraints);
        expr_ref zero_encoded_assert_x(m);

        collect_invocation_operands(spec, synth_funs, m_ops);


        init_used_variables(synth_funs, spec, m_used_vars);
        generate_coeff_decl(synth_funs);

        // [+] heuristics
//        std::cout << "======= [+] heuristics ======= " << std::endl;
        expr_ref heuristic_concrete_coef_from_literals(m.mk_true(), m);
        if (m_params.add_literals_heuristic())
        {
            heuristic_concrete_coef_from_literals = generate_heuristic_concrete_coef_from_literals(task);
        }

//        std::cout << "Heuristic_concrete_coef_from_literals: " << human_print(heuristic_concrete_coef_from_literals, m, 0) << std::endl;
        args_t *args_decl = get_args_decl_for_synth_fun(synth_funs.get(0));

        expr_ref  heuristic_constaraint_coeff(generate_heuristic_constaraint_coeff(spec, m_coeff_decl_vec));

//        std::cout << "Generated heuristic: " << human_print(heuristic_constaraint_coeff, m, 0) << std::endl;
//        std::cout << "======= [-] heuristics ======= " << std::endl;
        // [-] heuristics

        //params_ref params;
        ref<solver> slv_for_prec = m_cmd.get_solver_factory()(m, params, false, true, false, symbol::null);
        ref<solver> slv_for_mbp = m_cmd.get_solver_factory()(m, params, false, true, false, symbol::null);
        expr_ref last_precond(0, m);



        const unsigned int MAX_ITERATION = UINT_MAX;

        unsigned int current_assumption_idx = 0;
        unsigned int attempt_number_current_assumption = 0;
        bool pushed_assumption = false;
        bool is_added_heuristic = false;

        unsigned int  current_iter_model_x = UINT_MAX - 1;
        unsigned int  current_iter_trivial_model_x = 0;

        expr_ref spec_for_concrete_x(m);
        model_ref mdl_for_x;


        args_t *synth_fun_args = get_args_decl_for_synth_fun(synth_funs.get(0));

        //[+] mbp
        invocations_rewriter inv_rwr(m_cmd, m);
        app2expr_map map;
        func_decl_ref_vector fresh_vars(m);
        expr_ref_vector inv_replaced(m);
        app_ref_vector fresh_vars_app(m);


        expr_ref spec_with_inv_vars(m);
        inv_rwr.rewriter_fun_inv_to_var(spec, synth_funs, map, fresh_vars, inv_replaced, spec_with_inv_vars);

        for (func_decl * fd : fresh_vars)
            fresh_vars_app.push_back(m.mk_const(fd));


        slv_for_mbp->push();
        slv_for_mbp->assert_expr(spec_with_inv_vars);
        //[-]

        expr_ref_vector all_precs_for_ops(m);
        slv_for_prec->push();
        slv_for_prec->assert_expr(m.mk_true());
        //for (unsigned int k = 0; k < MAX_ITERATION ; ++k)
        {
            //[+]mbp
            //reset coeff solver (blacklist model)
            init_coeff_solver(synth_funs);
            init_x_solver();
            expr_ref result_mbp(m.mk_true(), m) ;
            model_ref mdl_for_mbp;
            if (m_params.mbp())
            {

                lbool r = slv_for_mbp->check_sat();
                if (r != lbool::l_true)
                {
                    std::cout << "@@@@@@@ UNREACHABLE STATE!!! Disj of mbp is valid" << std::endl;;

                    if (try_find_simultaneously_branches(synth_funs, constraints, 0, true))
                        return true;
                    return false;

                }


                slv_for_mbp->get_model(mdl_for_mbp);

                expr_ref_vector res_v(m);
                res_v.push_back(spec_with_inv_vars);
                qe::mbp mbp(m);
                app_ref_vector fresh_vars_app_mbp(fresh_vars_app);
                mbp(false,  fresh_vars_app_mbp, *mdl_for_mbp, res_v);
                result_mbp = m_utils.con_join(res_v);
//                std::cout << "RESULT mdl_for_mbp: " << mk_ismt2_pp(spec_with_inv_vars, m, 0) << std::endl;
//                std::cout << "RESULT mdl_for_mbp: " << *mdl_for_mbp << std::endl;
//                std::cout << "RESULT MBP: " << mk_ismt2_pp(result_mbp, m, 0) << std::endl;

                //expr_ref result_spacer(spec_with_inv_vars, m);
                //spacer::qe_project(m, fresh_vars_app, result_spacer, *mdl_for_mbp);
                //result_mbp = result_spacer;

                //std::cout << "RESULT MBP2: " << mk_ismt2_pp(result_mbp, m, 0) << std::endl;
                slv_for_mbp->push();
                slv_for_mbp->assert_expr(m.mk_not(result_mbp));

                slv_for_prec->pop(slv_for_prec->get_num_assertions());

                m_slv_for_x_prec->push();
                m_slv_for_x_prec->assert_expr(result_mbp);


                // {
                //result_mbp = m.mk_true();
                //slv_for_mbp->assert_expr(m.mk_false());//for unsat of slv_for_mbp

                // }
                m_slv_for_x_prec->push();
                m_slv_for_x_prec->assert_expr(m.mk_true());

            }

            //[-]mbp
            bool is_add_literals_heuristic = m_params.add_literals_heuristic();
            int max_assm = m_params.attempts_per_one_model_x();

            for (iters_main_alg = 0; iters_main_alg < MAX_ITERATION ; ++iters_main_alg)
            {
                if (iters_main_alg % 22 == 0 &&
                    m_params.attempts_per_one_model_x() == 0) max_assm ++; // heuristic to try different tresholds
                if (DEBUG_MODE)
                    std::cout << "====  Iteration #" << iters_main_alg << "  ====" << std::endl;

                if (last_precond.get()) // non first iteration
                {
                    all_precs_for_ops.reset();
                    for (unsigned int i = 0; i < m_ops.size(); ++i)
                    {
                        expr_ref_vector precs_for_one_op(m);
                        invocation_operands &op = m_ops.get(i);
                        for (unsigned int j = 0; j < fn.get_precs().size(); ++j)
                        {
                            expr_ref called_prec = m_utils.replace_vars_decl(fn.get_precs().get(j), *args_decl, op);
                            precs_for_one_op.push_back(m.mk_not(called_prec));
                        }

                        all_precs_for_ops.push_back(m_utils.con_join(precs_for_one_op));

                        if (DEBUG_MODE)
                        {
                            //std::cout << "add to solver called precondition: " << mk_ismt2_pp(slv_for_prec->get_assertion(slv_for_prec->get_num_assertions() - 1), m, 0) << std::endl;
                        }
                    }

                    if (slv_for_prec->get_num_assertions() > 0)
                      slv_for_prec->pop(1);// pop previos precs
                    slv_for_prec->push();
                    slv_for_prec->assert_expr(m_utils.con_join(all_precs_for_ops));       // GF: change con_join and dis_join
          //          std::cout << "Current precs: " << mk_ismt2_pp(slv_for_prec->get_assertion(slv_for_prec->get_num_assertions() - 1), m, 0) << std::endl;

                    last_precond = 0;
                }
//                clock_t start = clock();
                if (iters_main_alg != 0 || !m_params.mbp())
                {
//                  std::cout << "current_iter_model_x = " << current_iter_model_x << "\nm_params.attempts_per_one_model_x() = " << max_assm << "\n";
                    if (++current_iter_model_x >= max_assm) //(m_params.attempts_per_one_model_x() + m_params.trivial_attempts_per_one_model_x()))
                    {
                        current_iter_model_x = 0;
                        current_iter_trivial_model_x = 0;
                        if (attempt_number_current_assumption >= m_params.attempts_per_one_assumption())
                        {
                            ++current_assumption_idx;
                            attempt_number_current_assumption = 0;
                        }
                        if (current_assumption_idx < m_assumptions.size())
                        {
                            pushed_assumption = true;
                            slv_for_prec->push();
                            slv_for_prec->assert_expr(m_assumptions.get(current_assumption_idx));
//                            std::cout << "pushed assumption " << mk_ismt2_pp(m_assumptions.get(current_assumption_idx), m, 0) << std::endl;

                            ++attempt_number_current_assumption;
                        }

                        lbool r = slv_for_prec->check_sat();
                        if (pushed_assumption)
                        {
                            slv_for_prec->pop(1); //remove assumption
                            pushed_assumption = false;
                        }
                        if (r != lbool::l_true)//without assumption
                        {
                            current_assumption_idx++;
                            r = slv_for_prec->check_sat();
                        }

                        if (r == lbool::l_true)
                        {
                            slv_for_prec->get_model(mdl_for_x);
//                            std::cout << "SAT Precond 1: \n" << *mdl_for_x << std::endl;
                          zero_coeff = true;
                        }
                        else
                        {
                            std::cout << "!!! UNSAT of precs with replaced operands 2"  << std::endl;

                            // restart
                            fn.clear();
                            slv_for_prec = m_cmd.get_solver_factory()(m, params, false, true, false, symbol::null);
                            last_precond = 0;

                            continue;

                            //unused
                            if (try_find_simultaneously_branches(synth_funs, constraints, 0, true))
                                return true;
                            continue;


                        }

                        zero_encoded_assert_x = m_utils.replace_vars_according_to_model(encoded_asserts[0].get(), mdl_for_x, m_used_vars, true);
                        spec_for_concrete_x = m_utils.replace_vars_according_to_model(spec, mdl_for_x, m_used_vars, true);
                        if (prove_unrealizability_simple(spec_for_concrete_x))
                        {
                            return false;
                        }
                    }
                    else// simply check sat of prec
                    {
                        lbool r = slv_for_prec->check_sat();
                        if (r == lbool::l_false)
                        {
//                            std::cout << "!!! UNSAT of precs with replaced operands\nRestarting\n"  << std::endl;

                            // restart
                            fn.clear();
                            slv_for_prec = m_cmd.get_solver_factory()(m, params, false, true, false, symbol::null);
                            last_precond = 0;

                            continue;

                            //unused
                            if (try_find_simultaneously_branches(synth_funs, constraints, 0, true))
                                return true;
                            continue;

                        }

                    }
                }
                else
                {
                    spec_for_concrete_x = m_utils.replace_vars_according_to_model(spec, mdl_for_mbp, m_used_vars, true);
                }
//                all_time_coeff_model += ((double)(clock() - start) / CLOCKS_PER_SEC);
//                if (DEBUG_MODE)
//                {
//                    std::cout << "Spec_for_concrete_x: " << human_print(spec_for_concrete_x, m, 3) << std::endl;
//                }


                /*
                 * [+] getting model for coefficients
                 * */
                if (current_iter_trivial_model_x++ < m_params.trivial_attempts_per_one_model_x())
                {
//                    std::cout << "Pushed heuristic constaraint for coeff" << std::endl;
                    is_added_heuristic = true;
                }

                //++current_iter_trivial_model_x;

                expr_ref spec_with_coeff_and_x(m);
                expr_ref zero_encoded_assert_x_and_coeff(m);
                invocations_rewriter inv_rwr(m_cmd, m);
                if (false) //(m_params.reused_brances())
                {
                     inv_rwr.rewriter_functions_to_linear_term_with_prec(m_coeff_decl_vec, synth_funs, zero_encoded_assert_x, zero_encoded_assert_x_and_coeff, *synth_fun_args, fn.get_precs(), fn.get_branches());
                }
                else
                {
                    inv_rwr.rewriter_functions_to_linear_term(m_coeff_decl_vec, synth_funs, zero_encoded_assert_x, zero_encoded_assert_x_and_coeff);
                }

//                if (DEBUG_MODE)
//                {
//                    std::cout << "spec_with_coeff " << mk_ismt2_pp(spec_with_coeff_and_x, m) << std::endl;
//                    std::cout << "zero_encoded_assert_x_and_coeff " << mk_ismt2_pp(zero_encoded_assert_x_and_coeff, m) << std::endl;
//                }


                // [+] union assets
                expr_ref_vector asserts2(m);
                asserts2.push_back(zero_encoded_assert_x_and_coeff);
//                std::cout << "==== [+] Constraint_for_coeff ===" << std::endl;
//                std::cout << "assert #0: " << mk_ismt2_pp(zero_encoded_assert_x_and_coeff, m) << std::endl;
                for(unsigned i = 1; i < encoded_asserts.size(); ++i) {
                    expr_ref encoded_assert_x = m_utils.replace_vars_according_to_model(encoded_asserts[i].get(), mdl_for_x, m_used_vars, true);
                    asserts2.push_back(encoded_assert_x);
//                    std::cout << "assert #"<< i << ": " << mk_ismt2_pp(encoded_assert_x, m) << std::endl;
                }
                expr_ref constraint_for_coeff = m_utils.con_join(asserts2);

//                std::cout << "=== [-] Constraint_for_coeff ===" << std::endl;
                // [-]
                //model_ref mdl_for_coeff = get_coeff_model(spec_with_coeff_and_x, is_added_heuristic ? heuristic_constaraint_coeff : expr_ref(m));

//                std::cout << "   (model #" << current_iter_model_x <<")\n";

                model_ref mdl_for_coeff = 0;
                if (is_add_literals_heuristic)
                {
                    mdl_for_coeff = get_coeff_model(expr_ref(m.mk_and(constraint_for_coeff, heuristic_concrete_coef_from_literals), m),  is_added_heuristic ? heuristic_constaraint_coeff : expr_ref(m));
                    if (!mdl_for_coeff)
                    {
                        is_add_literals_heuristic = false;
                        mdl_for_coeff = get_coeff_model(constraint_for_coeff, is_added_heuristic ? heuristic_constaraint_coeff : expr_ref(m));
                    }
                }
                else
                {
                  unsigned num_of_coeff = synth_funs.get(0)->get_arity();

                  expr_ref cnt(m_arith.mk_int(0), m);
                  for (unsigned i = 0; i < num_of_coeff + 1; ++i)
                    cnt = m_arith.mk_add(cnt, m.mk_ite(m.mk_eq(m_arith.mk_int(0), m.mk_const(m_coeff_decl_vec.get(i))), m_arith.mk_int(0), m_arith.mk_int(1)));
//                  std::cout << "   tmp cnt: " << mk_ismt2_pp(cnt, m, 0) << std::endl;

                  // GF
                  if (false) // original
                  {
                    mdl_for_coeff = get_coeff_model(expr_ref(constraint_for_coeff, m),
                          is_added_heuristic ? heuristic_constaraint_coeff : expr_ref(m));
                  }
                  else
                  {
//                      for (unsigned i = num_of_coeff + 1; i >= current_iter_model_x / 2 + 1; --i)
                    for (unsigned i = current_iter_model_x / 2 ; i <= num_of_coeff + 1; ++i)
                    {
                      expr_ref_vector cnjs(m);
                      cnjs.push_back(m_utils.con_join(assms2));
                      cnjs.push_back(constraint_for_coeff);
                      cnjs.push_back(zero_coeff ? m.mk_true() : m.mk_eq(m_arith.mk_int(0), m.mk_const(m_coeff_decl_vec.get(0))));
                      cnjs.push_back(m.mk_eq(m_arith.mk_int(i), cnt));
                      is_added_heuristic = true;
                      mdl_for_coeff = get_coeff_model(m_utils.con_join(cnjs),
                                                      is_added_heuristic ? heuristic_constaraint_coeff : expr_ref(m));
                      if (mdl_for_coeff)
//                      {
//                        std::cout << "solved with " << i << " ones, zero_coeff = " << zero_coeff << "\n";
                        break;
//                      }
//                      else
//                      {
//                        std::cout << "        tried with " << i << " ones, zero_coeff = " << zero_coeff << "; but no luck\n";
//                      }
                    }
                    zero_coeff = !zero_coeff;
                  }
                }
                is_added_heuristic = false;

                if (!mdl_for_coeff)
                {
                    std::cout << "WARNING!!! There are several branches\nRestarting" << std::endl;
                  // restart
                    fn.clear();
                    slv_for_prec = m_cmd.get_solver_factory()(m, params, false, true, false, symbol::null);
                    last_precond = 0;
                    if (m_params.attempts_per_one_model_x() == 0 && max_assm > synth_funs.get(0)->get_arity() * 2)
                    {
                      max_assm = 1;
                      if (heuri == 3) heuri = 2;  // GF: heuristically
                      else if (heuri == 2) heuri = 3;
                      heuristic_constaraint_coeff = generate_heuristic_constaraint_coeff(spec, m_coeff_decl_vec);
                    }
                    continue;

//                    if (try_find_simultaneously_branches(synth_funs, constraints, mdl_for_x))
//                        return true;

                    // TODO:???

                }
//                std::cout << "SAT mdl_for_coeff: " << std::endl << *mdl_for_coeff << std::endl;

                //simplify spec for concrete coef

                expr_ref branch = m_futils.generate_branch(m_coeff_decl_vec, *synth_fun_args, synth_funs, mdl_for_coeff);

                /*[+] Find a precondition*/
                //[+] add mbp
//                expr_ref spec_and_mbp(m_params.mbp() ? m.mk_and(spec, result_mbp) : spec, m);
                //[-] mbp
//              std::cout << "  mdl_for_x   " << *mdl_for_x << std::endl;
              bool prec_res = true;
              if (false)
                prec_res = find_precondition(synth_funs, spec, mdl_for_coeff, last_precond, mdl_for_x);
              else
                for (int i = 0; i < constraints.size(); i++)
                {
                  expr_ref last_precond_tmp(0, m);
                  expr_ref tmp(constraints.get(i), m);
                  prec_res &= find_precondition(synth_funs, tmp, mdl_for_coeff, last_precond_tmp, mdl_for_x);
                  if (!last_precond) last_precond = last_precond_tmp;
                  else last_precond = m.mk_and(last_precond, last_precond_tmp);
                }

              if (!prec_res)
              {
//                  std::cout << " prec result (false -- a precondition doesn't exist)\nRestarting\n" << std::endl;
                
                  // restart
                  fn.clear();
                  slv_for_prec = m_cmd.get_solver_factory()(m, params, false, true, false, symbol::null);
                  last_precond = 0;
                  continue;

//                  if (try_find_simultaneously_branches(synth_funs, constraints, mdl_for_x, true))
//                      return true;
              }

                if (m_utils.is_unsat(last_precond))
                {
                    last_precond = 0;
//                    std::cout << "!!! Precond is unsat" << std::endl;
                    continue;
                }

                //current_iter_model_x = UINT_MAX - 1; // reset model X

                if (m_utils.is_unsat(m.mk_not(last_precond)))
                    //if(m.is_true(last_precond))
                {
                    fn.clear();
                    fn.add_branch(m.mk_true(), branch);
                    if (completed_solving(synth_funs, constraints, fn.generate_clia_fun_body(false)))
                      return true;
                    else
                    {
                      // restart
                      //                        std::cout << "Restarting\n" << std::endl;
                      fn.clear();
                      slv_for_prec = m_cmd.get_solver_factory()(m, params, false, true, false, symbol::null);
                      last_precond = 0;
                      continue;
                    }
                }


                fn.add_branch(last_precond, branch);

                /*[-] */
//                if (DEBUG_MODE)
//                {
//                    std::cout << "-------------------" << std::endl;
//                    std::cout << mk_ismt2_pp(last_precond, m, 0) << "  ==> " << mk_ismt2_pp(fn.get_branches().back(), m, 0) << std::endl;
//                }
                if (fn.is_completed())
                {
                    if (completed_solving(synth_funs, constraints, fn.generate_clia_fun_body(false)))
                        return true;
                    else
                    {
                        // restart
//                        std::cout << "Restarting\n" << std::endl;
                        fn.clear();
                        slv_for_prec = m_cmd.get_solver_factory()(m, params, false, true, false, symbol::null);
                        last_precond = 0;
                        continue;
                    }
                }
//                {
//                    if (try_find_simultaneously_branches(synth_funs, constraints, 0))
//                        return true;
//                }
//                std::cout << "-------------------" << std::endl;
//              exit(0);

            }
        }
        return false;
    }



    bool misynth_solver::solve_simult_model_x(func_decl_ref_vector & synth_funs, expr_ref_vector & constraints,  obj_map<func_decl, args_t *> &synth_fun_args_decl)
    {
        // [+] INITIALIZE
        m_current_slv_for_coeff = 0;
        params_ref params;
        expr_ref spec = m_utils.con_join(constraints);



        // [-] INITIALIZE


        m_synth_fun_args_decl = synth_fun_args_decl; // COPY
        collect_invocation_operands(spec, synth_funs, m_ops);

        //std::cout << "m_ops size: " << m_ops.size() << std::endl;
        if (prove_unrealizability(spec))
        {
            std::cout << "Unrealizability!!! Specification is unsat \n. " << std::endl;
            return false;
        }

        init_used_variables(synth_funs, spec, m_used_vars);

        generate_coeff_decl(synth_funs);
        /*expr_ref spec_with_coeff(m);
        invocations_rewriter inv_rwr(m_cmd, m);
        inv_rwr.rewriter_functions_to_linear_term(m_coeff_decl_vec, synth_funs, spec, spec_with_coeff);

        if (VERBOSE)
        {
            std::cout << "spec_with_coeff: " << mk_ismt2_pp(spec_with_coeff, m, 3) << std::endl;
        }*/


        //params_ref params;
        ref<solver> slv_for_prec = m_cmd.get_solver_factory()(m, params, false, true, false, symbol::null);
        ref<solver> slv_for_mbp = m_cmd.get_solver_factory()(m, params, false, true, false, symbol::null);

        //m_slv_for_prec_completing_cond = m_cmd.get_solver_factory()(m, params, false, true, false, symbol::null);

        expr_ref last_precond(0, m);

        //func_decl *fd  = m.mk_const_decl("x", m_arith.mk_int());
        //precond = m_arith.mk_lt(m.mk_const(fd), m_arith.mk_int(0));

        //precond = spec_with_coeff;
        args_t *args_decl = get_args_decl_for_synth_fun(synth_funs.get(0));


        const unsigned int MAX_ITERATION = UINT_MAX;

        unsigned int current_assumption_idx = 0;
        unsigned int attempt_number_current_assumption = 0;
        bool pushed_assumption = false;


        bool is_added_heuristic = false;

        unsigned int  current_iter_model_x = UINT_MAX - 1;
        unsigned int  current_iter_trivial_model_x = 0;

        expr_ref spec_for_concrete_x(m);
        model_ref mdl_for_x;

        expr_ref  heuristic_constaraint_coeff(generate_heuristic_constaraint_coeff(spec, m_coeff_decl_vec));

 //       std::cout << "generated heuristic: " << mk_ismt2_pp(heuristic_constaraint_coeff, m, 0) << std::endl;

        args_t *synth_fun_args = get_args_decl_for_synth_fun(synth_funs.get(0));

        //[+] mbp
        invocations_rewriter inv_rwr(m_cmd, m);
        app2expr_map map;
        func_decl_ref_vector fresh_vars(m);
        expr_ref_vector inv_replaced(m);
        app_ref_vector fresh_vars_app(m);


        expr_ref spec_with_inv_vars(m);
        inv_rwr.rewriter_fun_inv_to_var(spec, synth_funs, map, fresh_vars, inv_replaced, spec_with_inv_vars);

        for (func_decl * fd : fresh_vars)
        {
            fresh_vars_app.push_back(m.mk_const(fd));
        }

        //expr_ref quant_spec_with_inv_vars = m_utils.exist_quantified(spec_with_inv_vars, fresh_vars);
        //std::cout << "spec_with_inv_vars heuristic: " << mk_ismt2_pp(quant_spec_with_inv_vars, m, 0) << std::endl;


        slv_for_mbp->push();
        slv_for_mbp->assert_expr(spec_with_inv_vars);
        //[-]

        expr_ref_vector all_precs_for_ops(m);
        slv_for_prec->push();
        slv_for_prec->assert_expr(m.mk_true());
        for (unsigned int k = 0; k < MAX_ITERATION ; ++k)
        {
            //[+]mbp
            lbool r = slv_for_mbp->check_sat();
            if (r != lbool::l_true)
            {
//                std::cout << "@@@@@@@ UNREACHABLE STATE!!! Disj of mbp is valid" << std::endl;;

                if (try_find_simultaneously_branches(synth_funs, constraints, 0, true))
                    return true;
                return false;

            }

            model_ref mdl_for_mbp;
            slv_for_mbp->get_model(mdl_for_mbp);

            expr_ref_vector res_v(m);
            res_v.push_back(spec_with_inv_vars);
            qe::mbp mbp(m);
            app_ref_vector fresh_vars_app_mbp(fresh_vars_app);
            mbp(false,  fresh_vars_app_mbp, *mdl_for_mbp, res_v);
            expr_ref result_mbp = m_utils.con_join(res_v);
            //std::cout << "RESULT mdl_for_mbp: " << mk_ismt2_pp(spec_with_inv_vars, m, 0) << std::endl;
            std::cout << "RESULT mdl_for_mbp: " << *mdl_for_mbp << std::endl;
            //expr_ref result_spacer(spec_with_inv_vars, m);
            //spacer::qe_project(m, fresh_vars_app, result_spacer, *mdl_for_mbp);
            //result_mbp = result_spacer;

            std::cout << "RESULT MBP: " << mk_ismt2_pp(result_mbp, m, 0) << std::endl;

            slv_for_mbp->push();
            slv_for_mbp->assert_expr(m.mk_not(result_mbp));

            slv_for_prec->pop(slv_for_prec->get_num_assertions());
            if (m_params.mbp())
            {
                slv_for_prec->push();
                slv_for_prec->assert_expr(result_mbp);


            }
            else
            {
                result_mbp = m.mk_true();
                slv_for_mbp->assert_expr(m.mk_false());//for unsat of slv_for_mbp

            }
            current_iter_model_x = UINT_MAX - 1; // reset model X
            current_iter_trivial_model_x = 0;
            slv_for_prec->push();
            slv_for_prec->assert_expr(m.mk_true());

            //reset coeff solver (blacklist model)
            init_coeff_solver(synth_funs);

            //[-]mbp
            //disj of prec => mbp
            // disj prec /\ \not(mbp) = unsat
            int max_assm = m_params.attempts_per_one_model_x();
            for (unsigned int i = 0; i < MAX_ITERATION ; ++i)
            {
                iters_main_alg++;
                if (DEBUG_MODE)
                    std::cout << "====  Iteration #" << i << "  ====" << std::endl;

                if (last_precond.get()) // non first iteration
                {

                    all_precs_for_ops.reset();
                    for (unsigned int i = 0; i < m_ops.size(); ++i)
                    {
                        expr_ref_vector precs_for_one_op(m);
                        invocation_operands &op = m_ops.get(i);
                        for (unsigned int j = 0; j < fn.get_precs().size(); ++j)
                        {
                            expr_ref called_prec = m_utils.replace_vars_decl(fn.get_precs().get(j), *args_decl, op);
                            precs_for_one_op.push_back(m.mk_not(called_prec));

                        }

                        all_precs_for_ops.push_back(m_utils.con_join(precs_for_one_op));



                        //slv_for_prec->push();
                        //slv_for_prec->assert_expr(m.mk_not(called_prec));

                        if (DEBUG_MODE)
                        {
                            //std::cout << "add to solver called precondition: " << mk_ismt2_pp(slv_for_prec->get_assertion(slv_for_prec->get_num_assertions() - 1), m, 0) << std::endl;
                        }
                    }



                    slv_for_prec->pop(1);// pop previos precs
                    slv_for_prec->push();
                    slv_for_prec->assert_expr(m_utils.dis_join(all_precs_for_ops));
                 //   std::cout << "Current precs: " << mk_ismt2_pp(slv_for_prec->get_assertion(slv_for_prec->get_num_assertions() - 1), m, 0) << std::endl;

                    last_precond = 0;
                }
                if (++current_iter_model_x >= max_assm) //(m_params.attempts_per_one_model_x() + m_params.trivial_attempts_per_one_model_x()))
                {
                    current_iter_model_x = 0;
                    current_iter_trivial_model_x = 0;
                    if (attempt_number_current_assumption >= m_params.attempts_per_one_assumption())
                    {
                        ++current_assumption_idx;
                        attempt_number_current_assumption = 0;
                    }
                    if (current_assumption_idx < m_assumptions.size())
                    {
                        pushed_assumption = true;
                        slv_for_prec->push();
                        slv_for_prec->assert_expr(m_assumptions.get(current_assumption_idx));
                     //   std::cout << "pushed assumption " << mk_ismt2_pp(m_assumptions.get(current_assumption_idx), m, 0) << std::endl;

                        ++attempt_number_current_assumption;
                    }

                    lbool r = slv_for_prec->check_sat();
                    if (pushed_assumption)
                    {
                        slv_for_prec->pop(1); //remove assumption
                        pushed_assumption = false;
                    }
                    if (r != lbool::l_true)//without assumption
                    {
                        current_assumption_idx++;
                        r = slv_for_prec->check_sat();
                    }

                    expr_ref coeff_spec(spec, m);
                    //
                    if (m_params.mbp())
                    {

                        expr_ref lits = m_utils.pick_literals(spec_with_inv_vars, mdl_for_mbp);
              //          std::cout << "spec_with_inv_vars " << mk_ismt2_pp(spec_with_inv_vars, m, 0) << std::endl;
                        coeff_spec = m_utils.replace_vars_decl(lits, fresh_vars, inv_replaced);
              //          std::cout << "pick_literals mdl x " << mk_ismt2_pp(coeff_spec, m, 0) << std::endl;

                    }
                    expr_ref_vector spec_for_concrete_x_vec(m);
                    if (r == lbool::l_true)
                    {
                        for (int i = 0; i < m_params.simult_model_x(); ++i)
                        {
                            if (i > 0)
                            {
                                slv_for_prec->push();
                                slv_for_prec->assert_expr(m.mk_not(m_utils.get_logic_model_with_default_value(mdl_for_x, m_used_vars)));
                      //          std::cout << "pushed mdl x " << mk_ismt2_pp(slv_for_prec->get_assertion(slv_for_prec->get_num_assertions() - 1), m, 0) << std::endl;
                                r = slv_for_prec->check_sat();
                                //slv_for_prec->pop(1);
                                if (r != lbool::l_true) break;
                            }

                            slv_for_prec->get_model(mdl_for_x);
                            std::cout << "SAT Precond!! "  << std::endl;

                            if (prove_unrealizability_with_mdl(spec, mdl_for_x))
                            {
                                return false;
                            }
                            spec_for_concrete_x_vec.push_back(m_utils.replace_vars_according_to_model(coeff_spec, mdl_for_x, m_used_vars, true));
                        }
//                        m_utils.print_slv(std::cout, slv_for_prec);
                        //push to blacklist
                        //slv_for_prec->push();
                        //slv_for_prec->assert_expr(m.mk_not(m_utils.get_logic_model_with_default_value(mdl_for_x, m_used_vars)));

                        // slv->pop(1);
                        /*std::cout << "SAT Precond!! " << *mdl << std::endl;

                        for (func_decl *fd : m_used_vars)
                        {
                            expr_ref e( to_expr(m.mk_const(fd)), m) ;
                            std::cout << fd->get_name() << " " <<  mk_ismt2_pp((*mdl)(e), m, 3) << std::endl;
                        }*/
                    }
                    else
                    {
                        std::cout << "!!! UNSAT of precs with replaced operands 1"  << std::endl;

                        break;

                        //unused
                        if (try_find_simultaneously_branches(synth_funs, constraints, 0, true))
                            return true;
                        continue;


                    }

                    spec_for_concrete_x = m_utils.con_join(spec_for_concrete_x_vec);
                }
                else// simply check sat of prec
                {
                    lbool r = slv_for_prec->check_sat();
                    if (r == lbool::l_false)
                    {
                        std::cout << "!!! UNSAT of precs with replaced operands"  << std::endl;
                        std::cout << "ERROR!!!! TODO: simply check sat of prec " << r << std::endl;

                        break;

                        //unused
                        if (try_find_simultaneously_branches(synth_funs, constraints, 0, true))
                            return true;
                        continue;

                    }

                }
                if (DEBUG_MODE)
                {
                    //std::cout << "spec_with_coeff " << mk_ismt2_pp(spec_with_coeff, m, 3) << std::endl;
                   // std::cout << "spec_for_concrete_x " << mk_ismt2_pp(spec_for_concrete_x, m, 3) << std::endl;
                }


                /*
                 * [+] getting model for coefficients
                 * */
                if (current_iter_trivial_model_x++ < m_params.trivial_attempts_per_one_model_x())
                {
                    std::cout << "pushed heuristic constaraint for coeff" << std::endl;
                    is_added_heuristic = true;
                }

                //++current_iter_trivial_model_x;



                //

                expr_ref spec_with_coeff_and_x(m);
                invocations_rewriter inv_rwr(m_cmd, m);
                if (m_params.reused_brances())
                {
                    inv_rwr.rewriter_functions_to_linear_term_with_prec(m_coeff_decl_vec, synth_funs, spec_for_concrete_x, spec_with_coeff_and_x, *synth_fun_args, fn.get_precs(), fn.get_branches());
                }
                else
                {
                    inv_rwr.rewriter_functions_to_linear_term(m_coeff_decl_vec, synth_funs, spec_for_concrete_x, spec_with_coeff_and_x);
                }




                //[+] add mbp
                // expr_ref spec_with_coeff_and_x_mbp(m.mk_and(spec_with_coeff_and_x, result_mbp), m);
                //[-] mbp
                if (DEBUG_MODE)
                {
                   //// std::cout << "spec_with_coeff " << mk_ismt2_pp(spec_with_coeff_and_x, m) << std::endl;
                    //std::cout << "spec_for_concrete_x " << mk_ismt2_pp(spec_for_concrete_x, m, 3) << std::endl;
                }




                model_ref mdl_for_coeff = get_coeff_model(spec_with_coeff_and_x, is_added_heuristic ? heuristic_constaraint_coeff : expr_ref(m));
                is_added_heuristic = false;

                if (!mdl_for_coeff)
                {
                    std::cout << "WARNING!!! There are several branches. " << std::endl;

                    if (try_find_simultaneously_branches(synth_funs, constraints, mdl_for_x))
                        return true;

                    // TODO:???

                }
                std::cout << "SAT res_spec_for_x!! " << *mdl_for_coeff << std::endl;
                //simplify spec for concrete coef

                expr_ref branch = m_futils.generate_branch(m_coeff_decl_vec, *synth_fun_args, synth_funs, mdl_for_coeff);

                /*expr_ref additional_cond = generate_fun_macros(branch, synth_funs, *synth_fun_args);
                expr_ref simplified_spec = m_utils.simplify_context_cond(spec, additional_cond);
                std::cout << "simplified_spec for concrete coeff " << mk_ismt2_pp(simplified_spec, m, 3) << std::endl;*/


                /*[+] Find a precondition*/
                //[+] add mbp
                expr_ref spec_and_mbp(m.mk_and(spec, result_mbp), m);
                //[-] mbp
                bool prec_res = find_precondition(synth_funs, spec_and_mbp, mdl_for_coeff, last_precond, mdl_for_x);
                std::cout << " prec_res " << prec_res << std::endl;
                if (!prec_res)
                {
                    if (try_find_simultaneously_branches(synth_funs, constraints, mdl_for_x, true))
                        return true;
                }
                else
                {

                    //reset model x
                    //current_iter_model_x = 1000000;
                }

                if (m_utils.is_unsat(last_precond))
                {
                    last_precond = 0;
                    std::cout << "!!! Precond is unsat" << std::endl;
                    continue;
                }

                //current_iter_model_x = UINT_MAX - 1; // reset model X

                if (m_utils.is_unsat(m.mk_not(last_precond)))
                    //if(m.is_true(last_precond))
                {
                    fn.clear();
                    fn.add_branch(m.mk_true(), branch);
                    completed_solving(synth_funs, constraints, fn.generate_clia_fun_body(false));
                    return true;
                }


                fn.add_branch(last_precond, branch);

                /*[-] */
                if (DEBUG_MODE)
                {
                  //  std::cout << "-------------------" << std::endl;
                  //  std::cout << mk_ismt2_pp(last_precond, m, 0) << "  ==> " << mk_ismt2_pp(fn.get_branches().back(), m, 0) << std::endl;
                }
                //if (fn.is_completed())
                {
                    if (try_find_simultaneously_branches(synth_funs, constraints, 0))
                        return true;
                }
                std::cout << "-------------------" << std::endl;


            }
        }
        return false;
    }
    bool misynth_solver::try_find_simultaneously_branches(func_decl_ref_vector & synth_funs, expr_ref_vector & constraints, model_ref mdl_for_x, bool is_infinity_loop)
    {

        std::cout << "====== Checking a completion condition ======" << std::endl;
        args_t *synth_fun_args = get_args_decl_for_synth_fun(synth_funs.get(0));


        search_simultaneously_branches search(m_cmd, m);
        int is_added_heuristic = m_params.type_heuristic_branches();

        unsigned int iter = 0;


        //expr_ref_vector local_branches(m), local_precs(m);

        ite_function source_fn(m_cmd, m);
        ite_function result_fn(m_cmd, m);

        result_fn.unite(fn);


        if (m_params.reused_brances())
        {
            if (!m_params.clear_run_alg2())
            {
                source_fn.unite(fn);
            }

        }
        if (mdl_for_x.get())
        {
            is_infinity_loop = true; // if alg1 gave a model
            std::cout << "start search_simultaneously_branches with mdl: " << *mdl_for_x << std::endl;

            search(synth_funs, constraints, mdl_for_x, *synth_fun_args, source_fn, result_fn, is_added_heuristic);
            /* m_slv_for_prec_completing_cond = m_cmd.get_solver_factory()(m, params_slv, false, true, false, symbol::null);
             for (expr * e : local_precs)
             {
                 m_slv_for_prec_completing_cond->push();
                 m_slv_for_prec_completing_cond->assert_expr(m.mk_not(e));
                 std::cout << "prec " << mk_ismt2_pp(e, m, 3) << std::endl;
             }*/
        }


        bool is_incorrect_partial_prorgram = false;
        std::cout << "trying to start main while loop for search simult. "  << std::endl;
        sanity_checker sanity(m_cmd, m);
        while (is_infinity_loop || result_fn.is_empty() || result_fn.is_completed() || is_incorrect_partial_prorgram)
        {
//            std::cout << "###source_fn:  " <<  mk_ismt2_pp(source_fn.generate_clia_fun_body(true), m, 3) << std::endl;
            if (iter >= m_params.trivial_attempts_simultaneously_branches())
            {
                is_added_heuristic = 0;
            }
            // else ++is_added_heuristic;

            std::cout << "====== Completing condition is sat! ======"  << std::endl;
            expr_ref fun_body = result_fn.generate_clia_fun_body(m_params.compact());
//            std::cout << "###current result_fn:  " <<  mk_ismt2_pp(fun_body, m, 3) << std::endl;
            bool sanity_res = sanity.check(constraints, m_used_vars, fun_body, synth_funs, *synth_fun_args, mdl_for_x);
            if (sanity_res)
            {
                if (!result_fn.is_completed())
                {
                    is_incorrect_partial_prorgram = false;
                }
                else
                {
                    fn = result_fn;
                    completed_solving(synth_funs, constraints, fun_body);
                    return true;
                }
            }
            else
            {
                //if (is_incorrect_partial_prorgram)
                std::cout << "====== Sanity failed, start   search_simultaneously_branches for model X: "
                          << std::endl  << *mdl_for_x << std::endl;

                /*local_fn.clear();
                if (m_params.reused_brances())
                {
                    local_fn.unite(fn);
                }*/

                alg3_run++;
                search(synth_funs, constraints, mdl_for_x, *synth_fun_args, source_fn, result_fn, is_added_heuristic);

                if (result_fn.is_empty())
                {
                    sanity.reset_constraint_for_model_x();
                }

            }

            iter++;
        }
        std::cout << "====== Completing condition is unsat! ======"  << std::endl;
        return false;
    }

//    double all_time_simplify = 0;
    bool misynth_solver::completed_solving(func_decl_ref_vector & synth_funs, expr_ref_vector & constraints, expr_ref fun_body)
    {
        args_t *synth_fun_args = get_args_decl_for_synth_fun(synth_funs.get(0));
        std::cout << "Incompact solution: \n";
//        clock_t start = clock();
        print_def_fun(std::cout, synth_funs.get(0), *synth_fun_args, fun_body);


        sanity_checker sanity(m_cmd, m);
        bool sanity_res = sanity.check(constraints, fun_body, synth_funs, *synth_fun_args);
        std::cout << "Sanity Checker Result: " << sanity_res << std::endl;
        std::cout << iters_main_alg << " " << max_iter_iso_mor << " " << fn.get_incompact_depth()  << std::endl;
//        std::cout  << "Number of 2 algorithm runs : " << alg3_run << std::endl;
//        std::cout  << " all_time_coeff_model: " << all_time_coeff_model << std::endl;
//        std::cout << "time sanity.check : " << ((double)(clock() - start) / CLOCKS_PER_SEC) << std::endl;;
//         std::cout  << " all_time_simplify: " << all_time_sanity_ck << std::endl;
        return sanity_res;
    }

    bool misynth_solver::find_precondition(func_decl_ref_vector & synth_funs, expr_ref & spec, model_ref mdl_for_coeff, expr_ref &res,  model_ref mdl_for_x)
    {
//        std::cout << "+++++ [+] Find a precondition +++++++" << std::endl;

        vector<invocation_operands> current_ops;
        app_ref_vector current_invocations(m);
        collect_invocation_operands(spec, synth_funs, current_ops);
        collect_invocation(spec, synth_funs, current_invocations);
      
        args_t *synth_fun_args = get_args_decl_for_synth_fun(synth_funs.get(0));
        //[+]simplifying
        expr_ref branch = m_futils.generate_branch(m_coeff_decl_vec, *synth_fun_args, synth_funs, mdl_for_coeff);

        expr_ref additional_cond = m_futils.generate_fun_macros(branch, synth_funs, *synth_fun_args);

        //expr_ref additional_cond2 = m_utils.get_logic_model_with_default_value(mdl_for_x, m_used_vars);
        //spec = m_utils.simplify_context_cond(spec, additional_cond2);
//        std::cout << "Before spec: " << mk_smt_pp(spec, m) << std::endl;
      //        spec = m_utils.simplify_context_cond(spec, additional_cond);      // GF: disabled

        //std::cout << "additional_cond: " << mk_smt_pp(additional_cond, m) << std::endl;
//        std::cout << "After spec: " << mk_smt_pp(spec, m) << std::endl;
        //[-]simplifying


        expr_ref spec_with_coeff(m);
        invocations_rewriter inv_rwr(m_cmd, m);

        expr_ref spec_for_concrete_coeff(m);
        expr_ref_vector concrete_coeff =  m_utils.get_vars_according_to_model(mdl_for_coeff, m_coeff_decl_vec, true);
        inv_rwr.rewriter_functions_to_linear_term(concrete_coeff, synth_funs, spec, spec_for_concrete_coeff);

        //inv_rwr.rewriter_functions_to_linear_term(m_coeff_decl_vec, synth_funs, spec, spec_with_coeff);

        //expr_ref spec_for_concrete_coeff = m_utils.replace_vars_according_to_model(spec_with_coeff, mdl_for_coeff, m_coeff_decl_vec, true);
 //       std::cout << "spec_for_concrete_coeff: " << mk_ismt2_pp(spec_for_concrete_coeff, m, 3) << std::endl;
//        clock_t start = clock();
        expr_ref th_res = m_utils.simplify(spec_for_concrete_coeff);
        //std::cout << "spec_for_concrete_coeff2 " << mk_ismt2_pp(th_res2, m, 3) << std::endl;
        if (m_params.simplify_prec()) th_res = m_utils.simplify_context(th_res);

//        std::cout << "time : " << ((double)(clock() - start) / CLOCKS_PER_SEC) << std::endl;;
//        all_time_simplify += ((double)(clock() - start) / CLOCKS_PER_SEC);
  //      std::cout << "Simplified precondition candidate: " << mk_ismt2_pp(th_res, m, 3) << std::endl;
        //

        if (m_utils.is_unsat(th_res))
        {
            res = th_res;
            return true;
        }

        decl_collector decls(m);
        decls.visit(th_res);
        func_decl_ref_vector used_vars(m);

        for (func_decl *fd :  decls.get_func_decls())
        {
            if (!synth_funs.contains(fd))
            {
                used_vars.push_back(fd);
            }
        }


        expr_ref new_branch = m_futils.generate_branch(m_coeff_decl_vec, *synth_fun_args, synth_funs, mdl_for_coeff);
        // expr_ref res(m);
        if (current_ops.size() == 0)
        {
//            std::cout << "PREC has no invocation" << std::endl;
            res = th_res;
//            std::cout << "+++++ [-] Find a precondition +++++++" << std::endl;
            return true;
        }

        // some optimization for si
//        if (current_ops.size() == 1)
//        {
//            std::cout << "PREC is SI" << std::endl;
//            res = th_res;
//            return true;
//        }
//
//        // some optimization
//        if (used_vars.size() == 0 || (synth_fun_args->size() == 1 && used_vars.size() == 1))
//        {
//            res = m_utils.replace_vars_decl(th_res, used_vars, *synth_fun_args);
//
//            if (DEBUG_MODE)
//            {
//                std::cout << "used_vars.size() <= args.size()" << std::endl;
//
//            }
//
//            app_ref_vector invocations(m);
//            collect_invocation(spec, synth_funs, invocations);
//            auto res_abd = check_all_abductions(synth_funs, spec, invocations, res, new_branch);
//            if (res_abd == result_incremental_abd::total_false)
//            {
//                return  false;
//            }
//        }
//        else
//        {{
//            /*//[+]sample
//            func_decl_ref_vector sample_pattern(m);
//            func_decl *x_decl = m.mk_const_decl("x", m_arith.mk_int());
//            sample_pattern.push_back(x_decl);
//            func_decl *y_decl = m.mk_const_decl("y", m_arith.mk_int());
//            //etalon.push_back(y_decl);
//
//            expr_ref s(m);
//
//            expr_ref_vector r_x(m);
//            r_x.push_back(m.mk_const(x_decl));
//
//            expr_ref_vector r_y(m);
//            r_y.push_back(m.mk_const(y_decl));
//
//
//            vector<expr_ref_vector> inv_args;
//            inv_args.push_back(r_x);
//            inv_args.push_back(r_y);
//
//            expr_ref sample_expr(m_arith.mk_ge(m_arith.mk_add(m.mk_const(x_decl), m.mk_const(y_decl)), m_arith.mk_int(10)), m);
//            expr_ref res2 = m_abducer.nonlinear_abduce(inv_args, expr_ref(m.mk_true(), m), sample_expr, sample_pattern);
//            std::cout << "Sample x+y>=10: " << mk_ismt2_pp(sample_expr, m, 3) << mk_ismt2_pp(res2, m, 3) << std::endl;
//
//            //[-]
//            */
//        }
//            if (m.is_or(th_res))
//            {
//
//                for (unsigned int i = 0; i < to_app(th_res)->get_num_args(); ++i)
//                {
//                    expr_ref  arg(to_app(th_res)->get_arg(i), m);
//                    res = m_abducer.nonlinear_abduce(current_ops, expr_ref(m.mk_true(), m), arg, *synth_fun_args);
//                    if (!m_utils.is_unsat(res))
//                        return true;
//                    else
//                    {
//                        std::cout << "unsat candidate" << std::endl;
//                    }
//                }
//                // we take first argument
//
//            }
//            else
//            {
                if (m_params.incremental_multiabduction())
                {
                    result_incremental_abd res_abd = incremental_multiabduction(synth_funs, spec, new_branch, current_invocations, res);
  //                  std::cout << "incremental_multiabduction: " << mk_ismt2_pp(res, m, 3) << std::endl;
                    if (res_abd == result_incremental_abd::total_false)
                    {
                        return  false;
                    }
                }
                else
                {
                      res = m_abducer.nonlinear_abduce(current_ops, expr_ref(m.mk_true(), m), th_res, *synth_fun_args);
                }
//            }
//
//            //lit(x1) /\ lit(x2) => phi(x1, x2)
//            //try_to_separate_into_disjoint_sets();
//        }
//        std::cout << "+++++ [-] Find a precondition +++++++" << std::endl;

        return true;
    }




    args_t *misynth_solver::get_args_decl_for_synth_fun(func_decl * f)
    {
        return m_synth_fun_args_decl[f];
    }

    bool misynth_solver::prove_unrealizability_with_mdl(expr_ref spec, model_ref & mdl)
    {
        expr_ref logic_mdl(m);
        //model2expr(mdl, logic_mdl);
        logic_mdl = m_utils.get_logic_model_with_default_value(mdl, m_used_vars);

        if (m_utils.is_unsat(m.mk_and(spec, logic_mdl)))
        {
            if (VERBOSE)
            {
                std::cout << "Unrealizability!!! Specification is unsat. \n  with model: " << mk_ismt2_pp(logic_mdl, m, 3) << std::endl;
            }

            return true;
        }
        return false;
    }
    bool misynth_solver::prove_unrealizability_simple(expr_ref spec)
    {

        if (m_utils.is_unsat(spec))
        {
//            if (VERBOSE)
            {
                std::cout << "Unrealizability!!! Specification is unsat. \n  with model: " << mk_ismt2_pp(spec, m, 3) << std::endl;
            }

            return true;
        }
        return false;
    }
    bool misynth_solver::prove_unrealizability(expr_ref spec)
    {
//        std::cout << "prove_unrealizability: " << mk_ismt2_pp(spec, m, 3) << std::endl;

        if (m_utils.is_unsat(spec))
        {
//            if (VERBOSE)
            {
                std::cout << "Unrealizability!!! Specification is unsat \n. " << mk_ismt2_pp(spec, m, 3) << std::endl;
            }

            return true;
        }

        //expr_ref_vector assumptions(m);
        generate_assumptions_from_operands(m_assumptions);

        if (VERBOSE)
        {
            for (unsigned int i = 0; i < m_assumptions.size(); ++i)
            {
                std::cout << "assumptions: " << mk_ismt2_pp(m_assumptions.get(i), m, 3) << std::endl;
            }
        }
        if (m_params.check_assumptions())
            return check_assumptions(spec, m_assumptions);
        else
            return false;
    }

    bool misynth_solver::check_assumptions(expr_ref spec, expr_ref_vector & assumptions)
    {
        params_ref params;
        ref<solver> slv = m_cmd.get_solver_factory()(m, params, false, true, false, symbol::null);
        return subsets_backtracking(assumptions, spec, slv.get(), 0);
    }

    bool misynth_solver::subsets_backtracking(expr_ref_vector & assump, expr * spec, solver * slv, unsigned int index)
    {
        if (index > 0)
        {
            if (slv->check_sat() == lbool::l_false)
            {
                // Next any superset is unsat
                return false;

            }
            else
            {

                slv->push();
                slv->assert_expr(spec);

                if (slv->check_sat() == lbool::l_false)  // unsat -- unrealizability
                {
                    slv->pop(1);

                    if (VERBOSE)
                    {

                        std::cout << "Unrealizability!!! Specification is unsat. \n Unrealizability assumptions:" << std::endl;

//                        for (unsigned i = 0; i < slv->get_num_assertions(); ++i)
//                        {
//                            std::cout << mk_ismt2_pp(slv->get_assertion(i), m, 3) << std::endl;
//                        }
                    }

                    return true;
                }
                /*else
                {
                    model_ref mdl;
                    slv->get_model(mdl);
                    m_models_from_assumptions.push_back(mdl);
                }*/

                slv->pop(1);
            }
        }

        for (unsigned int i = index; i < assump.size(); ++i)
        {

            // include the A[i] in subset.
            slv->push();
            slv->assert_expr(assump.get(i));



            // move onto the next element.
            if (subsets_backtracking(assump, spec, slv, i + 1))
            {
                return true;
            }

            // exclude the A[i] from subset and triggers backtracking.
            slv->pop(1);
        }

        return false;
    }

    void misynth_solver::generate_assumptions_from_operands(expr_ref_vector & assumptions)
    {
        for (unsigned int i = 0; i < m_ops.size(); ++i)
        {
            for (unsigned int j = 0; j < i; ++j)
            {
                expr_ref eq = m_utils.mk_eq(m_ops.get(i), m_ops.get(j));

                if (m_utils.is_sat(eq))
                {
                    assumptions.push_back(eq);
                }
            }
        }
    }

    void misynth_solver::print_def_fun(std::ostream & out, func_decl * f, func_decl_ref_vector & args, expr_ref body)
    {
        out << "(define-fun " << f->get_name() << " (";
        m_utils.print_sorted_var_list(out, args);
        out << ") " << f->get_range()->get_name() << " ";
        out << mk_ismt2_pp(body, m, 0);
        out << ") " << std::endl;
    }

    expr_ref misynth_solver::generate_heuristic_constaraint_coeff(expr_ref spec, func_decl_ref_vector & coeff_decls)
    {
        if (heuri == 1)
        {
            expr_ref_vector v(m);
            //for (func_decl * fd : coeff_decls)
            for (unsigned int i = 0; i < coeff_decls.size(); i++)
            {
                func_decl * fd = coeff_decls.get(i);
                expr_ref e(m.mk_const(fd), m);
                v.push_back(m.mk_or(
                                m.mk_eq(e, m_arith.mk_int(-1)),
                                m.mk_eq(e, m_arith.mk_int(0)),
                                m.mk_eq(e, m_arith.mk_int(1))
                            ));
            }
            //v.reverse();
            return m_utils.dis_join(v);
        }
        else if (heuri == 2)
        {
            expr_ref_vector v(m);
            //for (func_decl * fd : coeff_decls)
            for (unsigned int i = 0; i < coeff_decls.size(); i++)
            {
                func_decl * fd = coeff_decls.get(i);
                expr_ref e(m.mk_const(fd), m);
                v.push_back(m.mk_or(
                                m.mk_eq(e, m_arith.mk_int(-1)),
                                m.mk_eq(e, m_arith.mk_int(0)),
                                m.mk_eq(e, m_arith.mk_int(1))
                            ));
            }
            //v.reverse();
            return m_utils.con_join(v);
        }
        else
        {
            expr_set constants_set;
            collect_consts(spec, constants_set, m);
            expr_ref_vector v(m);
            //for (func_decl * fd : coeff_decls)
            for (unsigned int i = 0; i < coeff_decls.size(); i++)
            {
                func_decl * fd = coeff_decls.get(i);
                expr_ref e(m.mk_const(fd), m);
                expr_ref_vector disj(m);
                disj.push_back(m.mk_eq(e, m_arith.mk_int(-1)));
                disj.push_back(m.mk_eq(e, m_arith.mk_int(0)));
                disj.push_back(m.mk_eq(e, m_arith.mk_int(1)));
                for (auto it = constants_set.begin(); it != constants_set.end(); it++)
                {
                    disj.push_back(m.mk_eq(e, *it));
                    disj.push_back(m.mk_eq(e, m_arith.mk_uminus(*it)));
                }
                v.push_back(m_utils.dis_join(disj));
            }
            //v.reverse();
            return m_utils.con_join(v);
        }
    }

    result_incremental_abd misynth_solver::check_all_abductions(func_decl_ref_vector & synth_funs, expr_ref & spec, app_ref_vector &invocations, expr_ref & new_prec, expr_ref & new_branch)
    {
        unsigned int k = invocations.size();
        unsigned int n = fn.get_incompact_depth();

        for (unsigned int i = 1; i <= k; ++i)
        {
            generator_combination_with_repetiton comb(k - i, n);
            while (comb.do_next())
            {
                vector<unsigned int> permutation = comb.get_next();
                permutation.resize(k, n);
                std::sort(permutation.begin(), permutation.end());
                do
                {
                    print_vector(permutation);
                    auto res = check_abduction_for_comb(permutation, synth_funs, spec, invocations, new_prec, new_branch);
                    if (res == result_incremental_abd::false_v)
                    {
//                        std::cout << "!!! ABDUCTION PROBLEM IS UNSAT" << std::endl;
                        return result_incremental_abd::false_v;

                    }
                    else if (res == result_incremental_abd::total_false)
                    {

//                        std::cout << "!!! CONCLUSION of ABDUCTION PROBLEM IS UNSAT" << std::endl;
                        return result_incremental_abd::total_false;

                    }

                }
                while (std::next_permutation(permutation.begin(), permutation.end()));

            }


        }
        return result_incremental_abd::true_v;
    }

    result_incremental_abd misynth_solver::check_abduction_for_comb(vector<unsigned int> &comb, func_decl_ref_vector & synth_funs, expr_ref & spec, app_ref_vector &invocations, expr_ref & new_prec, expr_ref & new_branch)
    {
        SASSERT(invocations.size() == comb.size());

        app2expr_map  term_subst;

        unsigned int n = fn.get_incompact_depth();

        vector<invocation_operands> current_ops;
        collect_invocation_operands(invocations, current_ops);
        args_t *synth_fun_args = get_args_decl_for_synth_fun(synth_funs.get(0));

        expr_ref_vector preds(m), temp(m);

        for (unsigned int i = 0; i < invocations.size(); ++i)
        {
            if (comb[i] == n)
            {
                expr_ref concrete_prec =  m_utils.replace_vars_decl(new_prec, *synth_fun_args, current_ops[i]);
                preds.push_back(concrete_prec);
                expr_ref concrete_branch =  m_utils.replace_vars_decl(new_branch, *synth_fun_args, current_ops[i]);
                temp.push_back(concrete_branch);
                term_subst.insert(invocations[i].get(), concrete_branch);
            }
            else
            {
                expr_ref concrete_prec =  m_utils.replace_vars_decl(fn.get_precs()[comb[i]].get(), *synth_fun_args, current_ops[i]);
                preds.push_back(concrete_prec);
                expr_ref concrete_branch =  m_utils.replace_vars_decl(fn.get_branches()[comb[i]].get(), *synth_fun_args, current_ops[i]);
                temp.push_back(concrete_branch);
                term_subst.insert(invocations[i].get(), concrete_branch);
            }
        }

        invocations_rewriter inv_rwr(m_cmd, m);
        expr_ref spec_with_branches(m);
        inv_rwr.rewrite_expr(spec, spec_with_branches, term_subst);
        expr_ref premise = m_utils.con_join(preds);
//        std::cout << "check_abduction_for_comb " << mk_ismt2_pp(premise, m) << " ==> " << mk_ismt2_pp(spec_with_branches, m) << std::endl;
//        if (m_utils.is_unsat(spec_with_branches))
//        {
//          std::cout << "  is unsat [1]\n";
//            return result_incremental_abd::total_false;
//        }

        if (m_utils.implies(premise, spec_with_branches)){
            return result_incremental_abd::true_v;
        }
        else {
            return result_incremental_abd::false_v;
        }
    }


    expr_ref misynth_solver::solve_abduction_for_comb(vector<unsigned int> &comb, func_decl_ref_vector & synth_funs, expr_ref & spec, app_ref_vector &invocations, expr_ref & new_branch)
    {
        SASSERT(invocations.size() == comb.size());
        app2expr_map  term_subst;
        vector<invocation_operands> current_ops;
        collect_invocation_operands(invocations, current_ops);

        args_t *synth_fun_args = get_args_decl_for_synth_fun(synth_funs.get(0));

        vector<invocation_operands> unknown_pred;
        unsigned int n = fn.get_incompact_depth();
//        std::cout << " n " << n << std::endl;
        expr_ref_vector known_pred(m), temp(m);
        for (unsigned int i = 0; i < invocations.size(); ++i)
        {
            if (comb[i] == n)
            {

                unknown_pred.push_back(current_ops[i]);
                expr_ref concrete_branch =  m_utils.replace_vars_decl(new_branch, *synth_fun_args, current_ops[i]);
                temp.push_back(concrete_branch);
                term_subst.insert(invocations[i].get(), concrete_branch);
            }
            else
            {
                expr_ref concrete_prec =  m_utils.replace_vars_decl(fn.get_precs()[comb[i]].get(), *synth_fun_args, current_ops[i]);
                known_pred.push_back(concrete_prec);
                expr_ref concrete_branch =  m_utils.replace_vars_decl(fn.get_branches()[comb[i]].get(), *synth_fun_args, current_ops[i]);
                expr_ref concrete_pre = m_utils.replace_vars_decl(fn.get_precs()[comb[i]].get(), *synth_fun_args, current_ops[i]);
                temp.push_back(concrete_branch);
                term_subst.insert(invocations[i].get(), concrete_branch);
            }

        }

        invocations_rewriter inv_rwr(m_cmd, m);
        expr_ref spec_with_branches(m);
        inv_rwr.rewrite_expr(spec, spec_with_branches, term_subst);
        expr_ref res = m_abducer.nonlinear_abduce(unknown_pred, m_utils.con_join(known_pred), spec_with_branches, *synth_fun_args);
        return res;
    }

  
    result_incremental_abd misynth_solver::incremental_multiabduction(func_decl_ref_vector &synth_funs, expr_ref & spec, expr_ref & new_branch, app_ref_vector &invocations, expr_ref &result)
    {
//        app_ref_vector invocations(m);
//        collect_invocation(spec, synth_funs, invocations);

        unsigned int k = invocations.size();
        unsigned int n = fn.get_incompact_depth();
        /*generator_permutation_with_repetitions comb(current_ops.size(), fn.get_incompact_depth());

         while (comb.do_next())
         {
             vector<unsigned int> v = comb.get_next();
             int freq = std::count(v.begin(), v.end(), n);
         }*/

//      std::cout << "k = " << k << "; n = " << n << std::endl; // GF: here
      expr_ref res(m.mk_true(), m);
        if (n == 0)
        {
            /*vector<invocation_operands> current_ops;
            collect_invocation_operands(invocations, current_ops);
            return  m_abducer.nonlinear_abduce(current_ops, expr_ref(m.mk_true(), m), spec, *synth_fun_args);*/
            vector<unsigned int> permutation(k, n);
            res = solve_abduction_for_comb(permutation, synth_funs, spec, invocations, new_branch);
//            return result_incremental_abd::true_v;
        }
      else
      {
        //increase "complexity" multiabduction
        // i - number of unknown predicates
//        int cnt = 0;
//      expr_ref res(m.mk_true(), m);
        for (int i = 1; i <= k; ++i)
        {
//            std::cout << "k   "   << std::endl;
            generator_combination_with_repetiton comb(k - i, n);
            while (comb.do_next())
            {
//                std::cout << "k :  " << i  << std::endl;
                //print_vector(comb.get_next());
                vector<unsigned int> permutation = comb.get_next();
                permutation.resize(k, n);
                std::sort(permutation.begin(), permutation.end());
                do
                {
                    //todo
//                    print_vector(permutation);
                  auto already_good = check_abduction_for_comb(permutation, synth_funs, spec, invocations, res, new_branch);
                  if (already_good == result_incremental_abd::false_v)
                  {
                    expr_ref potential_prec = solve_abduction_for_comb(permutation, synth_funs, spec, invocations, new_branch);
                    res = m.mk_and(res, potential_prec);
                  }
                }
                while (std::next_permutation(permutation.begin(), permutation.end()));
            }
        }
      }
//        std::cout << "All abduction problems have been enumerated"  << std::endl;
        //[-]

        // sanity check
        for (int i = 1; i <= k; ++i)
        {
          generator_combination_with_repetiton comb(k - i, n);
          while (comb.do_next())
          {
            vector<unsigned int> permutation = comb.get_next();
            permutation.resize(k, n);
            std::sort(permutation.begin(), permutation.end());
            do
            {
              if (check_abduction_for_comb(permutation, synth_funs, spec, invocations, res, new_branch) == result_incremental_abd::false_v)
              {
                return result_incremental_abd::total_false;
              }
            }
            while (std::next_permutation(permutation.begin(), permutation.end()));
          }
        }

        //expr_ref res(m.mk_false(), m);
        result = res;

        return result_incremental_abd::false_v;
    }
} // namespace misynth
