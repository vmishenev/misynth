#ifndef ITE_FUNCTION_H
#define ITE_FUNCTION_H

#include "cmd_context/cmd_context.h"
#include "misynth/smt_utils.h"

#include <set>

namespace misynth
{


    class ite_function
    {
        private:
            cmd_context &m_cmd;
            ast_manager &m;
            expr_ref_vector m_precs, m_branches;
            ref<solver> slv_for_prec;

            params_ref m_slv_params;

            smt_utils m_utils;


        public:

            ite_function(cmd_context &cmd_ctx, ast_manager &m)
                : m_cmd(cmd_ctx),
                  m(m),
                  m_precs(m),
                  m_branches(m),
                  m_utils(cmd_ctx, m)
            {

                slv_for_prec = m_cmd.get_solver_factory()(m, m_slv_params, false, true, false, symbol::null);

            }

            ite_function& operator=(ite_function& other)
            {

                if (&other == this)
                    return *this;
                clear();
                add_branches(other.get_precs(), other.get_branches());
                return *this;
            }

            void add_branches(const expr_ref_vector & precs, const expr_ref_vector & brs)
            {
                m_precs.append(precs);
                m_branches.append(brs);

                for (expr *p : precs)
                {
                    slv_for_prec->push();
                    slv_for_prec->assert_expr(m.mk_not(p));
                }
            }

            void add_branch(expr * prec, expr * br)
            {
                SASSERT(precs.size() == m_branches.size());

                slv_for_prec->push();
                slv_for_prec->assert_expr(m.mk_not(prec));

                m_precs.push_back(prec);
                m_branches.push_back(br);
            }

            bool is_completed()
            {
                return slv_for_prec->check_sat() == lbool::l_false;
            }
            void clear()
            {
                m_precs.reset();
                m_branches.reset();
                slv_for_prec = m_cmd.get_solver_factory()(m, m_slv_params, false, true, false, symbol::null);


            }

            expr_ref_vector &get_precs()
            {
                return m_precs;
            }

            expr_ref_vector &get_branches()
            {
                return m_branches;
            }

            void unite(ite_function &other)
            {
                add_branches(other.get_precs(), other.get_branches());
            }

            unsigned int get_incompact_depth()
            {
                return m_precs.size();
            }

            bool is_empty()
            {
                return m_precs.size() == 0;
            }
            ite_function remove_branches(vector<unsigned int> &idxs)
            {
                ///ite_function tmp(m_cmd, m);//nrvo
                ///
                for (unsigned int i : idxs)
                {
                    //m_precs[i] = m.mk_false();
                    std::cout << "remove branche:" <<  mk_ismt2_pp(m_precs.get(i), m, 0) << std::endl;
                    m_precs.set(i, m.mk_false());

                }
                slv_for_prec = m_cmd.get_solver_factory()(m, m_slv_params, false, true, false, symbol::null);
                for (expr *p : m_precs)
                {
                    slv_for_prec->push();
                    slv_for_prec->assert_expr(m.mk_not(p));
                }
                return *this;
            }
            expr_ref generate_clia_fun_body(bool is_compact)
            {
                SASSERT(m_precs.size() == m_branches.size());
                expr_ref res(m);
                if (m_precs.size() == 0) return res;




                std::set<unsigned int> todo_remove;
                //[+] compaction
                if (is_compact)
                {


                    for (unsigned int i = 0 ; i < m_precs.size() - 1; ++i)
                    {
                        if (todo_remove.find(i) != todo_remove.end())
                        {
                            continue;
                        }
                        for (unsigned int j = 0 ; j < m_precs.size(); ++j)
                        {
                            if (i != j)
                            {
                                if (todo_remove.find(j) != todo_remove.end())
                                {
                                    continue;
                                }
                                if (m_utils.implies(m_precs.get(i), m_precs.get(j)))
                                {
                                    //std::cout << "remove " <<  mk_ismt2_pp(m_precs.get(j), m, 0)
                                    //          << " ===> " << mk_ismt2_pp(m_precs.get(i), m, 0) << std::endl;
                                    todo_remove.insert(i);
                                    break;
                                }
                                else if (m_utils.implies(m_precs.get(j), m_precs.get(i)))
                                {
                                    todo_remove.insert(j);
                                    //std::cout << "remove " <<  mk_ismt2_pp(m_precs.get(i), m, 0)
                                    //         << " ===> " << mk_ismt2_pp(m_precs.get(j), m, 0) << std::endl;

                                }

                            }
                        }
                    }
                }
                //[-] compaction


                for (unsigned int i = m_precs.size() - 1 ; i < m_precs.size(); --i)
                {
                    if (todo_remove.find(i) != todo_remove.end())
                    {
                        continue;
                    }

                    // for incompleted function
                    if (! is_completed())
                    {
                        res = m_utils.get_non_deter_const();
                        res = m.mk_ite(m_precs.get(i), m_branches.get(i), res);
                    }
                    else
                        res = m_branches.get(i);

                    break;
                }

                //expr_ref_vector v(m);

                for (unsigned int i = 0 ; i < m_precs.size() - 1; ++i)
                {
                    if (todo_remove.find(i) != todo_remove.end())
                    {
                        continue;
                    }
                    res = m.mk_ite(m_precs.get(i), m_branches.get(i), res);
                }



                return res;
            }

    };

}


#endif // ITE_FUNCTION_H
