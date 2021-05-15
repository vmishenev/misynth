#ifndef INVOCATION_OPERANDS_COLLECTOR_H_
#define INVOCATION_OPERANDS_COLLECTOR_H_

#include "ast/ast.h"
#include "ast/expr_delta_pair.h"
#include "util/hashtable.h"
#include "ast/ast_pp.h"
#include "model/model.h"
#include "smt_utils.h"

typedef expr_ref_vector invocation_operands;

class invocation_collector
{
    private:
        //typedef hashtable<symbol, symbol_hash_proc, symbol_eq_proc> symbol_set;
        typedef obj_hashtable<app > app_set;

        func_decl_ref_vector&   m_fun_list;
        app_set                 m_invocations;
        obj_hashtable<expr>     m_visited;
        ptr_vector<expr>        m_todo;



        void visit(expr * n)
        {
            if (!m_visited.contains(n))
            {
                m_visited.insert(n);
                m_todo.push_back(n);
            }
        }

    public:
        invocation_collector(func_decl_ref_vector&   fun_list):
            m_fun_list(fun_list)
        {
        }

        void operator()(expr * n, bool ignore_quantifiers = false)
        {
            m_visited.reset();
            m_invocations.reset();
            m_todo.reset();
            visit(n);
            while (!m_todo.empty())
            {
                n = m_todo.back();
                m_todo.pop_back();
                unsigned j;
                switch (n->get_kind())
                {
                    case AST_APP:
                        {
                            app *app_n = to_app(n);
                            if (m_fun_list.contains(app_n->get_decl()))
                            {
                                m_invocations.insert(app_n);
                            }
                            else
                            {
                                j = to_app(n)->get_num_args();
                                while (j > 0)
                                {
                                    --j;
                                    visit(to_app(n)->get_arg(j));
                                }
                            }
                            break;
                        }
                    case AST_QUANTIFIER:
                        if (!ignore_quantifiers)
                        {

                            //unsigned num_decls = to_quantifier(n)->get_num_decls();
                            //for (unsigned i = 0; i < num_decls; i++)
                            //found(to_quantifier(n)->get_decl_name(i));
                            unsigned num_pats = to_quantifier(n)->get_num_patterns();
                            for (unsigned i = 0; i < num_pats; i++)
                                visit(to_quantifier(n)->get_pattern(i));
                            unsigned num_no_pats = to_quantifier(n)->get_num_no_patterns();
                            for (unsigned i = 0; i < num_no_pats; i++)
                                visit(to_quantifier(n)->get_no_pattern(i));
                            visit(to_quantifier(n)->get_expr());
                        }
                        break;
                    default:
                        break;
                }
            }
        }

        app_set &get_invocation()
        {
            return m_invocations;
        }


};

void collect_invocation_operands(expr * n, func_decl_ref_vector&   fun_list, vector<invocation_operands> &l)
{
    l.reset();
    invocation_collector collector(fun_list);
//    std::cout << "------ [+] Collect invocation operands: -----"<< std::endl;
    collector(n);
    obj_hashtable<app > set = collector.get_invocation();
    for (auto it = set.begin(); it != set.end(); it++)
    {
        app * ap_f = (*it);
//        std::cout << "invocation: " << mk_ismt2_pp(ap_f, fun_list.get_manager(), 3) << std::endl;

        invocation_operands ops(fun_list.get_manager());
        ops.append(ap_f->get_num_args(), ap_f->get_args());
        l.insert(ops);
    }
//    std::cout << "------ [-] Collect invocation operands: -----"<< std::endl;
}


void collect_invocation_operands(app_ref_vector &apps, vector<invocation_operands> &l)
{

    for (auto it = apps.begin(); it != apps.end(); it++)
    {
        app * ap_f = (*it);


        invocation_operands ops(apps.get_manager());
        ops.append(ap_f->get_num_args(), ap_f->get_args());
        l.insert(ops);
    }
}
void collect_invocation(expr * n, func_decl_ref_vector&   fun_list,  app_ref_vector &l)
{
    invocation_collector collector(fun_list);
    collector(n);
    obj_hashtable<app > set = collector.get_invocation();
    for (auto it = set.begin(); it != set.end(); it++)
    {
        app * ap_f = (*it);
        l.push_back(ap_f);
    }
}



#endif
