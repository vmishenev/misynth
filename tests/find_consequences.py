import sys
from os import path
sys.path.insert(0, path.join('C:/tunable-static-analyzer/src'))
sys.path.insert(0, path.join('C:/debug/z3'))
from fol_ast import *
from fol_z3_converter import *
from z3 import *

def mk_array_type(d):
    arity = d.arity()
    srt = d.range()
    while arity > 0:
	s = d.domain(arity-1)
	arity -= 1
	srt = ArraySort(s, srt)
    return srt
    
def is_builtin(e):
    return is_not(e) or is_and(e) or is_or(e) or is_eq(e)

def to_array(e):
    if is_quantifier(e):
	vars = [Const(e.var_name(i), e.var_sort(i)) for i in range(e.num_vars())]
	body = e.body()
	body = to_array(body)
	if e.is_forall():
	    return ForAll(vars, body)
	else:
	    return Exists(vars, body)
    if is_var(e):
	return e
    chs = [to_array(ch) for ch in e.children()]
    if is_not(e):
	return Not(chs[0])
    if is_and(e):
	return And(chs)
    if is_or(e):
	return Or(chs)
    if is_eq(e):
	return chs[0] == chs[1]
    if len(chs) == 0:
	return e    
    d = e.decl()
    srt = mk_array_type(d)
    r = Const(d.name(), srt)
    for i in range(d.arity()):
	r = Select(r, chs[i])
    return r

def to_project(e, to_keep, to_proj):
    for ch in e.children():
	to_project(ch, to_keep, to_proj)
    if is_builtin(e):
	return
    if is_var(e):
	return
    if is_quantifier(e):
	return
    d = e.decl()
    if d.name() not in to_proj:
	if d.name() not in to_keep:
	    to_proj[d.name()] = e
    
	

def find_consequences(theory, back, c_keep, u_keep, b_keep):
    theory = to_array(clauses_to_z3(theory))
    back = to_array(clauses_to_z3(back))
    to_proj = {}
    to_keep = {}
    for c in c_keep + u_keep + b_keep + ['select', 'nstar']:
	to_keep[c] = 1
    to_project(theory, to_keep, to_proj)
    to_project(back, to_keep, to_proj)
    vars = [ to_proj[k] for k in to_proj ]
    print vars
    fml = Exists(vars, And(theory, back))
    s = Solver()
    s.add(fml)
    print s.to_smt2()

    
theory = to_clauses('[[r_x(last)], [~n_last(V)], [~=(x, last)]]')
background_theory = to_clauses('[[~nstar(A, B), ~nstar(B, A), =(A, B)], [nstar(A, A)], [~nstar(A, B), ~nstar(B, C), nstar(A, C)], [~nstar(A, B), ~nstar(A, C), nstar(B, C), nstar(C, B)], [~n_last(V), =(V, sk__n__last)], [~n_last(V), ~=(last, sk__n__last)], [=(last, sk__n__last), n_last(sk__n__last)], [nstar(last, sk__n__last)], [~nstar(last, V), =(last, V), nstar(sk__n__last, V)], [~nstar(last, V), =(last, V), ~=(sk__n__last, last)], [~n_x(V), =(V, sk__n__x)], [~n_x(V), ~=(x, sk__n__x)], [=(x, sk__n__x), n_x(sk__n__x)], [nstar(x, sk__n__x)], [~nstar(x, V), =(x, V), nstar(sk__n__x, V)], [~nstar(x, V), =(x, V), ~=(sk__n__x, x)], [~r_last(V), nstar(last, V)], [r_last(V), ~nstar(last, V)], [~r_x(V), nstar(x, V)], [r_x(V), ~nstar(x, V)]]')
constants_to_keep = ['last', 'x']
unary_to_keep = ['r_x', 'n_last', 'n_x', 'r_last']
binary_to_keep = ['nstar']

find_consequences(theory, background_theory, constants_to_keep, unary_to_keep, binary_to_keep)



theory = to_clauses('[[aux_join__()], [r_x(last)], [~n_last(V)], [~=(x, last)]]')
background_theory = to_clauses('[[~nstar(A, B), ~nstar(B, A), =(A, B)], [nstar(A, A)], [~nstar(A, B), ~nstar(B, C), nstar(A, C)], [~nstar(A, B), ~nstar(A, C), nstar(B, C), nstar(C, B)], [~n_last(V), =(V, sk__n__last)], [~n_last(V), ~=(last, sk__n__last)], [=(last, sk__n__last), n_last(sk__n__last)], [nstar(last, sk__n__last)], [~nstar(last, V), =(last, V), nstar(sk__n__last, V)], [~nstar(last, V), =(last, V), ~=(sk__n__last, last)], [~n_x(V), =(V, sk__n__x)], [~n_x(V), ~=(x, sk__n__x)], [=(x, sk__n__x), n_x(sk__n__x)], [nstar(x, sk__n__x)], [~nstar(x, V), =(x, V), nstar(sk__n__x, V)], [~nstar(x, V), =(x, V), ~=(sk__n__x, x)], [~r_last(V), nstar(last, V)], [r_last(V), ~nstar(last, V)], [~r_x(V), nstar(x, V)], [r_x(V), ~nstar(x, V)]]')
constants_to_keep = ['last', 'x']
unary_to_keep = ['r_x', 'n_last']
binary_to_keep = []


find_consequences(theory, background_theory, constants_to_keep, unary_to_keep, binary_to_keep)

theory = to_clauses('[[r_x(last)], [~n_last(V)], [~=(x, last)], [n_x(new_temp_new)]]')
background_theory = to_clauses('[[~nstar(A, B), ~nstar(B, A), =(A, B)], [nstar(A, A)], [~nstar(A, B), ~nstar(B, C), nstar(A, C)], [~nstar(A, B), ~nstar(A, C), nstar(B, C), nstar(C, B)], [~n_last(V), =(V, sk__n__last)], [~n_last(V), ~=(last, sk__n__last)], [=(last, sk__n__last), n_last(sk__n__last)], [nstar(last, sk__n__last)], [~nstar(last, V), =(last, V), nstar(sk__n__last, V)], [~nstar(last, V), =(last, V), ~=(sk__n__last, last)], [~new_n_temp_new(V), =(V, new_sk__n__temp_new)], [~new_n_temp_new(V), ~=(new_temp_new, new_sk__n__temp_new)], [=(new_temp_new, new_sk__n__temp_new), new_n_temp_new(new_sk__n__temp_new)], [nstar(new_temp_new, new_sk__n__temp_new)], [~nstar(new_temp_new, V), =(new_temp_new, V), nstar(new_sk__n__temp_new, V)], [~nstar(new_temp_new, V), =(new_temp_new, V), ~=(new_sk__n__temp_new, new_temp_new)], [~n_x(V), =(V, sk__n__x)], [~n_x(V), ~=(x, sk__n__x)], [=(x, sk__n__x), n_x(sk__n__x)], [nstar(x, sk__n__x)], [~nstar(x, V), =(x, V), nstar(sk__n__x, V)], [~nstar(x, V), =(x, V), ~=(sk__n__x, x)], [~r_last(V), nstar(last, V)], [r_last(V), ~nstar(last, V)], [~new_r_temp_new(V), nstar(new_temp_new, V)], [new_r_temp_new(V), ~nstar(new_temp_new, V)], [~r_x(V), nstar(x, V)], [r_x(V), ~nstar(x, V)]]')
constants_to_keep = ['new_temp_new', 'x', 'last']
unary_to_keep = ['r_x', 'n_x', 'new_r_temp_new', 'r_last', 'n_last', 'new_n_temp_new']
binary_to_keep = ['nstar']


find_consequences(theory, background_theory, constants_to_keep, unary_to_keep, binary_to_keep)


theory = to_clauses('[[aux_join__()], [r_x(last)], [~n_last(V)], [~=(x, last)], [n_x(temp)]]')
background_theory = to_clauses('[[~nstar(A, B), ~nstar(B, A), =(A, B)], [nstar(A, A)], [~nstar(A, B), ~nstar(B, C), nstar(A, C)], [~nstar(A, B), ~nstar(A, C), nstar(B, C), nstar(C, B)], [~n_last(V), =(V, sk__n__last)], [~n_last(V), ~=(last, sk__n__last)], [=(last, sk__n__last), n_last(sk__n__last)], [nstar(last, sk__n__last)], [~nstar(last, V), =(last, V), nstar(sk__n__last, V)], [~nstar(last, V), =(last, V), ~=(sk__n__last, last)], [~n_temp(V), =(V, sk__n__temp)], [~n_temp(V), ~=(temp, sk__n__temp)], [=(temp, sk__n__temp), n_temp(sk__n__temp)], [nstar(temp, sk__n__temp)], [~nstar(temp, V), =(temp, V), nstar(sk__n__temp, V)], [~nstar(temp, V), =(temp, V), ~=(sk__n__temp, temp)], [~n_x(V), =(V, sk__n__x)], [~n_x(V), ~=(x, sk__n__x)], [=(x, sk__n__x), n_x(sk__n__x)], [nstar(x, sk__n__x)], [~nstar(x, V), =(x, V), nstar(sk__n__x, V)], [~nstar(x, V), =(x, V), ~=(sk__n__x, x)], [~r_last(V), nstar(last, V)], [r_last(V), ~nstar(last, V)], [~r_temp(V), nstar(temp, V)], [r_temp(V), ~nstar(temp, V)], [~r_x(V), nstar(x, V)], [r_x(V), ~nstar(x, V)]]')
constants_to_keep = ['temp', 'x', 'last']
unary_to_keep = ['r_x', 'n_last', 'n_x']
binary_to_keep = []


find_consequences(theory, background_theory, constants_to_keep, unary_to_keep, binary_to_keep)

theory = to_clauses('[[r_x(last)], [~n_last(V)], [~=(x, last)], [n_x(temp)], [~new_nstar_new(A, B), nstar(A, B)], [~new_nstar_new(A, B), ~nstar(A, x), ~nstar(x, B), =(x, B)], [new_nstar_new(A, B), ~nstar(A, B), nstar(A, x)], [new_nstar_new(A, B), ~nstar(A, B), nstar(x, B)], [new_nstar_new(A, x), ~nstar(A, x)]]')
background_theory = to_clauses('[[~nstar(A, B), ~nstar(B, A), =(A, B)], [nstar(A, A)], [~nstar(A, B), ~nstar(B, C), nstar(A, C)], [~nstar(A, B), ~nstar(A, C), nstar(B, C), nstar(C, B)], [~n_last(V), =(V, sk__n__last)], [~n_last(V), ~=(last, sk__n__last)], [=(last, sk__n__last), n_last(sk__n__last)], [nstar(last, sk__n__last)], [~nstar(last, V), =(last, V), nstar(sk__n__last, V)], [~nstar(last, V), =(last, V), ~=(sk__n__last, last)], [~n_temp(V), =(V, sk__n__temp)], [~n_temp(V), ~=(temp, sk__n__temp)], [=(temp, sk__n__temp), n_temp(sk__n__temp)], [nstar(temp, sk__n__temp)], [~nstar(temp, V), =(temp, V), nstar(sk__n__temp, V)], [~nstar(temp, V), =(temp, V), ~=(sk__n__temp, temp)], [~n_x(V), =(V, sk__n__x)], [~n_x(V), ~=(x, sk__n__x)], [=(x, sk__n__x), n_x(sk__n__x)], [nstar(x, sk__n__x)], [~nstar(x, V), =(x, V), nstar(sk__n__x, V)], [~nstar(x, V), =(x, V), ~=(sk__n__x, x)], [~r_last(V), nstar(last, V)], [r_last(V), ~nstar(last, V)], [~r_temp(V), nstar(temp, V)], [r_temp(V), ~nstar(temp, V)], [~r_x(V), nstar(x, V)], [r_x(V), ~nstar(x, V)], [~new_nstar_new(A, B), ~new_nstar_new(B, A), =(A, B)], [new_nstar_new(A, A)], [~new_nstar_new(A, B), ~new_nstar_new(B, C), new_nstar_new(A, C)], [~new_nstar_new(A, B), ~new_nstar_new(A, C), new_nstar_new(B, C), new_nstar_new(C, B)], [~new_n_last_new(V), =(V, new_sk__n__last_new)], [~new_n_last_new(V), ~=(last, new_sk__n__last_new)], [=(last, new_sk__n__last_new), new_n_last_new(new_sk__n__last_new)], [new_nstar_new(last, new_sk__n__last_new)], [~new_nstar_new(last, V), =(last, V), new_nstar_new(new_sk__n__last_new, V)], [~new_nstar_new(last, V), =(last, V), ~=(new_sk__n__last_new, last)], [~new_n_temp_new(V), =(V, new_sk__n__temp_new)], [~new_n_temp_new(V), ~=(temp, new_sk__n__temp_new)], [=(temp, new_sk__n__temp_new), new_n_temp_new(new_sk__n__temp_new)], [new_nstar_new(temp, new_sk__n__temp_new)], [~new_nstar_new(temp, V), =(temp, V), new_nstar_new(new_sk__n__temp_new, V)], [~new_nstar_new(temp, V), =(temp, V), ~=(new_sk__n__temp_new, temp)], [~new_n_x_new(V), =(V, new_sk__n__x_new)], [~new_n_x_new(V), ~=(x, new_sk__n__x_new)], [=(x, new_sk__n__x_new), new_n_x_new(new_sk__n__x_new)], [new_nstar_new(x, new_sk__n__x_new)], [~new_nstar_new(x, V), =(x, V), new_nstar_new(new_sk__n__x_new, V)], [~new_nstar_new(x, V), =(x, V), ~=(new_sk__n__x_new, x)], [~new_r_last_new(V), new_nstar_new(last, V)], [new_r_last_new(V), ~new_nstar_new(last, V)], [~new_r_temp_new(V), new_nstar_new(temp, V)], [new_r_temp_new(V), ~new_nstar_new(temp, V)], [~new_r_x_new(V), new_nstar_new(x, V)], [new_r_x_new(V), ~new_nstar_new(x, V)]]')
constants_to_keep = ['last', 'temp', 'x']
unary_to_keep = ['new_r_x_new', 'new_r_temp_new', 'new_r_last_new', 'new_n_last_new', 'new_n_temp_new', 'new_n_x_new']
binary_to_keep = ['new_nstar_new']



find_consequences(theory, background_theory, constants_to_keep, unary_to_keep, binary_to_keep)

theory = to_clauses('[[aux_join__()], [~=(x, last)], [~r_last(x)], [~n_last(V0)], [~n_x(V0)], [~r_temp(x)], [r_temp(last)]]')
background_theory = to_clauses('[[~nstar(A, B), ~nstar(B, A), =(A, B)], [nstar(A, A)], [~nstar(A, B), ~nstar(B, C), nstar(A, C)], [~nstar(A, B), ~nstar(A, C), nstar(B, C), nstar(C, B)], [~n_last(V), =(V, sk__n__last)], [~n_last(V), ~=(last, sk__n__last)], [=(last, sk__n__last), n_last(sk__n__last)], [nstar(last, sk__n__last)], [~nstar(last, V), =(last, V), nstar(sk__n__last, V)], [~nstar(last, V), =(last, V), ~=(sk__n__last, last)], [~n_temp(V), =(V, sk__n__temp)], [~n_temp(V), ~=(temp, sk__n__temp)], [=(temp, sk__n__temp), n_temp(sk__n__temp)], [nstar(temp, sk__n__temp)], [~nstar(temp, V), =(temp, V), nstar(sk__n__temp, V)], [~nstar(temp, V), =(temp, V), ~=(sk__n__temp, temp)], [~n_x(V), =(V, sk__n__x)], [~n_x(V), ~=(x, sk__n__x)], [=(x, sk__n__x), n_x(sk__n__x)], [nstar(x, sk__n__x)], [~nstar(x, V), =(x, V), nstar(sk__n__x, V)], [~nstar(x, V), =(x, V), ~=(sk__n__x, x)], [~r_last(V), nstar(last, V)], [r_last(V), ~nstar(last, V)], [~r_temp(V), nstar(temp, V)], [r_temp(V), ~nstar(temp, V)], [~r_x(V), nstar(x, V)], [r_x(V), ~nstar(x, V)]]')
constants_to_keep = ['last', 'x']
unary_to_keep = ['n_last', 'n_x', 'r_temp', 'r_last']
binary_to_keep = []

find_consequences(theory, background_theory, constants_to_keep, unary_to_keep, binary_to_keep)


theory = to_clauses('[[~=(x, last)], [~r_last(x)], [~n_last(V0)], [~n_x(V0)], [~r_temp(x)], [r_temp(last)], [~new_nstar_new(A, B), nstar(A, B)], [~new_nstar_new(A, B), ~nstar(A, last), ~nstar(last, B), =(last, B)], [new_nstar_new(A, B), ~nstar(A, B), nstar(A, last)], [new_nstar_new(A, B), ~nstar(A, B), nstar(last, B)], [new_nstar_new(A, last), ~nstar(A, last)]]')
background_theory = to_clauses('[[~nstar(A, B), ~nstar(B, A), =(A, B)], [nstar(A, A)], [~nstar(A, B), ~nstar(B, C), nstar(A, C)], [~nstar(A, B), ~nstar(A, C), nstar(B, C), nstar(C, B)], [~n_last(V), =(V, sk__n__last)], [~n_last(V), ~=(last, sk__n__last)], [=(last, sk__n__last), n_last(sk__n__last)], [nstar(last, sk__n__last)], [~nstar(last, V), =(last, V), nstar(sk__n__last, V)], [~nstar(last, V), =(last, V), ~=(sk__n__last, last)], [~n_temp(V), =(V, sk__n__temp)], [~n_temp(V), ~=(temp, sk__n__temp)], [=(temp, sk__n__temp), n_temp(sk__n__temp)], [nstar(temp, sk__n__temp)], [~nstar(temp, V), =(temp, V), nstar(sk__n__temp, V)], [~nstar(temp, V), =(temp, V), ~=(sk__n__temp, temp)], [~n_x(V), =(V, sk__n__x)], [~n_x(V), ~=(x, sk__n__x)], [=(x, sk__n__x), n_x(sk__n__x)], [nstar(x, sk__n__x)], [~nstar(x, V), =(x, V), nstar(sk__n__x, V)], [~nstar(x, V), =(x, V), ~=(sk__n__x, x)], [~r_last(V), nstar(last, V)], [r_last(V), ~nstar(last, V)], [~r_temp(V), nstar(temp, V)], [r_temp(V), ~nstar(temp, V)], [~r_x(V), nstar(x, V)], [r_x(V), ~nstar(x, V)], [~new_nstar_new(A, B), ~new_nstar_new(B, A), =(A, B)], [new_nstar_new(A, A)], [~new_nstar_new(A, B), ~new_nstar_new(B, C), new_nstar_new(A, C)], [~new_nstar_new(A, B), ~new_nstar_new(A, C), new_nstar_new(B, C), new_nstar_new(C, B)], [~new_n_last_new(V), =(V, new_sk__n__last_new)], [~new_n_last_new(V), ~=(last, new_sk__n__last_new)], [=(last, new_sk__n__last_new), new_n_last_new(new_sk__n__last_new)], [new_nstar_new(last, new_sk__n__last_new)], [~new_nstar_new(last, V), =(last, V), new_nstar_new(new_sk__n__last_new, V)], [~new_nstar_new(last, V), =(last, V), ~=(new_sk__n__last_new, last)], [~new_n_x_new(V), =(V, new_sk__n__x_new)], [~new_n_x_new(V), ~=(x, new_sk__n__x_new)], [=(x, new_sk__n__x_new), new_n_x_new(new_sk__n__x_new)], [new_nstar_new(x, new_sk__n__x_new)], [~new_nstar_new(x, V), =(x, V), new_nstar_new(new_sk__n__x_new, V)], [~new_nstar_new(x, V), =(x, V), ~=(new_sk__n__x_new, x)], [~new_r_last_new(V), new_nstar_new(last, V)], [new_r_last_new(V), ~new_nstar_new(last, V)], [~new_r_x_new(V), new_nstar_new(x, V)], [new_r_x_new(V), ~new_nstar_new(x, V)]]')
constants_to_keep = ['last', 'temp', 'x']
unary_to_keep = ['new_r_x_new', 'new_n_last_new', 'new_n_x_new', 'new_r_last_new']
binary_to_keep = ['new_nstar_new']


find_consequences(theory, background_theory, constants_to_keep, unary_to_keep, binary_to_keep)
