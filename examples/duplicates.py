#!/usr/bin/env python
import os
import sys
sys.path.insert(1, os.path.abspath('..'))


#---------------------------------------------------------------------------------------------------
#                                      REMOVING DUPLICATES
#---------------------------------------------------------------------------------------------------
# This example presents one of the possible practical applications of SMT solvers.
#
# SCENARIO: We have a list of arithmetic expressions over some real variables. We want to have on
# the list only semantically unique expressions. For example, we may want to count how many there are
# unique expressions meeting a certain property, or we may want to decrease their number for efficiency
# reasons.
#
# SOLUTION: For every pair of expressions e1 and e2, we assert a constraint "e1 != e2". Then, we run
# the Z3 SMT solver. Solver will look for such a valuation of variables that will satisfy this constraint.
# If it succeeds, it will also generate an example for which e1 != e2. If it does not succeed, we can
# infer that expressions are semantically equal.
#
#---------------------------------------------------------------------------------------------------


from pysv import utils
from pysv import ast_utils
from pysv import solvers


def are_semantically_equal(f1, f2):
    env = utils.Options("--silent 1")
    s = solvers.SolverBinaries(env)
    constrs = []
    def decl_var(name):
        constrs.append('(declare-fun ' + name + '() Real)')
    def helper(code):
        expr = ast_utils.py_to_interm_expr(code)
        constrs.append('(assert ' + expr.to_smt2(env).get_src() + ')')

    constrs.append('(set-logic NRA)')
    decl_var('a')
    decl_var('b')
    decl_var('c')
    decl_var('d')
    helper(f1 + ' != ' + f2)
    # All constraints below are because of possible exception of dividing by 0. Expressions can be
    # parsed to detect which of these constraints are necessary, but we omitted this for simplicity.
    helper("a > 0")
    helper("b > 0")
    helper("c > 0")
    helper("d > 0")
    helper("a + b > 0")
    helper("a + c > 0")
    helper("a + d > 0")
    helper("b + c > 0")
    helper("b + d > 0")
    helper("c + d > 0")
    helper("b + c + d > 0")
    helper("a + c + d > 0")
    helper("a + b + d > 0")
    helper("a + b + c > 0")
    helper("a + b + c + d == 1")
    constrs.append('(check-sat)')

    res = s.apply('\n'.join(constrs)) # Executing solver for asserted constraints.
    if res.decision == solvers.SAT:
        print('Semantically different!')
        print('Differentiating values: ' + str(res.model))
        return False
    elif res.decision == solvers.UNSAT:
        # Model was not found, so solution are semantically equal.
        print('Equal! Removing ' + f2)
        return True
    elif res.decision == solvers.UNKNOWN:
        print('Solver returned *unknown*.')
        return False
    else:
        raise Exception('Not recognized response of the solver!')


def search_for_duplicates(tab):
    tab = tab[:]
    duplicates = []
    i = 0
    # Loops realize pairwise comparison between all expressions. Duplicates are removed from the list.
    while i < len(tab)-1:
        j = i + 1
        while j < len(tab):
            print(tab[i] + '\n' + tab[j])

            if are_semantically_equal(tab[i], tab[j]):
                duplicates.append(tab[j])
                del tab[j]
                j -= 1

            print('----------------------------------')
            j += 1
        i += 1

    print('\n\nList of semantically unique expressions:')
    for d in tab:
        print(str(d))

    print('\nList of duplicates:')
    for d in duplicates:
        print(str(d))
    return tab, duplicates





#------------------------------------------------------------------------
#                                 MAIN
#------------------------------------------------------------------------

data = [
    '(a+b)/a + a/b', # duplicate of the second formula
    '(b*(a+b) + a*a)/(a*b)', # duplicate of the first formula
    'a*a + 2*b' # semantically unique formula
]

search_for_duplicates(data)
