#!/usr/bin/env python
import os
import sys
sys.path.insert(1, os.path.abspath('..'))


#---------------------------------------------------------------------------------------------------
#                              VERIFICATION OF A SIMPLE MODULO COUNTER
#---------------------------------------------------------------------------------------------------
# This is an example of the verification of Python program using framework based on SMT solvers.
# Program realizes a simple modulo counter. Input variables:
# - 'acc': current value of the accumulator. Must be always lesser than 'limit'.
# - 'limit': value, at which 'acc' resets and 'trigger' is set to True.
#
# Program should increment 'acc' and check, if 'limit' was reached. If yes, then 'x' should be zeroed
# and 'trigger' should be set to True. If no, then nothing happens.
#
#
# NOTE: As can be seen, variables may be of different types.
#---------------------------------------------------------------------------------------------------


from pysv import contract
from pysv import utils
from pysv import smt_verifier



def verify_code(code, precondition, postcondition, variables):

    # Running verifier
    env = utils.Options(['--logic', 'LIA',
                         '--silent', 0,
                         '--produce_assignments', 1,
                         '--post_in_cnf', 1,
                         '--solver_interactive_mode', 1,
                         '--produce_unsat_core', 1,
                         '--ver_annotate_post', 1,
                         '--ver_flat_formula', 1])
    res = smt_verifier.verify(code, precondition, postcondition, variables, env)

    # Printing result
    print('\n')
    print('----------------------------------------------')
    print('                SOLVER RESULT                 ')
    print('----------------------------------------------')
    if res.decision == 'unsat':
        print('Counterexample not found! Program is correct.')
    elif res.decision == 'sat':
        print(res.witness)
        print('Counterexample found! Program is incorrect.')
    print('----------------------------------------------\n\n')
    return res






#------------------------------------------------------------------------
#                                 MAIN
#------------------------------------------------------------------------

# This is a precondition of our program.
precondition = 'acc < limit and acc >= 0 and limit > 0'

# Here is an example of generalized symbolic test cases, in which symbols and relations between
# them may be used. Everything is expressed in the form of logical formulas.
#
# I think that this is a very convenient compromise between full formal contracts and test cases as
# we know from GP.

t1 = (['acc == limit - 1'], ['trigger == True', 'newAcc == 0'])
t2 = (['acc < limit - 1'], ['trigger == False', 'newAcc == acc + 1'])
postcondition = contract.formula_test_cases_py([t1, t2])



# We must also specify types of variables used in the program, because dynamic typing in Python
# does not allow us to reliably obtain this information via reflection. In Scala this could be
# automatically generated from the source code.

variables = contract.ProgramVars({'acc': 'Int', 'limit': 'Int'}, {'newAcc': 'Int', 'trigger': 'Bool'})




# First, we will verify incorrect implementation of the modulo counter. If user invokes this program
# for example with 'acc' equal to 2 and 'limit' equal to 3, then counter modulo three will return 3,
# which is incorrect.
#
# As can be seen, verifier without any problems discovers an example of incorrect behavior.
code =\
"""
trigger = False
if acc < limit:
    newAcc = acc + 1
else:
    newAcc = 0
    trigger = True
"""
verify_code(code, precondition, postcondition, variables)



# After previous verification we analyzed the code and slightly changed condition in the IF statement.
# The code should now be correct, but just to be sure we run verifier yet again.
#
# Verification ends with unsat, which means that the program is correct with respect to the specification.
code =\
"""
trigger = True # unsat-core will not contain this instruction, because it has no effect on the result.
trigger = False
if acc < limit-1:
    newAcc = acc + 1
else:
    newAcc = 0
    trigger = True
"""
verify_code(code, precondition, postcondition, variables)