#!/usr/bin/env python
import os
import sys
sys.path.insert(1, os.path.abspath('..'))


#---------------------------------------------------------------------------------------------------
#                              VERIFICATION OF A MAXIMUM
#---------------------------------------------------------------------------------------------------
# This is an example of the verification of Python program using framework based on SMT solvers.
# Program being verified realizes a maximum function of two integer numbers.
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

precondition = 'True'
postcondition = "res >= x and res >= y and (res == x or res == y)"
variables = contract.ProgramVars({'x': 'Int', 'y': 'Int'}, {'res': 'Int'})




# First, we will verify incorrect implementation of the program. Notice that a counterexample is returned.
code =\
"""
if x < y:
	res = x
else:
	res = y
"""
verify_code(code, precondition, postcondition, variables)



# After previous verification we analyzed the code and slightly changed condition in the IF statement.
# The code should now be correct, but just to be sure we run verifier yet again.
code =\
"""
if x > y:
	res = x
else:
	res = y
"""
verify_code(code, precondition, postcondition, variables)