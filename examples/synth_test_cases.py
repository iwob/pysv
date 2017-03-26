#!/usr/bin/env python
import os
import sys
sys.path.insert(1, os.path.abspath('..'))


#---------------------------------------------------------------------------------------------------
#                                  SMT SYNTHESIS FROM TEST CASES
#---------------------------------------------------------------------------------------------------
# This is an example of SMT synthesis for test cases instead of general correctness predicates.
# This allows to avoid the use of a forall quantifier. Normally, with the forall quantifier,
# synthesis formula is:
#
# (FORALL_(input and local vars)  PRE /\ PROGRAM => POST )
#
# where program is parametrized with several structure free variables. Forall quantifier is needed
# to assure that program is correct for all inputs. Implication is basically needed for safety reasons
# because many of those values (especially for local variables) may create erroneous program, and because
# of implication it does not end with unsat. There is also precondition to take care of.
#
#
# In the test cases scenario, we can expand forall quantifier to check correctness only for the
# specified (input, output) pairs instead of all possible inputs. Synthesize function used in this example
# uses encoding which removes forall quantifier completely and generates several constraints for each
# test case in which it compares the result of the program with the expected output.
#
#---------------------------------------------------------------------------------------------------


from pysv.contract import *
from pysv import smt_synthesis
from pysv import templates


def get_hole_declarations(program_vars):
    """Helper function for creating hole declaration with a grammar blow."""
    grammar_spec = """
    (
        (Start Int (
                (Constant Int)
                (Variable Int)
                (+ Start Start)
                (* Start Start)
        ))
    )
    """
    grammar = templates.load_gramar_from_SYGUS_spec(grammar_spec)
    h1 = smt_synthesis.HoleDecl('HOLE1', grammar, program_vars, True, max_depth=4)
    h2 = smt_synthesis.HoleDecl('HOLE2', grammar, program_vars, True, max_depth=4)
    return [h1, h2]




#------------------------------------------------------------------------
#                                 MAIN
#------------------------------------------------------------------------

code = """
res1 = HOLE1
res2 = HOLE2
"""

# Program should compute: res1 = x * y + z, res2 = x + y
tests = [Test([1,2,3], [5, 3]),
         Test([1,1,1], [2, 2]),
         Test([0,0,1], [1, 0]),
         Test([5,1,2], [7, 6])]
# Program should compute: res1 = x * y + z, res2 = x + y + 2
tests2 = [Test([1,2,3], [5, 5]),
          Test([1,1,1], [2, 4]),
          Test([0,0,1], [1, 2]),
          Test([5,1,2], [7, 8])]
# Choose your tests.
test_cases = TestCases(tests, in_vars=['x','y','z'], out_vars=['res1', 'res2'])




code_pre = 'True'
code_post = 'True' # test cases are the only source of knowledge to the system.
vars_in_program = ProgramVars({'x': 'Int', 'y': 'Int', 'z': 'Int'}, {'res1': 'Int', 'res2': 'Int'})
vars_in_hole    = ProgramVars({'x': 'Int', 'y': 'Int', 'z': 'Int'}, None)
hole_decls = get_hole_declarations(vars_in_hole)




# Running a synthesizer.
env = utils.Options({'--solver': 'z3', '--logic': 'NIA'})
res = smt_synthesis.synthesize_tc(test_cases, code, code_pre, code_post, vars_in_program, env,
                                  hole_decls)
print('******** Z3 RESULT ********')
print(res.text)
print('--------------------------\n')
print('SYNTHESIZED PYTHON CODE:')
print(res.final_code)