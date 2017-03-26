#!/usr/bin/env python
import os
import sys
sys.path.insert(1, os.path.abspath('..'))


#---------------------------------------------------------------------------------------------------
#                                      UNSAT CORE EXAMPLES
#---------------------------------------------------------------------------------------------------
# This is an example of the generation of unsat-core in the scenario of SMT synthesis for test cases.
#
# Test cases were constructed in such a way that for one of the tests correct program cannot be
# synthesized with the given grammar, while the rest of tests potentially can. The expected outcome is
# that solver will return unsat-core containing only assertions for this critical test. Unfortunately,
# the whole set of assertions is returned, because Z3 does not guarantee that the found unsat-core is
# minimal.
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
                (Variable Int)
                (+ Start Start)
        ))
    )
    """
    grammar = templates.load_gramar_from_SYGUS_spec(grammar_spec)
    h1 = smt_synthesis.HoleDecl('HOLE1', grammar, program_vars, True, max_depth=3)
    return [h1]




#------------------------------------------------------------------------
#                                 MAIN
#------------------------------------------------------------------------

code = """
res1 = HOLE1
"""
# Program should compute: res1 = x * y + 1
tests = [Test([2,2,5], [5]), # For the first 3 tests 'z' can be used to get result.
         Test([1,1,2], [2]),
         Test([0,0,1], [1]),
         Test([8,5,40], [0])] # Thus, this is the only test which is not feasible with this grammar.
test_cases = TestCases(tests, in_vars=['x','y','z'], out_vars=['res1'])




code_pre = 'True'
code_post = 'True' # test cases are the only source of specification.
vars_in_program = ProgramVars({'x': 'Int', 'y': 'Int', 'z': 'Int'}, {'res1': 'Int', 'res2': 'Int'})
vars_in_hole    = ProgramVars({'x': 'Int', 'y': 'Int', 'z': 'Int'}, None)
hole_decls = get_hole_declarations(vars_in_hole)




# Running a synthesizer.
env = utils.Options({'--solver': 'z3', '--logic': 'NIA', '--produce_unsat_core': '1'})
res = smt_synthesis.synthesize_tc(test_cases, code, code_pre, code_post, vars_in_program, env, hole_decls)
print('******** Z3 RESULT ********')
print(res.text)
print('--------------------------\n')
print('SYNTHESIZED PYTHON CODE:')
print(res.final_code)