#!/usr/bin/env python
import os
import sys
sys.path.insert(1, os.path.abspath('..'))


#---------------------------------------------------------------------------------------------------
#                                  SYNTHESIS OF POLYNOMIALS IN NIA
#---------------------------------------------------------------------------------------------------
# This is an example of the synthesis of polynomials in the NIA logic.
#---------------------------------------------------------------------------------------------------


from pysv import templates
from pysv import smt_synthesis
from pysv import contract
from pysv import utils



csv_keijzer12 = """x:Int; y:Int; res:Int
-3; -3; 115
-3; -2; 112
-3; -1; 109
-3; 0; 108
-3; 1; 107
-3; 2; 108
-3; 3; 109
-2; -3; 31
-2; -2; 28
-2; -1; 25
-2; 0; 24
-2; 1; 23
-2; 2; 24
-2; 3; 25
-1; -3; 9
-1; -2; 6
-1; -1; 3
-1; 0; 2
-1; 1; 1
-1; 2; 2
-1; 3; 3
0; -3; 7
0; -2; 4
0; -1; 1
0; 0; 0
0; 1; -1
0; 2; 0
0; 3; 1
1; -3; 7
1; -2; 4
1; -1; 1
1; 0; 0
1; 1; -1
1; 2; 0
1; 3; 1
2; -3; 15
2; -2; 12
2; -1; 9
2; 0; 8
2; 1; 7
2; 2; 8
2; 3; 9
3; -3; 61
3; -2; 58
3; -1; 55
3; 0; 54
3; 1; 53
3; 2; 54
3; 3; 55"""



def synthesize_keijzer12():
    smtgp_nia_grammar = """
    (
        ( Start Int
            ( x y (Constant Int) (+ Start Start) (- Start Start) (* Start Start) (div Start Start) (ite SBool Start Start) )
        )
        ( SBool Bool
            ( (> Start Start) (>= Start Start) (< Start Start) (<= Start Start) (= Start Start) (= SBool SBool) )
        )
    )
    """
    vars = contract.ProgramVars({'x': 'Int', 'y': 'Int'}, {'res': 'Int'})
    code = """(= res H1)"""
    code_pre = 'true'
    code_post = 'true'
    grammar = templates.load_gramar_from_SYGUS_spec(smtgp_nia_grammar)
    h1 = smt_synthesis.HoleDecl('H1', grammar, {'x': 'Int', 'y': 'Int'}, True, 6)
    hole_decls = [h1]
    tc = contract.TestCases.from_csv(csv_keijzer12)
    env = utils.Options(['--solver', 'z3', '--logic', 'NIA', "--lang", "smt2"])
    res = smt_synthesis.synthesize_tc(tc, code, code_pre, code_post, vars, env, hole_decls)
    return res



csv_square = """x:Int; res:Int
-2; 5
0; 1
2; 5"""

def synthesize_square():
    smtgp_nia_grammar = """
    (
        ( Start Int
            ( x (Constant Int) (+ Start Start) (- Start Start) (* Start Start) )
        )
    )
    """
    vars = contract.ProgramVars({'x': 'Int'}, {'res': 'Int'})
    code = """(= res (+ H1 1))"""
    code_pre = 'true'
    code_post = 'true'
    grammar = templates.load_gramar_from_SYGUS_spec(smtgp_nia_grammar)
    h1 = smt_synthesis.HoleDecl('H1', grammar, {'x': 'Int'}, True, 2)
    hole_decls = [h1]
    tc = contract.TestCases.from_csv(csv_square)
    env = utils.Options(['--solver', 'z3', '--logic', 'NIA', "--lang", "smt2", "--name_all_assertions", "0", "--synth_mode", "max"])
    res = smt_synthesis.synthesize_tc(tc, code, code_pre, code_post, vars, env, hole_decls)
    return res




# ------------------------------------------------------------------------
#                                 MAIN
# ------------------------------------------------------------------------


if __name__ == "__main__":
    # res = synthesize_keijzer12()
    res = synthesize_square()

    print('******** Z3 RESULT ********')
    print(res.text)
    print('--------------------------\n')
    print('SYNTHESIZED PYTHON CODE:')
    print(res.final_code)