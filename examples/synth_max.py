#!/usr/bin/env python
import os
import sys
sys.path.insert(1, os.path.abspath('..'))


#---------------------------------------------------------------------------------------------------
#                                  SYNTHESIS OF A MAXIMUM FUNCTION
#---------------------------------------------------------------------------------------------------
# This is an example of the synthesis of missing expressions in the Python program. Synthesis is
# done with a use of SMT solver. Several holes are synthesized simultaneously in order to meet a
# specification.
#
# Program should realize a maximum operation on two inputs: x and y.
#
# NOTE: Holes used here are so called "expression holes", that is they are representing only
# expressions and not independent instructions. Support for synthesizing instructions may be
# implemented in the future.
#---------------------------------------------------------------------------------------------------


from pysv import templates
from pysv import smt_synthesis
from pysv import contract
from pysv import utils



def synthesize_max():
    code = """
if H1:
    res = H2
else:
    res = H3
    """
    code_pre = 'True'
    code_post = 'res >= x and res >= y and (res == x or res == y)'

    # Specification of the hole's template in the form of the grammar in SYGUS format.
    sygus_grammar_hole1 = """
    (
        ( Start Bool
            ( (Constant Bool) (> TermInt TermInt) (>= TermInt TermInt) (= TermInt TermInt) (<= TermInt TermInt) (< TermInt TermInt)
            )
        )
        ( TermInt Int
            ( (Constant Int) x y )
        )
    )
    """
    # This encoding is easy for the solver.
    sygus_grammar_hole23 = """
    (
        ( Start Int
            ( (Constant Int) x y (+ x y) (- x y) (- y x) (+ x ( Constant Int )) (+ y ( Constant Int )) )
        )
    )
    """
    # This encoding is hard for the solver. Is it because of sharing terms across different ites branches?
    sygus_grammar_hole23_ = """
    (
        ( Start Int
            (  (- TermInt TermInt) (+ TermInt TermInt) (* (Constant Int) VarInt) )
        )
        ( VarInt Int
            ( x y )
        )
        ( TermInt Int
            ( (Constant Int) x y )
        )
    )
    """
    grammar1 = templates.load_gramar_from_SYGUS_spec(sygus_grammar_hole1)
    grammar23 = templates.load_gramar_from_SYGUS_spec(sygus_grammar_hole23)
    pv = contract.ProgramVars({'x': 'Int', 'y': 'Int'}, {'res': 'Int'})
    h1 = smt_synthesis.HoleDecl('H1', grammar1, pv, True, max_depth=2)
    h2 = smt_synthesis.HoleDecl('H2', grammar23, pv, True, max_depth=2)
    h3 = smt_synthesis.HoleDecl('H3', grammar23, pv, True, max_depth=2)
    hole_decls = [h1, h2, h3]


    # The result is currently only a raw output from the solver, but one can verify from the model
    # that synthesized program is correct.
    env = utils.Options(['--solver', 'z3', '--logic', 'NIA'])
    res = smt_synthesis.synthesize(code, code_pre, code_post, pv, env, hole_decls)
    return res






# ------------------------------------------------------------------------
#                                 MAIN
# ------------------------------------------------------------------------


if __name__ == "__main__":
    res = synthesize_max()

    print('******** Z3 RESULT ********')
    print(res.text)
    print('--------------------------\n')
    print('SYNTHESIZED PYTHON CODE:')
    print(res.final_code)