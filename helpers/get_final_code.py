#!/usr/bin/env python
import os
import sys
sys.path.insert(1, os.path.abspath('..'))

from pysv import utils
from pysv import contract
from pysv import templates
from pysv import smt_synthesis


# -------------------------------------------------------------------------
# When using a grammar tree, raw output of the SMT solver is unreadable
# in that the structure of the found program is obscured in the model.
# PySV offers utilities to produce python source code from the model
# returned by the solver. However, those utilities require access to the
# hole declaration and the original code. If you can provide those
# elements in this script, then you can produce final source code from the
# raw output of the solver.
#
# Example use case: producing readable source code of the result for manually
# modified synthesis scripts.
#
# Usage:
# ./get_final_code.py "$(cat data/get_final_code_input.txt)"
# -------------------------------------------------------------------------


def get_original_code():
    """Returns original source code of the program. This code is also fixed for the prettifier.
    Customize this for your needs."""
    return """HOLE1"""


def get_hole_declarations(program_vars):
    """Returns hole declarations. Customize this for your needs."""
    grammar_spec = """
    (
        (Start Int (
                (Constant Int)
                (Variable Int)
                (+ Start Start)
        ))
    )
    """
    grammar = templates.load_gramar_from_SYGUS_spec(grammar_spec)
    h1 = smt_synthesis.HoleDecl('HOLE1', grammar, program_vars, True, max_depth=4)
    return [h1]




if __name__ == "__main__":
    if len(sys.argv) == 1 or "-h" in sys.argv or "--help" in sys.argv:
        print("Usage: ./get_final_code.py [raw output from SMT solver]")
        exit()

    result = sys.argv[1]

    # Original source code (fixed for this prettifier instance).
    original_code = get_original_code()

    # Hole declarations (fixed for this prettifier instance).
    holes_decls = get_hole_declarations(contract.ProgramVars(input_vars={"x":"Int", "y":"Int", "z":"Int"}))

    # Options (fixed for this prettifier instance).
    env = utils.Options(merge_with_vargs=False)


    res = smt_synthesis.SynthesisResult(result, original_code, holes_decls, env)
    print("FINAL CODE:")
    print(res.final_code)
