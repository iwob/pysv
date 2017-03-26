#!/usr/bin/env python
import os
import sys
sys.path.insert(1, os.path.abspath('..'))


#---------------------------------------------------------------------------------------------------
#                            SELECTION OF THE MOST SUITABLE PROGRAM
#---------------------------------------------------------------------------------------------------
# This example shows how SMT based synthesis can be used to iteratively find the most suitable
# program from those correct with respect to the specification. There are two modes in this example
# to choose from:
#
# 1) Interactive mode, in which synthesizer returns synthesized code and user is asked, whether she
# wants to try to find some other program meeting the specification.
#
# 2) Automatic mode, in which synthesizer generates all possible programs meeting the specification.
#
#
# NOTE: Programs generated in both modes are different ONLY with respect to the used grammar productions.
# Allowing for differentiation of constant values would lead in most cases to infinitely many solutions.
#
#---------------------------------------------------------------------------------------------------


from pysv import templates
from pysv import smt_synthesis
from pysv import contract
from pysv import utils


def get_synthesizer():
    code = """a = HOLE"""
    vars = contract.ProgramVars({'x': 'Int', 'y': 'Int'}, {'a': 'Int'})
    code_pre = 'x >= 1 and y >= 1'
    code_post = 'a == 6*x + y'

    sygus_grammar = """
    (
        ( Start Int
            ( ( Constant Int ) x y (+ Start Start) (* ( Constant Int ) Start) )
        )
    )
    """ #(- Start Start)
    grammar = templates.load_gramar_from_SYGUS_spec(sygus_grammar)
    hole = smt_synthesis.HoleDecl('HOLE', grammar, {'x': 'Int', 'y': 'Int'}, is_expression_hole=True, max_depth=3)
    env = utils.Options({'--solver': 'z3', '--logic': 'NIA',
                         '--produce_proofs': True, '--silent': True})
    return smt_synthesis.SynthesizerSMT(code, code_pre, code_post, vars, env, [hole])


def synthesize_next_program(synth):
    res = synth.next_program()

    print('--------------------------\n')
    print('SYNTHESIZED PYTHON CODE:')
    print(res.final_code)
    return res


def interactive_mode():
    search_loop = True
    synth = get_synthesizer()

    while search_loop:
        res = synthesize_next_program(synth)

        if res.decision != 'sat':
            print('New program cannot be generated.')
            break

        while True:
            sys.stdout.write('Search for the next program? (y/n) ')
            t = sys.stdin.readline()
            if t[0].lower() == 'y':
                break
            elif t[0].lower() == 'n':
                search_loop = False
                break


def just_print_all_programs():
    synth = get_synthesizer()
    # programs = synth.find_all_possible_programs()

    print('Candidate programs:')
    programs = []
    while True:
        res = synth.next_program()
        if res.decision != 'sat':
            print("End of loop. Solver decision: " + res.decision)
            break
        programs.append(res.final_code)
        print(res.final_code)
        print('---------------------------')
    return programs


# ------------------------------------------------------------------------
#                                 MAIN
# ------------------------------------------------------------------------

# Uncomment option which you want to test.

# interactive_mode()

just_print_all_programs()

