#!/usr/bin/env python
import os
import sys
sys.path.insert(1, os.path.abspath('..'))


#---------------------------------------------------------------------------------------------------
#                          SMT SYNTHESIS OF ARTIFICIAL NEURAL NETWORKS
#---------------------------------------------------------------------------------------------------
# This is an example of using SMT synthesis to automatically generate weights of artificial neural
# network (ANN). Task of neural network stated is in the form of test cases and well-known XOR
# problem was chosen as a benchmark.
#
#---------------------------------------------------------------------------------------------------


from pysv.smt_synthesis import *
from pysv import templates


def get_hole_declarations(program_vars):
    """Helper function for creating hole declaration with a grammar blow."""
    grammar_spec = "((Start Int (   (Constant Real)   )))"
    grammar = templates.load_gramar_from_SYGUS_spec(grammar_spec)
    h1 = HoleDecl('HOLE1', grammar, program_vars, True, max_depth=4)
    h2 = HoleDecl('HOLE2', grammar, program_vars, True, max_depth=4)
    return {h1.id: h1, h2.id: h2}

def get_scenario_desc(code, tests, in_vars, weights_vars, local_vars, out_vars):
    prog_vars = ProgramVars()
    prog_vars.add_input_variables(in_vars, 'Real')
    prog_vars.add_local_variables(weights_vars, 'Real')
    prog_vars.add_local_variables(local_vars, 'Real')
    test_cases = TestCases(tests, in_vars=in_vars, out_vars=out_vars)
    return code, test_cases, prog_vars, weights_vars

def print_result(res):
    print(res.decision)
    if res.decision == 'sat':
        print('\nSynthesized ANN:')
        print(res.final_code)
    # if res.decision == 'unsat':
    #     print('unsat core:' + str(res.unsat_core))




#------------------------------------------------------------------------
#                             SCENARIOS
#------------------------------------------------------------------------

def scenario_linear_1layer():
    # Trying to synthesize ANN with only one linear neuron.
    # Should not succeed (unsat).
    # ----------------------------------------------------------
    code = "out_N1 = w0 + w1 * X1 + w2 * X2"
    tests_xor = [TestF([0.0, 0.0], ['out_N1 <= 0']),
                 TestF([0.0, 1.0], ['out_N1 >= 1']),
                 TestF([1.0, 0.0], ['out_N1 >= 1']),
                 TestF([1.0, 1.0], ['out_N1 <= 0'])]
    in_vars = ['X1', 'X2']
    out_vars = ['out_N1']
    local_vars = ['out_N1']
    weights_vars = ['w0', 'w1', 'w2']

    #----------------------------------------------------------
    return get_scenario_desc(code, tests_xor, in_vars, weights_vars, local_vars, out_vars)




def scenario_linear_2layers():
    # Trying to synthesize ANN with linear neurons and two layers (architecture 2-1).
    # Should not succeed (unsat).
    # ----------------------------------------------------------
    code =\
"""
# Layer 1 neurons
out_N1 = w1_0 + w1_1 * X1 + w1_2 * X2
out_N2 = w2_0 + w2_1 * X1 + w2_2 * X2

# Layer 2 neuron
out_N3 = w3_0 + w3_1 * out_N1 + w3_2 * out_N2
"""
    tests_xor = [TestF([0.0, 0.0], ['out_N3 <= 0']),
                 TestF([0.0, 1.0], ['out_N3 >= 1']),
                 TestF([1.0, 0.0], ['out_N3 >= 1']),
                 TestF([1.0, 1.0], ['out_N3 <= 0'])]
    in_vars = ['X1', 'X2']
    out_vars = ['out_N3']
    local_vars = ['out_N1', 'out_N2', 'out_N3']
    weights_vars = ['w1_0', 'w1_1', 'w1_2',
                    'w2_0', 'w2_1', 'w2_2',
                    'w3_0', 'w3_1', 'w3_2']
    #----------------------------------------------------------
    return get_scenario_desc(code, tests_xor, in_vars, weights_vars, local_vars, out_vars)



def scenario_binary_1layer():
    # Trying to synthesize ANN with only one neuron with binary activation function.
    # Should not succeed (unsat).
    # ----------------------------------------------------------
    code =\
"""
# Layer 1 neurons
sum_N1 = w1_0 + w1_1 * X1 + w1_2 * X2
if sum_N1 >= 0:
    out_N1 = 1
else:
    out_N1 = 0
"""
    tests_xor = [Test([0.0, 0.0], [0.0]),
                 Test([0.0, 1.0], [1.0]),
                 Test([1.0, 0.0], [1.0]),
                 Test([1.0, 1.0], [0.0])]
    in_vars = ['X1', 'X2']
    out_vars = ['out_N1']
    local_vars = ['out_N1', 'sum_N1']
    weights_vars = ['w1_0', 'w1_1', 'w1_2',
                    'w2_0', 'w2_1', 'w2_2',
                    'w3_0', 'w3_1', 'w3_2']
    #----------------------------------------------------------
    return get_scenario_desc(code, tests_xor, in_vars, weights_vars, local_vars, out_vars)



def scenario_binary_2layers():
    # Trying to synthesize ANN with neurons with binary activation function and two layers (architecture 2-1).
    # Should succeed (sat).
    # ----------------------------------------------------------
    code =\
"""
# Layer 1 neurons
sum_N1 = w1_0 + w1_1 * X1 + w1_2 * X2
if sum_N1 >= 0:
    out_N1 = 1
else:
    out_N1 = 0

sum_N2 = w2_0 + w2_1 * X1 + w2_2 * X2
if sum_N2 >= 0:
    out_N2 = 1
else:
    out_N2 = 0

# Layer 2 neuron
sum_N3 = w3_0 + w3_1 * out_N1 + w3_2 * out_N2
if sum_N3 >= 0:
    out_N3 = 1
else:
    out_N3 = 0
"""
    tests_xor = [Test([0.0, 0.0], [0.0]),
                 Test([0.0, 1.0], [1.0]),
                 Test([1.0, 0.0], [1.0]),
                 Test([1.0, 1.0], [0.0])]
    in_vars = ['X1', 'X2']
    out_vars = ['out_N3']
    local_vars = ['out_N1', 'out_N2', 'out_N3', 'sum_N1', 'sum_N2', 'sum_N3']
    weights_vars = ['w1_0', 'w1_1', 'w1_2',
                    'w2_0', 'w2_1', 'w2_2',
                    'w3_0', 'w3_1', 'w3_2']
    #----------------------------------------------------------
    return get_scenario_desc(code, tests_xor, in_vars, weights_vars, local_vars, out_vars)




def scenario_sigmoid_1layer():
    # Trying to synthesize ANN with only one neuron with binary sigmoid (logistic) activation function.
    # This cannot be realized by Z3, because it does not support exponential function.
    # ----------------------------------------------------------
    code =\
"""
# Layer 1 neurons
sum_N1 = w1_0 + w1_1 * X1 + w1_2 * X2
out_N1 = 1 / (1 + 2.72 ** (-sum_N1))
"""
    tests_xor = [TestF([0.0, 0.0], ['out_N1 <= 0.5']),
                 TestF([0.0, 1.0], ['out_N1 >= 0.5']),
                 TestF([1.0, 0.0], ['out_N1 >= 0.5']),
                 TestF([1.0, 1.0], ['out_N1 <= 0.5'])]
    in_vars = ['X1', 'X2']
    out_vars = ['out_N1']
    local_vars = ['out_N1', 'sum_N1']
    weights_vars = ['w1_0', 'w1_1', 'w1_2']
    #----------------------------------------------------------
    return get_scenario_desc(code, tests_xor, in_vars, weights_vars, local_vars, out_vars)



#------------------------------------------------------------------------
#                                 MAIN
#------------------------------------------------------------------------

env = utils.Options({'--solver':'z3', '--logic':'QF_NRA', '--synth_substitute_free':1,
                     '--produce_unsat_core':0, '--silent':1})





print('----------------------------------------------')
print("ANN: linear activation function, 1 layer")
print('----------------------------------------------')

code, test_cases, prog_vars, free_vars = scenario_linear_1layer()
res = synthesize_tc(test_cases, code, 'True', 'True', prog_vars, env, free_vars=free_vars)

print_result(res)
print('\n\n\n')





print('----------------------------------------------')
print("ANN: linear activation function, 2 layers")
print('----------------------------------------------')

code, test_cases, prog_vars, free_vars = scenario_linear_2layers()
res = synthesize_tc(test_cases, code, 'True', 'True', prog_vars, env, free_vars=free_vars)

print_result(res)
print('\n\n\n')





print('----------------------------------------------')
print("ANN: binary activation function, 1 layer")
print('----------------------------------------------')

code, test_cases, prog_vars, free_vars = scenario_binary_1layer()
res = synthesize_tc(test_cases, code, 'True', 'True', prog_vars, env, free_vars=free_vars)

print_result(res)
print('\n\n\n')





print('----------------------------------------------')
print("ANN: binary activation function, 2 layers")
print('----------------------------------------------')

code, test_cases, prog_vars, free_vars = scenario_binary_2layers()
res = synthesize_tc(test_cases, code, 'True', 'True', prog_vars, env, free_vars=free_vars)

print_result(res)
# print('\n\n\n')





# print('----------------------------------------------')
# print("ANN: sigmoid (logistic) activation function, 1 layer")
# print('----------------------------------------------')
#
# code, test_cases, prog_vars, free_vars = scenario_sigmoid_1layer()
# res = synthesize_test_cases(test_cases, code, 'True', 'True', prog_vars, env, free_vars=free_vars)
#
# print_result(res)