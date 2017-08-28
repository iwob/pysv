import unittest
from pysv import smt_synthesis
from pysv import templates
from pysv.contract import *
from pysv import utils


class TestsSynthesis(unittest.TestCase):
    tests_int1 = TestCases([Test([0, 0], [0]),
                            Test([1, 1], [4]),
                            Test([1, 2], [6]),
                            Test([1, 0], [2]),
                            Test([2, 2], [8])], in_vars=['x', 'y'], out_vars=['res'])
    tests_and = TestCases([Test([0, 0], [0]),
                           Test([0, 1], [0]),
                           Test([1, 0], [0]),
                           Test([1, 1], [1])], in_vars=['x', 'y'], out_vars=['res'])


    def test_HoleDecl_from_str(self):
        h = smt_synthesis.HoleDecl.from_str("H0,((Start Bool (a b)))")
        self.assertEquals('H0', h.id)
        self.assertEquals({'a':'Bool', 'b':'Bool'}, h.vars)
        self.assertEquals('Bool', h.expr_type)
        self.assertEquals('Start', h.grammar['Start'].symb)
        self.assertEquals('Bool', h.grammar['Start'].sort)
        self.assertEquals(smt_synthesis.HoleDecl.DEFAULT_MAX_DEPTH, h.max_depth)
        h = smt_synthesis.HoleDecl.from_str("H0,10,((Start Bool (a b)))")
        self.assertEquals('H0', h.id)
        self.assertEquals({'a': 'Bool', 'b': 'Bool'}, h.vars)
        self.assertEquals('Bool', h.expr_type)
        self.assertEquals('Start', h.grammar['Start'].symb)
        self.assertEquals('Bool', h.grammar['Start'].sort)
        self.assertEquals(10, h.max_depth)


    def test_HoleDecl_many_from_str(self):
        h = smt_synthesis.HoleDecl.many_from_str("")
        self.assertEquals([], h)
        h = smt_synthesis.HoleDecl.many_from_str("H0,((Start Bool (a b)))")
        self.assertEquals(1, len(h))
        self.assertEquals('H0', h[0].id)
        self.assertEquals({'a':'Bool', 'b':'Bool'}, h[0].vars)
        self.assertEquals('Bool', h[0].expr_type)
        h = smt_synthesis.HoleDecl.many_from_str("H0,((Start Bool (a b))); H1,((Start Int (x y (+ Start Start))))")
        self.assertEquals(2, len(h))
        self.assertEquals('H0', h[0].id)
        self.assertEquals({'a': 'Bool', 'b': 'Bool'}, h[0].vars)
        self.assertEquals('Bool', h[0].expr_type)
        self.assertEquals('H1', h[1].id)
        self.assertEquals({'x': 'Int', 'y': 'Int'}, h[1].vars)
        self.assertEquals('Int', h[1].expr_type)


    def test_synthesis_simple(self):
        grammar = templates.load_gramar_from_SYGUS_spec("((Start Int (x y)))")
        h = smt_synthesis.HoleDecl('H0', grammar, None, True, 2)
        code = "(= res (* 2 (+ H0 y)))"
        env = utils.Options({'--solver': 'z3', '--logic': 'NIA', '--silent': 1, '--lang':'smt2', '--output_data':'holes_content',
                             '--solver_timeout':'2000'})
        vars = ProgramVars({'x': 'Int', 'y': 'Int'}, {'res': 'Int'})
        # Trivial case with the postcondition being always true.
        res = smt_synthesis.synthesize(code, 'true', 'true', vars, env, [h])
        self.assertEquals('sat', res.decision)
        # Slightly less trivial case.
        res = smt_synthesis.synthesize(code, 'true', '(= res (+ (* 2 x) (* 2 y)))', vars, env, [h])
        self.assertEquals('sat', res.decision)
        self.assertEquals('0', res.model['H0Start0_r0'])
        self.assertEquals('x', res.holes_content['H0'])
        self.assertEquals("{'H0': 'x'}", res.str_formatted())
        # Case for which UNSAT is the expected answer.
        res = smt_synthesis.synthesize(code, 'true', '(= res 0)', vars, env, [h])
        self.assertEquals('unsat', res.decision)


    def test_synthesis_recursive_grammar(self):
        code = """
if x > y:
    res = HOLE2
else:
    res = HOLE3
        """
        vars = ProgramVars({'x': 'Int', 'y': 'Int'}, {'res': 'Int'})
        code_pre = 'True'
        code_post = 'res >= x and res >= y and (res == x or res == y)'
        sygus_grammar_hole23 = """
        (
            ( Start Int
                ( ( Constant Int ) x y (+ Start Start) (- Start Start) (- y x) (+ x ( Constant Int )) (* Start Start)
                )
            )
        )
        """
        grammar23 = templates.load_gramar_from_SYGUS_spec(sygus_grammar_hole23)
        h2 = smt_synthesis.HoleDecl('HOLE2', grammar23, None, True, 2)
        h3 = smt_synthesis.HoleDecl('HOLE3', grammar23, None, True, 2)
        hole_decls = [h2, h3]
        assertions = []#['(assert (= HOLE3_r0 3))']
        env = utils.Options({'--solver':'z3', '--solver_interactive_mode':0, '--logic':'NIA', '--silent':0,
                             '--solver_timeout':'2000'})
        res = smt_synthesis.synthesize(code, code_pre, code_post, vars, env, hole_decls, assertions)
        print('[test_synthesis_recursive_grammar] RES:')
        print(res.text)
        print('[test_synthesis_recursive_grammar] SYNTHESIZED CODE:')
        print(res.final_code)
        self.assertTrue(res.decision == 'sat' or res.decision == "unknown")


    def test_synthesis_maximize_sum_tc(self):
        prog = "(= res constInt)"
        pre = "true"
        post = "true"
        program_vars = ProgramVars({'x':'Int', 'y':'Int'}, {'res':'Int', 'constInt':'Int'})
        env = utils.Options("--logic LIA --lang smt2 --synth_mode max --produce_assignments 1 --solver_interactive_mode 1")
        res = smt_synthesis.synthesize_tc(TestsSynthesis.tests_and, prog, pre, post, program_vars, env,
                                          free_vars=["constInt"], assertions=['(assert (or (= constInt 0) (= constInt 1)))'])
        self.assertEquals('sat', res.decision)
        self.assertEquals('0', res.model['constInt'])
        self.assertEquals('3', res.model['fitness'])
        self.assertEquals('true', res.assignments['pass_itest0'])
        self.assertEquals('true', res.assignments['pass_itest1'])
        self.assertEquals('true', res.assignments['pass_itest2'])
        self.assertEquals('false', res.assignments['pass_itest3'])


    def test_synthesis_minimize_sum_tc(self):
        prog = "(= res constInt)"
        pre = "true"
        post = "true"
        program_vars = ProgramVars({'x':'Int', 'y':'Int'}, {'res':'Int', 'constInt':'Int'})
        env = utils.Options("--logic LIA --lang smt2 --synth_mode min --produce_assignments 1 --solver_interactive_mode 0")
        res = smt_synthesis.synthesize_tc(TestsSynthesis.tests_and, prog, pre, post, program_vars, env,
                                          free_vars=["constInt"], assertions=['(assert (or (= constInt 0) (= constInt 1)))'])
        self.assertEquals('sat', res.decision)
        self.assertEquals('1', res.model['constInt'])
        self.assertEquals('1', res.model['fitness'])
        self.assertEquals('false', res.assignments['pass_itest0'])
        self.assertEquals('false', res.assignments['pass_itest1'])
        self.assertEquals('false', res.assignments['pass_itest2'])
        self.assertEquals('true', res.assignments['pass_itest3'])


    def test_synthesis_minimize_L0_tc(self):
        prog = "(= res constInt)"
        pre = "true"
        post = "true"
        program_vars = ProgramVars({'x':'Int', 'y':'Int'}, {'res':'Int', 'constInt':'Int'})
        env = utils.Options("--logic LIA --lang smt2 --synth_mode min --produce_assignments 1 --solver_interactive_mode 0 --tc_fitness_mode L1")
        res = smt_synthesis.synthesize_tc(TestsSynthesis.tests_and, prog, pre, post, program_vars, env,
                                          free_vars=["constInt"], assertions=['(assert (or (= constInt 0) (= constInt 1)))'])
        self.assertEquals('sat', res.decision)
        self.assertEquals('0', res.model['constInt']) # constInt set to 0 minimizes sum of errors while maximizing passed test cases.
        self.assertEquals('1', res.model['fitness'])


    def test_synthesis_optimize_passed_tests_for_complex_expr(self):
        """If this test fails with 'unknown' answer for z3, then you perhaps should update your z3 version. This test originally began as the unknown test, but z3 was improved and now this problem is solved quickly."""
        prog = "(= res (* (ite (<= (- x y) (+ x constInt0)) constInt1 y) (- (- constInt2 (ite constBool0 y constInt3)) constInt4)))"
        pre = "true"
        post = "true"
        input_vars = {'x':'Int', 'y':'Int'}
        local_vars = {'res':'Int', 'constInt0':'Int', 'constInt1':'Int', 'constInt2':'Int', 'constInt3':'Int',
                      'constInt4':'Int', 'constBool0':'Bool'}
        free_vars = ['constInt0', 'constInt1', 'constInt2', 'constInt3', 'constInt4', 'constBool0']
        program_vars = ProgramVars(input_vars, local_vars)
        tests = TestCases.from_str("([([0, 0], [0]), ([1, 1], [4]), ([1, 2], [6]), ([1, 0], [2]), ([2, 2], [8])], ['x', 'y'], ['res'])")
        env = utils.Options("--logic NIA --lang smt2 --synth_mode max --produce_assignments 1 --solver_timeout 2000")
        res = smt_synthesis.synthesize_tc(tests, prog, pre, post, program_vars, env,
                                          free_vars=free_vars)
        self.assertEquals('sat', res.decision)


    def test_synthesis_min_passed_tests(self):
        prog = "(= res constInt)"
        pre = "true"
        post = "true"
        program_vars = ProgramVars({'x':'Int', 'y':'Int'}, {'res':'Int', 'constInt':'Int'})
        # SAT case
        env = utils.Options("--logic LIA --lang smt2 --synth_mode min --produce_assignments 1 --synth_min_passed_tests 3")
        res = smt_synthesis.synthesize_tc(TestsSynthesis.tests_and, prog, pre, post, program_vars, env,
                                          free_vars=["constInt"], assertions=['(assert (or (= constInt 0) (= constInt 2)))'])
        self.assertEquals('sat', res.decision)
        self.assertEquals('0', res.model['constInt'])
        self.assertEquals('3', res.model['fitness'])

        # UNSAT case
        env = utils.Options("--logic LIA --lang smt2 --synth_mode min --produce_assignments 1 --synth_min_passed_tests 4")
        res = smt_synthesis.synthesize_tc(TestsSynthesis.tests_and, prog, pre, post, program_vars, env,
                                          free_vars=["constInt"],
                                          assertions=['(assert (or (= constInt 0) (= constInt 2)))'])
        self.assertEquals('unsat', res.decision)


    def test_synthesis_instruction_hole(self):
        code = "H0"
        grammar = templates.load_gramar_from_SYGUS_spec("((Start Int (x y)))")
        h = smt_synthesis.HoleDecl('H0', grammar, None, True, 2)
        env = utils.Options({'--logic': 'NIA', '--silent': 1, '--lang': 'python',
                             '--output_data': 'holes_content'})
        vars = ProgramVars({'x': 'Int', 'y': 'Int'}, {'res': 'Int'})
        with self.assertRaises(Exception) as context:
            smt_synthesis.synthesize(code, 'True', 'True', vars, env, [h])
        self.assertEquals("Instruction holes are currently not supported!", str(context.exception))