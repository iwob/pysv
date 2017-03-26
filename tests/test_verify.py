import unittest
from pysv import smt_verifier
from pysv import contract
from pysv import utils


class TestsVerify(unittest.TestCase):

    def test_verify_smt2_simple_program(self):
        prog = "(= res (ite (= x 5) -1 1))"
        pre = "true"
        post = "(> res 0)"
        program_vars = contract.ProgramVars({'x':'Int'},{'res':'Int'})
        env = utils.Options(["--lang", "smt2"])
        res = smt_verifier.verify(prog, pre, post, program_vars, env)

        self.assertEquals('sat', res.decision)
        self.assertEquals('5', res.model['x'])
        self.assertEquals({'x':'5'}, res.witness)

        post = "(>= res -1)"
        res = smt_verifier.verify(prog, pre, post, program_vars, env)
        self.assertEquals('unsat', res.decision)
        self.assertEquals({}, res.model)
        self.assertEquals({}, res.witness)


    def test_find_example(self):
        prog = "(= res (ite (= x 5) -1 1))"
        pre = "true"
        post = "(= res -1)"
        program_vars = contract.ProgramVars({'x':'Int'},{'res':'Int'})
        env = utils.Options(["--lang", "smt2"])
        res = smt_verifier.find_example(prog, pre, post, program_vars, env)

        self.assertEquals('sat', res.decision)
        self.assertEquals('5', res.model['x'])
        self.assertEquals({'x':'5'}, res.witness)

        post = "(= res 0)"
        res = smt_verifier.find_example(prog, pre, post, program_vars, env)
        self.assertEquals('unsat', res.decision)
        self.assertEquals({}, res.model)
        self.assertEquals({}, res.witness)


    def test_verify_smt2_maximize(self):
        prog = "true"
        pre = "true"
        post = "(and (< res 0) (<= res 0) (= res 0) (= res 0))"
        program_vars = contract.ProgramVars({'res': 'Int'}, {})
        env = utils.Options(["--lang", "smt2", "--ver_mode", "max", "--post_in_cnf", 1, "--ver_annotate_post", 1, "--logic", "LIA", "--produce_assignments", 1])
        res = smt_verifier.verify(prog, pre, post, program_vars, env)
        self.assertEquals('sat', res.decision)
        self.assertEquals('0', res.model['res'])
        self.assertEquals('false', res.assignments['post_0'])
        self.assertEquals('true', res.assignments['post_1'])
        self.assertEquals('true', res.assignments['post_2'])
        self.assertEquals('true', res.assignments['post_3'])


    def test_verify_smt2_minimize(self):
        prog = "true"
        pre = "true"
        post = "(and (< res 0) (<= res 0) (= res 0) (= res 0))"
        program_vars = contract.ProgramVars({'res': 'Int'}, {})
        env = utils.Options(["--lang", "smt2", "--ver_mode", "min", "--post_in_cnf", 1, "--ver_annotate_post", 1, "--logic", "LIA", "--produce_assignments", 1])
        res = smt_verifier.verify(prog, pre, post, program_vars, env)
        self.assertEquals('sat', res.decision)
        self.assertEquals(True, int(res.model['res']) > 0)
        self.assertEquals('false', res.assignments['post_0'])
        self.assertEquals('false', res.assignments['post_1'])
        self.assertEquals('false', res.assignments['post_2'])
        self.assertEquals('false', res.assignments['post_3'])