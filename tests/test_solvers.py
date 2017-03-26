import unittest
from pysv import solvers
from pysv import utils


class TestsSolvers(unittest.TestCase):

    def test_solver_result_1(self):
        raw_result = """sat
        (model
          (define-fun |trigger''| () Bool
            false)
          (define-fun newAcc () Int
            1)
          (define-fun |newAcc''| (sth) Int
            2)
          (define-fun trigger (sth () sth) Bool
            true)
        )
        (QS PS QPR)
        """
        env = utils.Options(['--solver_interactive_mode', 0, '--produce_unsat_core', 1])
        res = solvers.SolverResult(raw_result, env)
        self.assertEquals('sat', res.decision)
        self.assertEquals('false', res["|trigger''|"])
        self.assertEquals('1', res['newAcc'])
        self.assertEquals('2', res["|newAcc''|"])
        self.assertEquals('true', res['trigger'])
        self.assertEquals({"|trigger''|": 'false', "newAcc": '1', "|newAcc''|": '2', "trigger": 'true'}, res.model)
        self.assertEquals([], res.unsat_core)


    def test_solver_result_2(self):
        raw_result = """unsat
        (error
        "line 34 column 10: model is not available")
        (VER_FORMULA)
        """
        env = utils.Options(['--solver_interactive_mode', 0, '--produce_unsat_core', 1])
        res = solvers.SolverResult(raw_result, env)
        self.assertEquals('unsat', res.decision)
        self.assertEquals({}, res.model)
        self.assertEquals(['VER_FORMULA'], res.unsat_core)


    def test_solver_result_3(self):
        raw_result = """unsat
        (error "line 34 column 10: model is not available")
        """ # this is testing what happens, if solver ends work on the first error.
        env = utils.Options(['--solver_interactive_mode', 0, '--produce_unsat_core', 1])
        res = solvers.SolverResult(raw_result, env)
        self.assertEquals('unsat', res.decision)
        self.assertEquals({}, res.model)
        self.assertEquals([], res.unsat_core)


    def test_solver_result_unsat_core(self):
        raw_result1 = """unsat
        (error "line 35 column 10: model is not available")
        (error "line 36 column 15: model is not available")
        (A2 A3 A4 A5)
        """
        raw_result2 = """unsat
        (A2 A3 A4 A5)
        """

        # Option for producing unsat core is not set.
        env = utils.Options(['--solver_interactive_mode', 0, '--produce_unsat_core', 0, '--produce_assignments', 1])
        res = solvers.SolverResult(raw_result1, env)
        self.assertEquals([], res.unsat_core)

        # Option for producing unsat core is not set.
        env = utils.Options(['--solver_interactive_mode', 0, '--produce_unsat_core', 1, '--produce_assignments', 1])
        res = solvers.SolverResult(raw_result1, env)
        self.assertEquals(['A2', 'A3', 'A4', 'A5'], res.unsat_core)

        # Option for producing unsat core is not set.
        env = utils.Options(['--solver_interactive_mode', 1, '--produce_unsat_core', 0, '--produce_assignments', 1])
        res = solvers.SolverResult(raw_result2, env)
        self.assertEquals([], res.unsat_core)

        # Option for producing unsat core is not set.
        env = utils.Options(['--solver_interactive_mode', 1, '--produce_unsat_core', 1, '--produce_assignments', 1])
        res = solvers.SolverResult(raw_result2, env)
        self.assertEquals(['A2', 'A3', 'A4', 'A5'], res.unsat_core)


    def test_solver_result_assignment(self):
        raw_result = """sat
        (model
          (define-fun |trigger''| () Bool
            false)
          (define-fun newAcc () Int
            1)
          (define-fun |newAcc''| (sth) Int
            2)
          (define-fun trigger (sth) Bool
            true)
        )
        ((A4 false) (A1 true) (A2 false) (A3 true))
        (error "line 35 column 15: unsat core is not available")
        """
        # Option for producing assignments is not set.
        env = utils.Options(['--solver_interactive_mode', 0])
        res = solvers.SolverResult(raw_result, env)
        self.assertEquals({}, res.assignments)

        # Option for producing assignments is set.
        env = utils.Options(['--solver_interactive_mode', 0, '--produce_assignments', 1])
        res = solvers.SolverResult(raw_result, env)
        self.assertEquals({'A4':'false', 'A1':'true', 'A2':'false', 'A3':'true'}, res.assignments)

        # Option for producing assignments is not set.
        env = utils.Options(['--solver_interactive_mode', 1])
        res = solvers.SolverResult(raw_result, env)
        self.assertEquals({}, res.assignments)

        # Option for producing assignments is set.
        env = utils.Options(['--solver_interactive_mode', 1, '--produce_assignments', 1])
        res = solvers.SolverResult(raw_result, env)
        self.assertEquals({'A4': 'false', 'A1': 'true', 'A2': 'false', 'A3': 'true'}, res.assignments)


    def test_result_str_formatted(self):
        text = """sat
        (model
          (define-fun newAcc () Int
            1)
        )"""
        env = utils.Options(['--output_data', 'decision', 'model', '--silent', 1])
        res = solvers.SolverResult(text, env)
        exp =\
"""sat
{'newAcc': '1'}
"""
        self.assertEquals(exp, res.str_formatted())

        env = utils.Options(['--output_data', 'decision', '--silent', 0])
        res = solvers.SolverResult(text, env)
        exp =\
"""----------------------------------------------
SOLVER RESULT
----------------------------------------------
sat
"""
        self.assertEquals(exp, res.str_formatted())
