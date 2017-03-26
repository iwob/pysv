import unittest
from pysv.contract import *


class TestsContract(unittest.TestCase):

    def test_program_vars_input_and_local(self):
        vars = ProgramVars({'x': 'Int'}, {'y': 'Int'})
        vars.add_marked_variables(["|x|'", "|y|'", "|y|''"])

        self.assertEquals({'x': 'Int', "|x|'": 'Int'}, vars.input_vars)
        self.assertEquals({'y': 'Int', "|y|'": 'Int', "|y|''": 'Int'}, vars.local_vars)

        self.assertEquals({'x', "|x|'"}, set(vars.get_names_input()))
        self.assertEquals({'y', "|y|'", "|y|''"}, set(vars.get_names_local()))
        self.assertEquals({'x', "|x|'", 'y', "|y|'", "|y|''"}, set(vars.get_names_all()))

        self.assertEquals({'x': 'Int', "|x|'": 'Int', 'y': 'Int', "|y|'": 'Int', "|y|''": 'Int'}, vars.all())

        vars.add_input_variables(['a', 'b'], 'Bool')
        self.assertEquals({'x': 'Int', "|x|'": 'Int', 'a': 'Bool', 'b': 'Bool'}, vars.input_vars)

        vars.add_local_variables(['c'], 'Bool')
        self.assertEquals({'y': 'Int', "|y|'": 'Int', "|y|''": 'Int', 'c': 'Bool'}, vars.local_vars)
        vars.rename_var('c', 'c_T1')
        self.assertEquals({'y': 'Int', "|y|'": 'Int', "|y|''": 'Int', 'c_T1': 'Bool'}, vars.local_vars)


    def test_program_vars_markers(self):
        vars = ProgramVars({'x':'Int'}, {"y":"Int", "|y''|":"Int", "|asd'''''|":"Double", "|y'|":"Int"})
        self.assertEquals("|y''|", vars.get_latest_var_name('y'))


    def test_formula_test_case_border_cases(self):
        self.assertRaises(Exception, formula_test_case_py, [], [])
        self.assertRaises(Exception, formula_test_case_py, ['A'], [])
        self.assertRaises(Exception, formula_test_case_py, [], ['B'])


    def test_formula_test_case(self):
        formula = formula_test_case_py(['A'], ['C'])
        expected = "((not (A)) or (C))"
        self.assertEquals(expected, formula)

        formula = formula_test_case_py(['A', 'B'], ['C', 'D'])
        expected = "(((not (A)) or (not (B))) or ((C) and (D)))"
        self.assertEquals(expected, formula)


    def test_formula_test_cases_1(self):
        p1 = (['x>0'], ['res==5 and y<0'])
        formula = formula_test_cases_py([p1])
        expected = "((not (x>0)) or (res==5 and y<0))"
        self.assertEquals(expected, formula)


    def test_formula_test_cases_2(self):
        p1 = (['A', 'B'], ['x == 8', 'y == 0'])
        p2 = (['A', 'C'], ['x == 5', 'y == 1'])
        p3 = (['D', 'B'], ['x == 8', 'y == 2'])
        formula = formula_test_cases_py([p1, p2, p3])
        expected = "(((not (A)) or (not (B))) or ((x == 8) and (y == 0)))  and  (((not (A)) or (not (C))) or ((x == 5) and (y == 1)))  and  (((not (D)) or (not (B))) or ((x == 8) and (y == 2)))"
        self.assertEquals(expected, formula)


    def test_program_vars_static_methods(self):
        vars = {'x': 'Int', 'y': 'Int', 'z': 'Bool', 'a': 'Real'}
        self.assertEquals({'Int', 'Bool', 'Real'}, ProgramVars.get_types(vars))
        self.assertEquals({'x': 'Int', 'y': 'Int'}, ProgramVars.get_vars_of_type(vars, 'Int'))
        self.assertEquals({'z': 'Bool'}, ProgramVars.get_vars_of_type(vars, 'Bool'))
        self.assertEquals({'a': 'Real'}, ProgramVars.get_vars_of_type(vars, 'Real'))
        self.assertEquals({}, ProgramVars.get_vars_of_type(vars, 'String'))


    def test_Test_class(self):
        test = Test([1, 2], [3, -1], ['x', 'y'], ['add', 'sub'])
        self.assertEquals([1, 2], test.inputs)
        self.assertEquals([3, -1], test.outputs)
        self.assertEquals("(x == 1) and (y == 2)", test.code_inputs(lang=utils.LANG_PYTHON))
        self.assertEquals("(add == 3) and (sub == -1)", test.code_outputs(lang=utils.LANG_PYTHON))
        self.assertEquals("(and (= x 1) (= y 2))", test.code_inputs(lang=utils.LANG_SMT2))
        self.assertEquals("(and (= add 3) (= sub -1))", test.code_outputs(lang=utils.LANG_SMT2))


    def test_Test_formulaic_form_py(self):
        t = Test([1, 2], [3, -1], ['x', 'y'], ['add', 'sub'])
        self.assertEquals(['x == 1', 'y == 2'], Test.formulaic_form(t.inputs, t.in_vars, lang=utils.LANG_PYTHON))
        self.assertEquals(['add == 3', 'sub == -1'], Test.formulaic_form(t.outputs, t.out_vars, lang=utils.LANG_PYTHON))
        self.assertEquals(['(= x 1)', '(= y 2)'], Test.formulaic_form(t.inputs, t.in_vars, lang=utils.LANG_SMT2))
        self.assertEquals(['(= add 3)', '(= sub -1)'], Test.formulaic_form(t.outputs, t.out_vars, lang=utils.LANG_SMT2))


    def test_TestF_class(self):
        t = TestF([1, 2], ['add < sub', 'sub >= 0'], ['x', 'y'], ['add', 'sub'])
        self.assertEquals([1, 2], t.inputs)
        self.assertEquals(['add < sub', 'sub >= 0'], t.outputs)
        self.assertEquals("(x == 1) and (y == 2)", t.code_inputs(lang=utils.LANG_PYTHON))
        self.assertEquals("(add < sub) and (sub >= 0)", t.code_outputs(lang=utils.LANG_PYTHON))
        self.assertEquals("(and (= x 1) (= y 2))", t.code_inputs(lang=utils.LANG_SMT2))
        self.assertEquals("(and add < sub sub >= 0)", t.code_outputs(lang=utils.LANG_SMT2))


    def test_TestFF_class(self):
        t = TestFF(['x == 1', 'y == 2'], ['add < sub', 'sub >= 0'], ['x', 'y'], ['add', 'sub'])
        self.assertEquals(['x == 1', 'y == 2'], t.inputs)
        self.assertEquals(['add < sub', 'sub >= 0'], t.outputs)
        self.assertEquals("(x == 1) and (y == 2)", t.code_inputs(lang=utils.LANG_PYTHON))
        self.assertEquals("(add < sub) and (sub >= 0)", t.code_outputs(lang=utils.LANG_PYTHON))
        self.assertEquals("(and x == 1 y == 2)", t.code_inputs(lang=utils.LANG_SMT2))
        self.assertEquals("(and add < sub sub >= 0)", t.code_outputs(lang=utils.LANG_SMT2))


    def test_TestCases_class_py(self):
        tests = [Test([0, 2], [2]),
                 Test([1, 2], [3]),
                 Test([1, 3], [4])]
        tc = TestCases(tests, in_vars=['x', 'y'], out_vars=['res'], lang=utils.LANG_PYTHON)
        self.assertEquals([0, 2], tc.tests[0].inputs)
        self.assertEquals([1, 2], tc.tests[1].inputs)
        self.assertEquals([2], tc.tests[0].outputs)
        self.assertEquals([3], tc.tests[1].outputs)
        self.assertEquals('(not ((x == 0) and (y == 2)) or (res == 2)) and ' +\
                           '(not ((x == 1) and (y == 2)) or (res == 3)) and ' +\
                           '(not ((x == 1) and (y == 3)) or (res == 4))',
                          tc.code_postcond())

        tests = [TestFF(['A', 'B'], ['C'])]
        tc = TestCases(tests, in_vars=['x', 'y'], out_vars=['res'], lang=utils.LANG_PYTHON)
        self.assertEquals('(not ((A) and (B)) or (C))',
                          tc.code_postcond())

        tests = []
        tc = TestCases(tests, in_vars=['x', 'y'], out_vars=['res'], lang=utils.LANG_PYTHON)
        self.assertEquals('', tc.code_postcond())


    def test_TestCases_class_smt2(self):
        tests = [Test([0, 2], [2]),
                 Test([1, 2], [3]),
                 Test([1, 3], [4])]
        test_cases = TestCases(tests, in_vars=['x', 'y'], out_vars=['res'], lang=utils.LANG_SMT2)
        self.assertEquals('(and (=> (and (= x 0) (= y 2)) (= res 2)) ' +\
                               '(=> (and (= x 1) (= y 2)) (= res 3)) ' +\
                               '(=> (and (= x 1) (= y 3)) (= res 4))' +\
                          ')',
                          test_cases.code_postcond())

        tests = [TestFF(['A', 'B'], ['C'])]
        tc = TestCases(tests, in_vars=['x', 'y'], out_vars=['res'], lang=utils.LANG_SMT2)
        self.assertEquals('(=> (and A B) C)',
                          tc.code_postcond())

        tests = []
        tc = TestCases(tests, in_vars=['x', 'y'], out_vars=['res'], lang=utils.LANG_SMT2)
        self.assertEquals('', tc.code_postcond())