from pysv.interm import Var
from pysv import utils



def formula_test_cases_py(test_cases):
    """Transforms specified set of test cases into analogous Python expression.

    :param test_cases: List of tuples containing input and output expressions lists.
    :return: Logical formula encoding all test cases. INPUT => OUTPUT, i1 & i2 & .. & i_n; o1 & o2 & .. & o_n,
     i \in INPUT, o \in OUTPUT. Result uses only 'not', 'or', 'and' functions.
    """
    res = ""
    for i in range(0, len(test_cases)):
        inputs, outputs = test_cases[i]
        if i > 0:
            res += "  and  "
        res += formula_test_case_py(inputs, outputs)
    return res

def formula_test_case_py(inputs, outputs):
    """Creates a string of a Python expression encoding a single test case.

    :param inputs: List of conditions which hold on input. For example: ["x == 0", "y < 5"]
    :param outputs: List of conditions which hold on output. For example: ["z == x*x", ]
    :return: Verification formula string encoding test cases. INPUT => OUTPUT, i1 & i2 & .. & i_n; o1 & o2 & .. & o_n, i \in INPUT, o \in OUTPUT.
    """
    res = "(("
    res += formula_test_case_input(inputs)
    res += ") or ("
    res += formula_test_case_output(outputs)
    res += "))"
    return res

def formula_test_case_input(inputs):
    if len(inputs) == 0:
        raise Exception("Test case contains no input formula!")
    if len(inputs) == 1:
        return "not (" + inputs[0] + ")"
    else:
        res = ""
        for i in range(0, len(inputs)):
            if i > 0:
                res += " or "
            res += "(not (" + inputs[i] + "))"
        return res

def formula_test_case_output(outputs):
    if len(outputs) == 0:
        raise Exception("Test case contains no output formula!")
    if len(outputs) == 1:
        return outputs[0]
    else:
        return utils.conjunction(outputs)





class TestCases(object):
    """Contains all test cases and information about names of their variables.

    Attributes:
    -----------
    tests : list[Test]
        List containing test cases
    in_vars : list[string]
        Names of the input variables. Needed to generate a formula.
    out_vars : list[string]
        Names of the output variables. Needed to generate a formula.
    name_tests_vars : Bool
        Tells, if references to the names of the variables should be stored in the test cases.
    """
    def __init__(self, tests = None, in_vars = None, out_vars = None, do_name_tests_vars = True, lang = utils.LANG_PYTHON):
        if tests is None:
            tests = []
        self.tests = tests
        self.in_vars = in_vars
        self.out_vars = out_vars
        self.lang = lang
        self.do_name_tests_vars = do_name_tests_vars
        if self.do_name_tests_vars:
            for t in tests:
                t.in_vars = self.in_vars
                t.out_vars = self.out_vars

    def __getitem__(self, index):
        return self.tests[index]

    def __iter__(self):
        for t in self.tests:
            yield t

    def __len__(self):
        return len(self.tests)

    def all_vars(self):
        return self.in_vars + self.out_vars

    def add(self, test):
        """Adds a new test to the currently stored tests."""
        if self.do_name_tests_vars:
            test.in_vars = self.in_vars
            test.out_vars = self.out_vars
        self.tests.append(test)

    def code_postcond(self):
        """Returns a combined postcondition expression for all test cases (e.g. (=> (= x 0) (res = 1))). Format of this expression is depends on the chosen language."""
        if self.lang == utils.LANG_PYTHON:
            res = ['(not ({0}) or ({1}))'.format(t.code_inputs(self.lang), t.code_outputs(self.lang)) for t in self.tests]
            return ' and '.join(res)
        elif self.lang == utils.LANG_SMT2:
            res = ['(=> {0} {1})'.format(t.code_inputs(self.lang), t.code_outputs(self.lang)) for t in self.tests]
            if len(res) <= 1:
                return ''.join(res)
            else:
                return '(and ' + ' '.join(res) + ')'

    @classmethod
    def from_str(cls, text):
        """Creates test cases from a string encoding. Example of the string encoding: ([([0, 0], [0]), ([1, 1], [4]), ([1, 2], [6]), ([1, 0], [2]), ([2, 2], [8])], ['x', 'y'], ['res'])"""
        tc_desc = eval(text)
        tests = [Test(i, o) for i, o in tc_desc[0]]
        return TestCases(tests, in_vars=tc_desc[1], out_vars=tc_desc[2])

    @classmethod
    def from_csv(cls, text, is_header=True, sep=";"):
        """Returns test cases loaded from a content of a CSV file.

        :param text: (str) a content of a CSV file.
        :param is_header: (bool) informs, whether CSV file contains header with names of the variables.
        :param sep: (str) field separator of the CSV file.
        :return:
        """
        lines = text.split("\n")
        tests = []
        i, in_vars, out_vars = 0, None, None
        if is_header:
            header_cells = [x.split(":")[0].strip() for x in lines[0].split(sep)]
            i , in_vars, out_vars = 1, header_cells[:-1], [header_cells[-1]]

        for i in range(i, len(lines)):
            cells = [x.strip() for x in lines[i].split(sep)]
            t = Test(cells[:-1], [cells[-1]], in_vars, out_vars)
            tests.append(t)
        return tests





class Test(object):
    """Test represents a single test case with arbitrary many input and output values. For example Test([1,2,3], [1,3]) is a test case with three input values 1,2,3 and two expected return values 1,3. Values don't need to be strings, because str() method will be used on them during creation of the formulaic form.

    Attributes:
    -----------
    inputs : list[X]
        List containing inputs of this test case.
    outputs : list[X]
        List containing outputs of this test case, i.e. expected values.
    in_vars : list[string]
        Names of the input variables. Needed to generate a formula.
    out_vars : list[string]
        Names of the output variables. Needed to generate a formula.
    """
    def __init__(self, inputs, outputs, in_vars = None, out_vars = None):
        assert isinstance(inputs, list)
        assert isinstance(outputs, list)
        self.inputs = inputs
        self.outputs = outputs
        self.in_vars = in_vars
        self.out_vars = out_vars

    def get_by_name(self, in_var, default = None):
        """Returns input value based on variable name."""
        i = self.in_vars.index(in_var)
        return self.inputs[i] if i >= 0 else default

    def code_inputs(self, lang = utils.LANG_PYTHON):
        """Returns code representing equalities of input variables int the specified language. Example result: '(x == 1) and (y == 2)'."""
        f = Test.formulaic_form(self.inputs, self.in_vars, lang)
        return utils.conjunction(f, lang=lang)

    def code_outputs(self, lang = utils.LANG_PYTHON):
        """Returns Python code representing equalities of output variables. Example result: '(res1 == 1) and (res2 == 2)'."""
        f = Test.formulaic_form(self.outputs, self.out_vars, lang)
        return utils.conjunction(f, lang=lang)

    @staticmethod
    def formulaic_form(data, var_names, lang):
        if lang == utils.LANG_PYTHON:
            return Test._formulaic_form_helper(data, var_names, '{0} == {1}')
        else:
            return Test._formulaic_form_helper(data, var_names, '(= {0} {1})')

    @staticmethod
    def _formulaic_form_helper(data, var_names, sformat):
        return [sformat.format(n, v) for n,v in zip(var_names, data)]




class TestFF(Test):
    """TestFF represents a single test case in which both input and output are logical formulas."""
    def __init__(self, inputs, outputs, in_vars=None, out_vars=None):
        Test.__init__(self, inputs, outputs, in_vars, out_vars)

    def code_inputs(self, lang = utils.LANG_PYTHON):
        """Returns code representing equalities of input variables in the specified language. Example result: '(x == 1) and (y == 2)'."""
        return utils.conjunction(self.inputs, lang=lang)

    def code_outputs(self, lang = utils.LANG_PYTHON):
        """Returns code representing equalities of output variables in the specified language. Example result: '(res1 == 1) and (res2 == 2)'."""
        return utils.conjunction(self.outputs, lang=lang)




class TestF(TestFF):
    """TestF represents a single test case in which output is a logical formula and input is a sequence of values."""
    def __init__(self, inputs, outputs, in_vars=None, out_vars=None):
        Test.__init__(self, inputs, outputs, in_vars, out_vars)

    def code_inputs(self, lang = utils.LANG_PYTHON):
        """Returns code representing equalities of input variables in the specified language. Example result: '(x == 1) and (y == 2)'."""
        f = Test.formulaic_form(self.inputs, self.in_vars, lang)
        return utils.conjunction(f, lang=lang)







class ProgramVars(object):
    def __init__(self, input_vars = None, local_vars = None):
        """
        :param input_vars: Dictionary containing identifiers and types of program's input variables, e.g. {'n' : 'Int'} for fun(n) = n+1; a=0;.
        :param local_vars: Dictionary containing identifiers and types of program's local variables, e.g. {'a' : 'Int'} for fun(n) = n+1; a=0;.
        """
        if input_vars is None:
            input_vars = {}
        if local_vars is None:
            local_vars = {}
        self.input_vars = input_vars
        self.local_vars = local_vars

    def add_marked_variables(self, marked):
        """Finds on the provided list marked versions of variables already present in the dictionary and adds them with appropriate type (we assume that variables don't change type during runtime).

        :param marked: A list containing variable names (e.g. ["|x''|", "|y'|"]) to be added with appropriate types to the appropriate dictionary (input or local).
        """
        for v in marked:
            base_id = Var.base_id(v)
            if base_id in self.input_vars:
                self.input_vars[v] = self.input_vars[base_id]
            elif base_id in self.local_vars:
                self.local_vars[v] = self.local_vars[base_id]

    def add_input_variables(self, vars, type):
        """Adds all provided variables with the specified type to the input variables dictionary.

        :param vars: List of variable names (e.g. ["x", "|y'|"]).
        :param type: Name of the type of variables.
        """
        for v in vars:
            self.input_vars[v] = type

    def add_local_variables(self, vars, type):
        """Adds all provided variables with the specified type to the local variables dictionary.

        :param vars: List of variable names (e.g. ["x", "|y'|"]).
        :param type: Name of the type of variables.
        """
        for v in vars:
            self.local_vars[v] = type

    def get_names_input(self):
        """Returns list of input variables names"""
        return self.input_vars.keys()

    def get_names_local(self):
        """Returns list of local variables names"""
        return self.local_vars.keys()

    def get_names_all(self):
        """Returns list of all variables names"""
        return self.all().keys()

    def all(self):
        """Merges dictionaries for input and local variables into new dictionary and returns it.

        :return: A dictionary containing all program variables and their associated types.
        """
        res = dict(self.input_vars)
        res.update(self.local_vars)
        return res

    def rename_var(self, old_id, new_id):
        self.rename_var_for_dict(self.input_vars, old_id, new_id)
        self.rename_var_for_dict(self.local_vars, old_id, new_id)

    def rename_var_for_dict(self, vdict, old_id, new_id):
        if old_id in vdict:
            vdict[new_id] = vdict[old_id] # type
            del vdict[old_id]

    def get_base_input_vars(self):
        """Returns list of base (not marked) versions of input variables."""
        return ProgramVars.get_base_vars(self.input_vars)

    def get_latest_var_name(self, name):
        """Returns """
        keys = [k for k, v in self.all().items() if Var.base_id(k) == name]
        return max(keys, key=len)

    def __str__(self):
        return 'Input: ' + str(self.input_vars) + '\nLocal: ' + str(self.local_vars)

    @staticmethod
    def get_base_vars(vars_dict):
        """Returns list of base (not marked) versions of given variables."""
        res = {}
        for v in vars_dict:
            if Var.base_id(v) == v:
                res[v] = vars_dict[v]
        return res

    @staticmethod
    def get_vars_of_type(vars, type):
        """Returns dictionary containing variables with the given type.

        :param vars: Dictionary of original variables, possibly with different types.
        :param type: Type of the variables by which we will filter.
        :return: Dictionary of variable names (keys) and their types (values).
        """
        res = {}
        for v in vars:
            if type == vars[v]:
                res[v] = vars[v]
        return res

    @staticmethod
    def get_types(vars):
        """Returns set of types present in the variables dictionary.

        :param vars: Dictionary of original variables, possibly with different types.
        :return: A set containing names of all types present in the dictionary.
        """
        return set([vars[v] for v in vars])
