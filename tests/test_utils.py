import unittest
from pysv import utils


class TestsUtils(unittest.TestCase):

    def test_utils(self):
        words = ['(', 'a', '(', 'b', 'c', ')', '(', 'd', ')', ')']
        self.assertEquals(9, utils.index_of_closing_parenthesis(words, 0))
        self.assertEquals(5, utils.index_of_closing_parenthesis(words, 2))
        self.assertEquals(8, utils.index_of_closing_parenthesis(words, 6))
        self.assertEquals(-1, utils.index_of_closing_parenthesis(words, 9))

        self.assertEquals(-1, utils.index_of_opening_parenthesis(words, 0))
        self.assertEquals(2, utils.index_of_opening_parenthesis(words, 5))
        self.assertEquals(6, utils.index_of_opening_parenthesis(words, 8))
        self.assertEquals(0, utils.index_of_opening_parenthesis(words, 9))

        self.assertEquals(0, utils.index_closest_left(words, 2, '('))
        self.assertEquals(1, utils.index_closest_left(words, 5, 'a'))
        self.assertEquals(-1, utils.index_closest_left(words, 5, 'z'))

        self.assertEquals(6, utils.index_closest_right(words, 3, '('))
        self.assertEquals(-1, utils.index_closest_right(words, 3, 'a'))
        self.assertEquals(7, utils.index_closest_right(words, 3, 'd'))

        self.assertEquals(['(', 'a', '(', 'b', 'c', ')', '(', 'd', ')', ')'], utils.parenthesis_enclosure(words, 1))
        self.assertEquals(['(', 'b', 'c', ')'], utils.parenthesis_enclosure(words, 3))
        self.assertEquals(['(', 'b', 'c', ')'], utils.parenthesis_enclosure(words, 4))
        self.assertEquals(['(', 'd', ')'], utils.parenthesis_enclosure(words, 7))
        self.assertEquals(['(', 'd', ')'], utils.parenthesis_enclosure(words, 8))
        self.assertEquals(['(', 'a', '(', 'b', 'c', ')', '(', 'd', ')', ')'], utils.parenthesis_enclosure(words, 9))


    def test_utils_alternative(self):
        self.assertEquals('', utils.alternative([], lang=utils.LANG_PYTHON))
        self.assertEquals('x', utils.alternative(['x'], lang=utils.LANG_PYTHON))
        self.assertEquals('(x) or (y+z) or (a)', utils.alternative(['x', 'y+z', 'a'], lang=utils.LANG_PYTHON))
        self.assertEquals('', utils.alternative([], lang=utils.LANG_SMT2))
        self.assertEquals('x', utils.alternative(['x'], lang=utils.LANG_SMT2))
        self.assertEquals('(or x y+z a)', utils.alternative(['x', 'y+z', 'a'], lang=utils.LANG_SMT2))

    def test_utils_conjunction(self):
        self.assertEquals('', utils.conjunction([], lang=utils.LANG_PYTHON))
        self.assertEquals('x', utils.conjunction(['x'], lang=utils.LANG_PYTHON))
        self.assertEquals('(x) and (y+z) and (a)', utils.conjunction(['x', 'y+z', 'a'], lang=utils.LANG_PYTHON))
        self.assertEquals('', utils.conjunction([], lang=utils.LANG_SMT2))
        self.assertEquals('x', utils.conjunction(['x'], lang=utils.LANG_SMT2))
        self.assertEquals('(and x y+z a)', utils.conjunction(['x', 'y+z', 'a'], lang=utils.LANG_SMT2))


    def test_str_to_dict_parenthesis(self):
        d = utils.str_to_dict_parenthesis("((A4 false) ( A1 true ) (A2 false)(A3 true))")
        self.assertEquals({'A4':'false', 'A1':'true', 'A2':'false', 'A3':'true'}, d)

        d = utils.str_to_dict_parenthesis("( (A4 false) )")
        self.assertEquals({'A4': 'false'}, d)

        d = utils.str_to_dict_parenthesis("()")
        self.assertEquals({}, d)


    def test_merge_elements_by(self):
        s = utils.merge_elements_by(['x == 5', 'y == 6'], ' and ', wrapped_in_par=True)
        self.assertEquals("(x == 5) and (y == 6)", s)
        s = utils.merge_elements_by(['x == 5'], ' and ', wrapped_in_par=True)
        self.assertEquals("x == 5", s)
        s = utils.merge_elements_by([], ' and ', wrapped_in_par=True)
        self.assertEquals("", s)

        s = utils.merge_elements_by(['x == 5', 'y == 6'], ' and ', wrapped_in_par=False)
        self.assertEquals("x == 5 and y == 6", s)
        s = utils.merge_elements_by(['x == 5'], ' and ', wrapped_in_par=False)
        self.assertEquals("x == 5", s)
        s = utils.merge_elements_by([], ' and ', wrapped_in_par=False)
        self.assertEquals("", s)


    def test_join_smt2(self):
        s = utils._join_smt2(['(= x 5)', '(= y 6)', '(= z 7)'], 'and')
        self.assertEquals("(and (= x 5) (= y 6) (= z 7))", s)
        s = utils._join_smt2(['(= x 5)', '(= y 6)'], 'and')
        self.assertEquals("(and (= x 5) (= y 6))", s)
        s = utils._join_smt2(['(= x 5)'], 'and',)
        self.assertEquals("(= x 5)", s)
        s = utils._join_smt2([], 'and')
        self.assertEquals("", s)


    def test_options(self):
        env = utils.Options(["--verify", "--lang", "smt2"])
        self.assertEquals(True, env.verify)
        self.assertEquals("smt2", env.lang)
        env = utils.Options("--verify --lang smt2")
        self.assertEquals(True, env.verify)
        self.assertEquals("smt2", env.lang)