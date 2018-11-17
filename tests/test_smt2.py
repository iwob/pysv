import unittest
from pysv.smt2 import *


class TestsCodeSMTLIB(unittest.TestCase):

    def test_simple_assert(self):
        text = "(assert (= x 5))"
        # tree = CodeSMTLIB.from_str(text)


    def test_TreeSmt2_from_wlist_only_terminal(self):
        string = "true"
        tree = NodeSmt2.from_wlist(utils.str_to_wlist(string))
        self.assertEquals('true', tree.name)
        self.assertEquals(True, tree.is_terminal)
        self.assertEquals(0, len(tree.args))
        self.assertEquals(0, tree.height())
        self.assertEquals(1, tree.size())


    def test_TreeSmt2_from_wlist_simple(self):
        string = "(and (= x y) (> y z) a)"
        tree = NodeSmt2.from_wlist(utils.str_to_wlist(string))
        self.assertEquals('and', tree.name)
        self.assertEquals(False, tree.is_terminal)
        self.assertEquals(3, len(tree.args))
        self.assertEquals(2, tree.height())
        self.assertEquals(8, tree.size())

        self.assertEquals('=', tree.args[0].name)
        self.assertEquals(False, tree.args[0].is_terminal)
        self.assertEquals(['x', 'y'], [x.name for x in tree.args[0].args])
        self.assertEquals(True, tree.args[0].args[0].is_terminal)
        self.assertEquals(True, tree.args[0].args[1].is_terminal)

        self.assertEquals('>', tree.args[1].name)
        self.assertEquals(False, tree.args[1].is_terminal)
        self.assertEquals(['y', 'z'], [x.name for x in tree.args[1].args])
        self.assertEquals(True, tree.args[1].args[0].is_terminal)
        self.assertEquals(True, tree.args[1].args[1].is_terminal)

        self.assertEquals('a', tree.args[2].name)
        self.assertEquals(True, tree.args[2].is_terminal)