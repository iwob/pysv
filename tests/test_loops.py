import unittest
from pysv.interm import *
from pysv import ast_utils
from pysv import loops


class TestsLoops(unittest.TestCase):

    def test_unroll_level1(self):
        code = """
i = 1
while i < 6:
    print(i)
    i += 1
i *= 2
"""
        program = ast_utils.py_to_interm_ib(code)
        ib = loops.unroll_loops(program.src, n=1)
        wi = ib.instructions[1]

        self.assertEquals(InstrIf, type(wi))
        self.assertTrue(wi.condition.equals(Op("<", args=[Var("i"), ConstInt(6)])))
        self.assertTrue(wi.orelse[0].expr.equals(Op("not", [Op("<", args=[Var("i"), ConstInt(6)])])))