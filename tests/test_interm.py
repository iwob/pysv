import unittest
from pysv.interm import *
from pysv.contract import *
from pysv import ast_utils, ssa_converter


class TestsInterm(unittest.TestCase):

    def test_var_base_id(self):
        self.assertEquals("vec", Var.base_id("vec'"))
        self.assertEquals("vec", Var.base_id("vec''"))
        self.assertEquals("vec", Var.base_id("|vec''|"))
        self.assertEquals("v", Var.base_id("|v'5|"))


    def test_rename_vars(self):
        ib = InstrBlock([])
        ib.append(InstrAssign(Var('x'), Op('+', [Var("|y''|"), ConstInt('5')])))

        ib.rename_var('x', 'z')
        self.assertEquals('z', ib[0].var.id)
        self.assertEquals("|y''|", ib[0].expr.args[0].id)

        rename_base_vars(ib, 'y', 'asd')
        self.assertEquals('z', ib[0].var.id)
        self.assertEquals("|asd''|", ib[0].expr.args[0].id)


    def test_collect_nodes(self):
        ib = InstrBlock([])
        v = Var('x')
        var_y = Var("|y''|")
        const5 = ConstInt('5')
        op = Op('+', [var_y, const5])
        a = InstrAssign(v, op)
        ib.append(a)
        self.assertEquals([ib, a, v, op, var_y, const5], ib.collect_nodes())


    def test_interm_assert(self):
        code = """
a = 10
assert a > 0
"""
        ib = ast_utils.py_to_interm_ib(code)
        ins = ib.src.instructions

        self.assertEquals(InstrAssign, type(ins[0]))
        self.assertEquals("a", ins[0].var.id)
        self.assertEquals(InstrAssert, type(ins[1]))
        self.assertEquals("a", ins[1].expr.args[0].id)
        self.assertEquals(0, ins[1].expr.args[1].value)


    def test_interm_aug_assign(self):
        code = """
a += 1
b -= a + 6
c *= b
d /= 2
e %= 3
"""
        ib = ast_utils.py_to_interm_ib(code)
        ins = ib.src.instructions
        def check(instr, correctVar, correctOp):
            self.assertEquals(InstrAssign, type(instr))
            self.assertEquals(correctVar, instr.var.id)
            self.assertEquals(correctOp, instr.expr.id)
            self.assertEquals(correctVar, instr.expr.args[0].id)
        check(ins[0], "a", "+")
        check(ins[1], "b", "-")
        check(ins[2], "c", "*")
        check(ins[3], "d", "/")
        check(ins[4], "e", "mod")


    def test_interm_if(self):
        code = """
x = 0
y = 0
if x<2:
    x = 1
    x = x + 1
else:
    x = 3
    y = 2
x = x + 5
"""
        ib = ast_utils.py_to_interm_ib(code)
        ins = ib.src.instructions

        self.assertEquals(InstrAssign, type(ins[0]))
        self.assertEquals("x", ins[0].var.id)
        self.assertEquals(InstrAssign, type(ins[1]))
        self.assertEquals("y", ins[1].var.id)

        self.assertEquals(InstrIf, type(ins[2]))
        self.assertEquals("x", ins[2].body[0].var.id)
        self.assertEquals("x", ins[2].body[1].var.id)
        self.assertEquals("x", ins[2].orelse[0].var.id)
        self.assertEquals("y", ins[2].orelse[1].var.id)

        self.assertEquals(InstrAssign, type(ins[3]))
        self.assertEquals("x", ins[3].var.id)





    def test_interm_while(self):
        code = """
i = 1
while i < 6:
    print(i)
    i += 1
i *= 2
"""
        ib = ast_utils.py_to_interm_ib(code)
        ins = ib.src.instructions

        self.assertEquals(InstrAssign, type(ins[0]))
        self.assertEquals("i", ins[0].var.id)

        self.assertEquals(InstrWhile, type(ins[1]))
        self.assertEquals(Op, type(ins[1].condition))
        self.assertEquals("<", ins[1].condition.id)
        self.assertEquals("i", ins[1].condition.args[0].id)
        self.assertEquals(InstrCall, type(ins[1].body[0]))
        self.assertEquals("print", ins[1].body[0].id)
        self.assertEquals("i", ins[1].body[0].args[0].id)
        self.assertEquals(InstrAssign, type(ins[1].body[1]))
        self.assertEquals("i", ins[1].body[1].var.id)
        self.assertEquals(InstrAssign, type(ins[2]))
        self.assertEquals("i", ins[2].var.id)
        self.assertEquals("i", ins[2].expr.args[0].id)
        self.assertEquals(2, ins[2].expr.args[1].value)