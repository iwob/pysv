import unittest
from pysv.interm import *


class TestsInterm(unittest.TestCase):

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
