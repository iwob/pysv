import unittest
from pysv import ast_utils
from pysv import ssa_converter
from pysv import contract
from pysv import smt_synthesis


class TestsSSA(unittest.TestCase):

	def test_program_already_in_ssa_form(self):
		code = 'x = 0; y = 1; z = 2'
		post = 'z < 2'
		vars = contract.ProgramVars({'x': 'Int', 'y': 'Int'}, {'z': 'Int'})

		# Running SSA conversion
		ib = ast_utils.py_to_interm_ib(code)
		post = ast_utils.py_to_interm_expr(post)
		ib2, post2 = ssa_converter.convert(ib, post, vars)
		vars.add_marked_variables(ib2.src.collect_variables())

		# Assertions
		self.assertFalse(ib.src.equals(ib2.src))
		# -----------------------------------
		self.assertEquals("|x'|", ib2.src.instructions[0].var.id)
		self.assertEquals("|y'|", ib2.src.instructions[1].var.id)
		self.assertEquals("z", ib2.src.instructions[2].var.id)
		self.assertEquals(3, ib2.src.size())
		self.assertEquals("z", post2.src.expr.args[0].id)

		ib2, post2 = ssa_converter.convert(ib2, post2, vars)
		self.assertFalse(ib.src.equals(ib2))
		# -----------------------------------
		self.assertEquals("|x'|", ib2.src.instructions[0].var.id)
		self.assertEquals("|y'|", ib2.src.instructions[1].var.id)
		self.assertEquals("z", ib2.src.instructions[2].var.id)
		self.assertEquals(3, ib2.src.size())
		self.assertEquals("z", post2.src.expr.args[0].id)


	def test_simple_program_no_ifs(self):
		code = 'x=0; y=1; z=2; x=3; y=4'
		post = 'x<2 and z<2'
		vars = contract.ProgramVars({'x': 'Int', 'y': 'Int', 'z': 'Int'})

		# Running SSA conversion
		ib = ast_utils.py_to_interm_ib(code)
		post = ast_utils.py_to_interm_expr(post)
		ib2, post2 = ssa_converter.convert(ib, post, vars)

		# Assertions
		self.assertEquals("|x'|", ib2.src.instructions[0].var.id)
		self.assertEquals("|y'|", ib2.src.instructions[1].var.id)
		self.assertEquals("|z'|", ib2.src.instructions[2].var.id)
		self.assertEquals("|x''|", ib2.src.instructions[3].var.id)
		self.assertEquals("|y''|", ib2.src.instructions[4].var.id)
		self.assertEquals(5, ib2.src.size())
		self.assertEquals("|x''|", post2.src.expr.args[0].args[0].id)
		self.assertEquals("|z'|", post2.src.expr.args[1].args[0].id)


	def test_simple_program_one_if(self):
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

		post = 'x<2 and y<2'
		vars = contract.ProgramVars({'x': 'Int'}, {'y': 'Int'})

		# Running SSA conversion
		ib = ast_utils.py_to_interm_ib(code)
		post = ast_utils.py_to_interm_expr(post)
		ib2, post2 = ssa_converter.convert(ib, post, vars)

		# Assertions
		self.assertEquals("|x'|", ib2.src.instructions[0].var.id)
		self.assertEquals("y", ib2.src.instructions[1].var.id)

		if_instr = ib2.src.instructions[2]
		self.assertEquals("<(|x'|, 2)", str(if_instr.condition))

		# BODY branch
		self.assertEquals("|x''| = 1", str(if_instr.body[0]))
		self.assertEquals("|x''|", if_instr.body[0].var.id)
		self.assertEquals(False, if_instr.body[0].is_meta)
		self.assertEquals("|x'''| = +(|x''|, 1)", str(if_instr.body[1]))
		self.assertEquals("|x'''|", if_instr.body[1].var.id)
		self.assertEquals(False, if_instr.body[1].is_meta)
		# meta
		self.assertEquals("|x'''''| = |x'''|  (meta)", str(if_instr.body[2]))
		self.assertEquals("|x'''''|", if_instr.body[2].var.id)
		self.assertEquals("|x'''|", if_instr.body[2].expr.id)
		self.assertEquals(True, if_instr.body[2].is_meta)
		self.assertEquals("|y''| = y  (meta)", str(if_instr.body[3]))
		self.assertEquals("|y''|", if_instr.body[3].var.id)
		self.assertEquals("y", if_instr.body[3].expr.id)
		self.assertEquals(True, if_instr.body[3].is_meta)

		# ORELSE branch
		self.assertEquals("|x''''| = 3", str(if_instr.orelse[0]))
		self.assertEquals("|x''''|", if_instr.orelse[0].var.id)
		self.assertEquals(False, if_instr.orelse[0].is_meta)
		self.assertEquals("|y'| = 2", str(if_instr.orelse[1]))
		self.assertEquals("|y'|", if_instr.orelse[1].var.id)
		self.assertEquals(False, if_instr.orelse[1].is_meta)
		# meta
		self.assertEquals("|x'''''| = |x''''|  (meta)", str(if_instr.orelse[2]))
		self.assertEquals("|x'''''|", if_instr.orelse[2].var.id)
		self.assertEquals("|x''''|", if_instr.orelse[2].expr.id)
		self.assertEquals(True, if_instr.orelse[2].is_meta)
		self.assertEquals("|y''| = |y'|  (meta)", str(if_instr.orelse[3]))
		self.assertEquals("|y''|", if_instr.orelse[3].var.id)
		self.assertEquals("|y'|", if_instr.orelse[3].expr.id)
		self.assertEquals(True, if_instr.orelse[3].is_meta)


		# After if
		self.assertEquals("|x''''''|", ib2.src.instructions[3].var.id)
		self.assertEquals("|x'''''|", ib2.src.instructions[3].expr.args[0].id)
		# Postcondition
		self.assertEquals("|x''''''|", post2.src.expr.args[0].args[0].id)
		self.assertEquals("|y''|", post2.src.expr.args[1].args[0].id)


	def test_ssa_form_holes(self):
		code = """
trigger = False
newAcc = acc + 2
newAcc = newAcc - 1
if newAcc < limit:
	trigger = False
else:
	newAcc = HOLE # should be 0
	newAcc = newAcc - 1
	trigger = True
		"""

		post = 'True'
		vars = contract.ProgramVars({'acc': 'Int', 'limit': 'Int'}, {'newAcc': 'Int',  'trigger': 'Bool'})

		grammar_spec = """
		(
			( Start Int
				( ( Constant Int ) acc limit newAcc)
			)
		)
		"""
		from pysv import templates
		grammar = templates.load_gramar_from_SYGUS_spec(grammar_spec)
		hole = smt_synthesis.HoleDecl('HOLE', grammar, None, True)


		ib = ast_utils.py_to_interm_ib(code, [hole])
		holes = ib.src.get_holes_definitions()
		self.assertEquals(1, len(holes))
		self.assertEquals({'acc': 'Int', 'limit': 'Int', 'newAcc': 'Int'}, holes[0].vars)

		post = ast_utils.py_to_interm_expr(post)
		ib2, post2 = ssa_converter.convert(ib, post, vars)


		holes = ib2.src.get_holes_definitions()
		self.assertEquals(1, len(holes))
		self.assertEquals({'acc': 'Int', 'limit': 'Int', "|newAcc'|": 'Int'}, holes[0].vars)

