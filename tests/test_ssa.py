import unittest
from pysv import ast_utils
from pysv import ssa_converter
from pysv.contract import *
from pysv.interm import *
from pysv import smt_synthesis
from pysv import loops


class TestsSSA(unittest.TestCase):

    def test_program_already_in_ssa_form(self):
        code = 'x = 0; y = 1; z = 2'
        post = 'z < 2'
        vars = ProgramVars({'x': 'Int', 'y': 'Int'}, {'z': 'Int'})

        # Running SSA conversion
        ib = ast_utils.py_to_interm_ib(code)
        post = ast_utils.py_to_interm_expr(post)
        ib2, post2 = ssa_converter.convert(ib, post, vars, ssa_mark_indexed=False)
        vars.add_marked_variables(ib2.src.collect_variables())

        # Assertions
        self.assertFalse(ib.src.equals(ib2.src))
        # -----------------------------------
        self.assertEquals("|x'|", ib2.src.instructions[0].var.id)
        self.assertEquals("|y'|", ib2.src.instructions[1].var.id)
        self.assertEquals("z", ib2.src.instructions[2].var.id)
        self.assertEquals(3, ib2.src.size())
        self.assertEquals("z", post2.args[0].id)

        ib2, post2 = ssa_converter.convert(ib2, post2, vars, ssa_mark_indexed=False)
        self.assertFalse(ib.src.equals(ib2))
        # -----------------------------------
        self.assertEquals("|x'|", ib2.src.instructions[0].var.id)
        self.assertEquals("|y'|", ib2.src.instructions[1].var.id)
        self.assertEquals("z", ib2.src.instructions[2].var.id)
        self.assertEquals(3, ib2.src.size())
        self.assertEquals("z", post2.args[0].id)


    def test_simple_program_no_ifs(self):
        code = 'x=0; y=1; z=2; x=3; y=4'
        post = 'x<2 and z<2'
        vars = ProgramVars({'x': 'Int', 'y': 'Int', 'z': 'Int'})

        # Running SSA conversion
        ib = ast_utils.py_to_interm_ib(code)
        post = ast_utils.py_to_interm_expr(post)
        ib2, post2 = ssa_converter.convert(ib, post, vars, ssa_mark_indexed=False)

        # Assertions
        self.assertEquals("|x'|", ib2.src.instructions[0].var.id)
        self.assertEquals("|y'|", ib2.src.instructions[1].var.id)
        self.assertEquals("|z'|", ib2.src.instructions[2].var.id)
        self.assertEquals("|x''|", ib2.src.instructions[3].var.id)
        self.assertEquals("|y''|", ib2.src.instructions[4].var.id)
        self.assertEquals(5, ib2.src.size())
        self.assertEquals("|x''|", post2.args[0].args[0].id)
        self.assertEquals("|z'|", post2.args[1].args[0].id)


    def test_interm_assert(self):
        code = """
a = 10
assert a > 0
"""
        ib = ast_utils.py_to_interm_ib(code)
        ib = ssa_converter.convert_ib(ib, ProgramVars({"a": "Int"}), ssa_mark_indexed=False)
        ins = ib.src.instructions

        self.assertEquals(InstrAssign, type(ins[0]))
        self.assertEquals("|a'|", ins[0].var.id)
        self.assertEquals(InstrAssert, type(ins[1]))
        self.assertEquals("|a'|", ins[1].expr.args[0].id)
        self.assertEquals(0, ins[1].expr.args[1].value)


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
        exp_code = """
x' = 0
y = 0
if x'<2:
    x'' = 1
    x''' = x'' + 1
    x''''' = x''' (m)
    y'' = y (m)
else:
    x'''' = 3
    y' = 2
    x''''' = x'''' (m)
    y'' = y' (m)
x'''''' = x''''' + 5
"""

        post = 'x<2 and y<2'
        vars = ProgramVars({'x': 'Int'}, {'y': 'Int'})

        # Running SSA conversion
        ib = ast_utils.py_to_interm_ib(code)
        post = ast_utils.py_to_interm_expr(post)
        ib2, post2 = ssa_converter.convert(ib, post, vars, ssa_mark_indexed=False)

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
        self.assertEquals("|x''''''|", post2.args[0].args[0].id)
        self.assertEquals("|y''|", post2.args[1].args[0].id)


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
        vars = ProgramVars({'acc': 'Int', 'limit': 'Int'}, {'newAcc': 'Int',  'trigger': 'Bool'})

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
        ib2, post2 = ssa_converter.convert(ib, post, vars, ssa_mark_indexed=False)


        holes = ib2.src.get_holes_definitions()
        self.assertEquals(1, len(holes))
        self.assertEquals({'acc': 'Int', 'limit': 'Int', "|newAcc'|": 'Int'}, holes[0].vars)


    def test_ssa_while(self):
        code = """
i = 1
while i < 6:
    print(i)
    i += 1
i *= 2
"""
        exp_code = """
i'1 = 1
while i'1 < 6:
    print(i'1)
    i'2 = i'1 + 1
i'3 = i'2 * 2
"""
        ib = ast_utils.py_to_interm_ib(code)
        ib = ssa_converter.convert_ib(ib, ProgramVars({"i":"Int"}), ssa_mark_indexed=False)
        ins = ib.src.instructions

        self.assertEquals(InstrAssign, type(ins[0]))
        self.assertEquals("|i'|", ins[0].var.id)

        self.assertEquals(InstrWhile, type(ins[1]))
        self.assertEquals(Op, type(ins[1].condition))
        self.assertEquals("<", ins[1].condition.id)
        self.assertEquals("|i'|", ins[1].condition.args[0].id)

        self.assertEquals(InstrCall, type(ins[1].body[0]))
        self.assertEquals("print", ins[1].body[0].id)
        self.assertEquals("|i'|", ins[1].body[0].args[0].id)

        self.assertEquals(InstrAssign, type(ins[1].body[1]))
        self.assertEquals("|i''|", ins[1].body[1].var.id)

        self.assertEquals(InstrAssign, type(ins[2]))
        self.assertEquals("|i'''|", ins[2].var.id)
        self.assertEquals("|i''|", ins[2].expr.args[0].id)
        self.assertEquals(2, ins[2].expr.args[1].value)



    def test_ssa_nested_ifs(self):
        code = """
i = 3
if i > 0:
    i -= 1
    if i > 0:
        i -= 1
        if i > 0:
            i -= 1
i *= 2
"""
        # Expected code:
        exp_code = """
i = 3
if i > 0:
    i'1 = i - 1
    if i'1 > 0:
        i'2 -= 1
        if i'2 > 0:
            i'3 -= 1
            i'4 = i'3 (m)
        else:
            i'4 = i'2 (m)
        i'5 = i'4
    else:
        i'5 = i'1
    i'6 = i'5
else:
    i'6 = i
i'7 = i'6 * 2
"""

        ib = ast_utils.py_to_interm_ib(code)
        ib = ssa_converter.convert_ib(ib, ProgramVars(), ssa_mark_indexed=True)
        ins = ib.src.instructions

        self.assertEquals(InstrAssign, type(ins[0]))
        self.assertEquals("i", ins[0].var.id)

        if1 = ins[1]
        self.assertEquals(InstrIf, type(if1))
        self.assertEquals("i", if1.condition.args[0].id)
        self.assertEquals(InstrAssign, type(if1.body[0]))
        self.assertEquals("|i'1|", if1.body[0].var.id)
        self.assertEquals("i", if1.body[0].expr.args[0].id)
        self.assertEquals("|i'6|", if1.body[2].var.id)  # meta
        self.assertEquals("|i'5|", if1.body[2].expr.id) # meta
        self.assertEquals("|i'6|", if1.orelse[0].var.id)  # meta
        self.assertEquals("i", if1.orelse[0].expr.id) # meta

        if2 = ins[1].body[1]
        self.assertEquals(InstrIf, type(if2))
        self.assertEquals("|i'1|", if2.condition.args[0].id)
        self.assertEquals(InstrAssign, type(if2.body[0]))
        self.assertEquals("|i'2|", if2.body[0].var.id)
        self.assertEquals("|i'5|", if2.body[2].var.id)  # meta
        self.assertEquals("|i'4|", if2.body[2].expr.id)  # meta
        self.assertEquals("|i'5|", if2.orelse[0].var.id)  # meta
        self.assertEquals("|i'1|", if2.orelse[0].expr.id)  # meta

        if3 = ins[1].body[1].body[1]
        self.assertEquals(InstrIf, type(if3))
        self.assertEquals("|i'2|", if3.condition.args[0].id)
        self.assertEquals(InstrAssign, type(if3.body[0]))
        self.assertEquals(False, if3.body[0].is_meta)
        self.assertEquals("|i'3|", if3.body[0].var.id)
        self.assertEquals(True, if3.body[1].is_meta)  # meta
        self.assertEquals("|i'4|", if3.body[1].var.id)  # meta
        self.assertEquals("|i'3|", if3.body[1].expr.id)  # meta
        self.assertEquals(True, if3.orelse[0].is_meta)  # meta
        self.assertEquals("|i'4|", if3.orelse[0].var.id)  # meta
        self.assertEquals("|i'2|", if3.orelse[0].expr.id)  # meta

        # Last assignment
        last = ins[2]
        self.assertEquals(InstrAssign, type(last))
        self.assertEquals("|i'7|", last.var.id)
        self.assertEquals("|i'6|", last.expr.args[0].id)



    def test_ssa_only_if(self):
        code = """
if i > 0:
    i -= 1
"""
        # Expected code:
        exp_code = """
if i > 0:
    i'1 = i - 1
    i'2 = i'1
else:
    i'2 = i
"""

        ib = ast_utils.py_to_interm_ib(code)
        ib = ssa_converter.convert_ib(ib, ProgramVars({"i":"Int"}), ssa_mark_indexed=True)
        ins = ib.src.instructions

        if1 = ins[0]
        self.assertEquals(InstrIf, type(if1))
        self.assertEquals("i", if1.condition.args[0].id)
        self.assertEquals(InstrAssign, type(if1.body[0]))
        self.assertEquals("|i'1|", if1.body[0].var.id)
        self.assertEquals("i", if1.body[0].expr.args[0].id)
        self.assertEquals("|i'2|", if1.body[1].var.id)  # meta
        self.assertEquals("|i'1|", if1.body[1].expr.id) # meta
        self.assertEquals("|i'2|", if1.orelse[0].var.id)  # meta
        self.assertEquals("i", if1.orelse[0].expr.id) # meta


    def test_ssa_only_if_else(self):
        code = """
if i > 0:
    i -= 1
else:
    assert i > 1
    i += 1
assert i > 1
"""
        # Expected code:
        exp_code = """
if i > 0:
    i'1 = i - 1
    i'3 = i'1
else:
    assert i > 1
    i'2 = i + 1
    i'3 = i'2
assert i'3 > 1
"""

        ib = ast_utils.py_to_interm_ib(code)
        ib = ssa_converter.convert_ib(ib, ProgramVars({"i": "Int"}), ssa_mark_indexed=True)
        ins = ib.src.instructions

        if1 = ins[0]
        self.assertEquals(InstrIf, type(if1))
        self.assertEquals("i", if1.condition[0].id)
        self.assertEquals(InstrAssign, type(if1.body[0]))
        self.assertEquals("|i'1|", if1.body[0].var.id)
        self.assertEquals("i", if1.body[0].expr[0].id)
        self.assertEquals("|i'3|", if1.body[1].var.id)  # meta
        self.assertEquals("|i'1|", if1.body[1].expr.id)  # meta
        self.assertEquals("i", if1.orelse[0].expr[0].id)
        self.assertEquals("|i'2|", if1.orelse[1].var.id)
        self.assertEquals("i", if1.orelse[1].expr[0].id)
        self.assertEquals("|i'3|", if1.orelse[2].var.id)  # meta
        self.assertEquals("|i'2|", if1.orelse[2].expr.id)  # meta

        self.assertEquals(InstrAssert, type(ins[1]))
        self.assertEquals("|i'3|", ins[1].expr[0].id)


    def test_ssa_loop_unroll(self):
        code = """
i = 1
while i < 6:
    print(i)
    i += 1
"""
        # Expected code:
        exp_code = """
i'1 = 1
if i'1 < 6:
    print(i'1)
    i'2 = i'1 + 1
    i'3 = i'2  (m)
else:
    assert not(i'1 < 6)
    i'3 = i'1  (m)
"""
        program = ast_utils.py_to_interm_ib(code)
        program = loops.unroll_loops_program(program, n=1)
        program = ssa_converter.convert_ib(program, ProgramVars({"i": "Int"}), ssa_mark_indexed=True)

        if1 = program.src[1]
        self.assertEquals(InstrIf, type(if1))
        self.assertTrue(if1.condition.equals(Op("<", args=[Var("|i'1|"), ConstInt(6)])))
        self.assertEquals("|i'3|", if1.body[2].var.id)  # meta
        self.assertEquals("|i'2|", if1.body[2].expr.id)  # meta
        self.assertEquals(InstrAssert, type(if1.orelse[0]))
        self.assertEquals("not", if1.orelse[0].expr.id)

        assertIns = if1.orelse[0]
        self.assertTrue("<", assertIns.expr[0].id)
        self.assertTrue("|i'1|", assertIns.expr[0][0].id)
        self.assertEquals("|i'3|", if1.orelse[1].var.id)  # meta
        self.assertEquals("|i'1|", if1.orelse[1].expr.id)  # meta
