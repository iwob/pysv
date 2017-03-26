import unittest
from pysv.symb_logic import *

class TestsSymbolicLogic(unittest.TestCase):

    def test_expand_implications(self):
        t = Implies(Var('x'), Var('y'))
        t2 = expand_implications(t)
        self.assertEquals(False, t is t2)
        self.assertEquals("or(not(x), y)", str(t2))
        self.assertEquals("(or (not x) y)", t2.str_smt2())

        t = Not(Implies(Var('x'), Var('y')))
        t2 = expand_implications(t)
        self.assertEquals(False, t is t2)
        self.assertEquals("not(or(not(x), y))", str(t2))
        self.assertEquals("(not (or (not x) y))", t2.str_smt2())

        t = Var('y')
        t2 = expand_implications(t)
        self.assertEquals(True, t is t2)
        self.assertEquals("y", str(t2))
        self.assertEquals("y", t2.str_smt2())


    def test_propagate_negations(self):
        t = Implies(Var('x'), Var('y'))
        t2 = propagate_negations(t)
        self.assertEquals(False, t is t2)
        self.assertEquals("=>(x, y)", str(t2))

        t = Not(Implies(Var('x'), Var('y')))
        t2 = propagate_negations(t)
        self.assertEquals(False, t is t2)
        self.assertEquals("and(x, not(y))", str(t2))

        t = Not(Implies(Var('x'), Not(Var('y'))))
        t2 = propagate_negations(t)
        self.assertEquals("and(x, y)", str(t2))

        t = propagate_negations(Not(Not(Not(Fun('=', Var('x'), Const('5'))))))
        self.assertEquals("not(=(x, 5))", str(t))


    def test_propagate_negations_de_morgan_laws(self):
        t = propagate_negations(Not(And(Var('x'), Var('y'))))
        self.assertEquals("or(not(x), not(y))", str(t))

        t = propagate_negations(Not(And(Not(Var('x')), Not(Var('y')))))
        self.assertEquals("or(x, y)", str(t))

        t = propagate_negations(Not(Or(Var('x'), Var('y'))))
        self.assertEquals("and(not(x), not(y))", str(t))

        t = propagate_negations(Not(Or(Not(Var('x')), Not(Var('y')))))
        self.assertEquals("and(x, y)", str(t))


    def test_move_conjunctions_to_top_not_to_changed_examples(self):
        t = move_conjunctions_to_top(And(Var('x'), Var('y')))
        self.assertEquals("and(x, y)", str(t))

        t = move_conjunctions_to_top(Or(Var('x'), Var('y')))
        self.assertEquals("or(x, y)", str(t))

        t = move_conjunctions_to_top(And(Or(Var('x'), Var('z')), Var('y')))
        self.assertEquals("and(or(x, z), y)", str(t))

        t = move_conjunctions_to_top(And(Var('x'), Or(Var('y'), Var('z'))))
        self.assertEquals("and(x, or(y, z))", str(t))


    def test_move_conjunctions_to_top_basic_nontrivial_examples(self):
        t = move_conjunctions_to_top(Or(And(Var('x'), Var('z')), Not(Var('y'))))
        self.assertEquals("and(or(x, not(y)), or(z, not(y)))", str(t))
        self.assertEquals({"or(x, not(y))", "or(z, not(y))"}, set([str(x) for x in get_clauses_from_cnf_formula(t)]))

        t = move_conjunctions_to_top(Or(Var('x'), And(Var('y'), Var('z'))))
        self.assertEquals("and(or(x, y), or(x, z))", str(t))
        self.assertEquals({"or(x, y)", "or(x, z)"}, set([str(x) for x in get_clauses_from_cnf_formula(t)]))

        t = move_conjunctions_to_top(Or(And(Var('a'), Var('b')), And(Var('c'), Var('d'))))
        self.assertEquals("and(and(or(a, c), or(a, d)), and(or(b, c), or(b, d)))", str(t))
        self.assertEquals({"or(a, c)", "or(a, d)", "or(b, c)", "or(b, d)"},
                          set([str(x) for x in get_clauses_from_cnf_formula(t)]))


    def test_move_conjunctions_to_top_more_advanced_nontrivial_examples(self):
        t = move_conjunctions_to_top(Or(And(Var('x'), Var('z')), Var('y')))
        self.assertEquals("and(or(x, y), or(z, y))", str(t))
        self.assertEquals({"or(x, y)", "or(z, y)"}, set([str(x) for x in get_clauses_from_cnf_formula(t)]))

        t = move_conjunctions_to_top(Or(Or(Var('a'), Var('b')), Or(Var('c'), And(Var('d'), Var('e')))))
        self.assertEquals("and(or(or(a, b), or(c, d)), or(or(a, b), or(c, e)))", str(t))
        self.assertEquals({"or(or(a, b), or(c, d))", "or(or(a, b), or(c, e))"},
                          set([str(x) for x in get_clauses_from_cnf_formula(t)]))


    def test_compute_cnf(self):
        t = compute_cnf(And(Var('g'), Implies(Var('r'), Var('f'))))
        self.assertEquals("and(g, or(not(r), f))", str(t))

        t = compute_cnf(Not(And(Var('g'), Implies(Var('r'), Var('f')))))
        self.assertEquals("and(or(not(g), r), or(not(g), not(f)))", str(t))


    def test_canonical_tree_form_simple_cases(self):
        t = canonical_form(Not(Var('a')))
        self.assertEquals("not(a)", str(t))

        t = canonical_form(And(Var('a'), Var('b')))
        self.assertEquals("and(a, b)", str(t))

        t = canonical_form(And(Var('a'), Var('b')))
        self.assertEquals("and(a, b)", str(t))

        t = canonical_form(And(Var('a'), Var('b'), Var('c')))
        self.assertEquals("and(a, and(b, c))", str(t))

        t = canonical_form(Or(Var('a'), Var('b')))
        self.assertEquals("or(a, b)", str(t))

        t = canonical_form(Or(Var('a'), Var('b'), Var('c')))
        self.assertEquals("or(a, or(b, c))", str(t))

        t = canonical_form(Implies(Var('a'), Var('b')))
        self.assertEquals("=>(a, b)", str(t))

        t = canonical_form(Implies(Var('a'), Var('b'), Var('c')))
        self.assertEquals("=>(a, =>(b, c))", str(t))


    def test_canonical_tree_form_complex_cases(self):
        t = canonical_form(Or(Implies(Var('a'), Fun("=", Var('x'), Const('1')), Var('c')), Var('b'), And(Var('a'), Var('b'), Var('c'))))
        t.info[':named'] = 'alt'
        self.assertEquals("(! or(=>(a, =>(=(x, 1), c)), or(b, and(a, and(b, c)))) :named alt)", str(t))
        self.assertEquals('alt', t.info[':named'])