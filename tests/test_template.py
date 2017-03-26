import unittest
from pysv.smt_synthesis import *


class TestsTemplate(unittest.TestCase):
    grammar_spec_1 = """
    (
        ( Start Int
            (0 -1 x y z
            (+ Start Start )
            (- Start Start ))
        )
        ( StartBool Bool
            (a SpecialVal
            ( and StartBool StartBool )
            ( not StartBool )
            ( <= Start Start ))
        )
        ( SpecialVal Bool
            (b true false)
        )
    )
    """
    grammar_spec_3 = """
    (
        ( Start Int
            (x y
            (+ Start Start )
            (* Start (Constant Int) ))
        )
    )
    """
    grammar_spec_4 = """
    (
        ( Start Bool
            ((> StartInt StartInt)
            (and Start Start)
            )
        )
        ( StartInt Int
            (x y
            (+ StartInt StartInt )
            (* StartInt (Constant Int) ))
        )
    )
    """

    def test_grammar_static_methods(self):
        grammar = load_gramar_from_SYGUS_spec(TestsTemplate.grammar_spec_1)

        val = Grammar.get_symbols_usage_in_rule(grammar['Start'], grammar)
        self.assertEquals({'Start': 2}, val)

        val = Grammar.get_symbols_usage_in_rule(grammar['StartBool'], grammar)
        self.assertEquals({'Start': 2, 'StartBool': 2, 'SpecialVal': 1}, val)

        val = Grammar.get_symbols_usage_in_rule(grammar['SpecialVal'], grammar)
        self.assertEquals({}, val)


    def test_grammar_production(self):
        grammar = load_gramar_from_SYGUS_spec(TestsTemplate.grammar_spec_4)

        p = grammar['Start'][0]
        self.assertEquals(['(', '>', 'StartInt', 'StartInt', ')'], p.body)
        self.assertEquals(['StartInt', 'StartInt'], p.get_rule_symbols())

        p = grammar['StartInt'][3]
        self.assertEquals(['(', '*', 'StartInt', '(', 'Constant', 'Int', ')', ')'], p.body)
        self.assertEquals(['StartInt'], p.get_rule_symbols())


    def test_grammar_node_rich_body(self):
        grammar = load_gramar_from_SYGUS_spec(TestsTemplate.grammar_spec_4)
        hole = HoleDecl('H', grammar, {'x': 'Int', 'y': 'Int'}, True)
        tree = HoleGrammarTree(hole, 2)

        self.assertEquals(['(', '>', 'StartInt', 'StartInt', ')'], tree.root[0].prod.body)
        rich_body = tree.root[0].get_rich_body()
        e = rich_body[0]
        self.assertEquals('(', e.text)
        self.assertEquals(1, e.level)
        self.assertEquals(False, e.is_op)
        self.assertEquals(False, e.is_commutative_op)
        self.assertEquals(False, e.is_rule_symb)
        self.assertEquals(None, e.rule_symb_arg)

        e = rich_body[1]
        self.assertEquals('>', e.text)
        self.assertEquals(1, e.level)
        self.assertEquals(True, e.is_op)
        self.assertEquals(False, e.is_commutative_op)
        self.assertEquals(False, e.is_rule_symb)
        self.assertEquals(None, e.rule_symb_arg)

        e = rich_body[2]
        self.assertEquals('StartInt', e.text)
        self.assertEquals(1, e.level)
        self.assertEquals(False, e.is_op)
        self.assertEquals(False, e.is_commutative_op)
        self.assertEquals(True, e.is_rule_symb)
        self.assertEquals(tree.root[0][0], e.rule_symb_arg)

        e = rich_body[3]
        self.assertEquals('StartInt', e.text)
        self.assertEquals(1, e.level)
        self.assertEquals(False, e.is_op)
        self.assertEquals(False, e.is_commutative_op)
        self.assertEquals(True, e.is_rule_symb)
        self.assertEquals(tree.root[0][1], e.rule_symb_arg)

        e = rich_body[4]
        self.assertEquals(')', e.text)
        self.assertEquals(1, e.level)
        self.assertEquals(False, e.is_op)
        self.assertEquals(False, e.is_commutative_op)
        self.assertEquals(False, e.is_rule_symb)
        self.assertEquals(None, e.rule_symb_arg)


    def test_load_grammar_from_SYGUS_spec(self):
        grammar = load_gramar_from_SYGUS_spec(TestsTemplate.grammar_spec_1)

        set_prods_start = set([" ".join(x.body) for x in grammar['Start'].productions])
        self.assertEquals({'0', '-1', 'x', 'y', 'z', '( + Start Start )', '( - Start Start )'}, set_prods_start)

        set_prods_start_bool = set([" ".join(x.body) for x in grammar['StartBool'].productions])
        self.assertEquals({'a', 'SpecialVal', '( and StartBool StartBool )', '( not StartBool )', '( <= Start Start )'}, set_prods_start_bool)

        self.assertEquals(3, len(grammar.rules))

        self.assertEquals({'x':'Int', 'y':'Int', 'z':'Int', 'a':'Bool', 'b':'Bool'}, grammar.get_used_var_names())

        prod = grammar['Start'][5]
        self.assertEquals(['Start', 'Start'], Grammar.get_rule_symbols_in_production(prod, grammar))
        prod = grammar['Start'][0]
        self.assertEquals([], Grammar.get_rule_symbols_in_production(prod, grammar))


    def test_hole_grammar_tree_level_one_grammar(self):
        grammar_spec = """
        (
            ( Start Int
                (
                    0 x y
                    (Constant Real)
                    (+ x (InputVariable Int))
                    (+ (Constant Int) (Constant Int))
                )
            )
        )
        """
        grammar = load_gramar_from_SYGUS_spec(grammar_spec)
        hole = HoleDecl('H', grammar, {'x': 'Int', 'y': 'Int', 'a': 'Bool', 'b': 'Bool'}, True)
        tree = HoleGrammarTree(hole, 2)

        self.assertEquals({'InputVariable_Int': 1}, Grammar.get_symbols_usage_in_rule(tree.root.rule, grammar))


        self.assertEquals('HStart0_r0', tree.root.struct_var_name)
        self.assertEquals(5, tree.root.max_struct_var_value())
        self.assertEquals(6, len(tree.root.args))

        node = tree.root.args[0]
        self.assertEquals(GrammarLeaf, type(node))
        self.assertEquals(['0'], node.body)
        self.assertEquals({}, node.vars)

        node = tree.root.args[1]
        self.assertEquals(GrammarLeaf, type(node))
        self.assertEquals(['x'], node.body)
        self.assertEquals({}, node.vars)

        node = tree.root.args[2]
        self.assertEquals(GrammarLeaf, type(node))
        self.assertEquals(['y'], node.body)
        self.assertEquals({}, node.vars)

        node = tree.root.args[3]
        self.assertEquals(GrammarLeaf, type(node))
        self.assertEquals(['HStart0_Real0'], node.body)
        self.assertEquals({'HStart0_Real0': 'Real'}, node.vars)

        node = tree.root.args[4]
        self.assertEquals(GrammarOp, type(node))
        self.assertEquals(['(', '+', 'x', 'InputVariable_Int', ')'], node.body)
        self.assertEquals({}, node.vars)

        node = tree.root.args[5]
        self.assertEquals(GrammarLeaf, type(node))
        self.assertEquals(['(', '+', 'HStart0_Int0', 'HStart0_Int1', ')'], node.body)
        self.assertEquals({'HStart0_Int0': 'Int', 'HStart0_Int1': 'Int'}, node.vars)


    def test_hole_grammar_tree_recursive_grammar(self):
        grammar = load_gramar_from_SYGUS_spec(TestsTemplate.grammar_spec_3)
        hole = HoleDecl('H', grammar, {'x': 'Int', 'y': 'Int'}, True)
        tree = HoleGrammarTree(hole, 2)

        self.assertEquals('HStart0', tree.root.function_name)
        self.assertEquals({'Start': 2}, Grammar.get_symbols_usage_in_rule(tree.root.rule, grammar))


        node = tree.root.args[0] # Start0, r=0
        self.assertEquals(['x'], node.body)

        node = tree.root.args[1] # Start0, r=1
        self.assertEquals(['y'], node.body)

        # --------------------------
        node = tree.root.args[2] # Start0, r=2
        self.assertEquals(GrammarOp, type(node))
        self.assertEquals(['(', '+', 'Start', 'Start', ')'], node.body)
        self.assertEquals({}, node.vars)
        self.assertEquals(2, len(node.args))

        gra = node.args[0] # Start1
        self.assertEquals(2, len(gra.args))
        self.assertEquals(GrammarRuleApplier, type(gra))
        self.assertEquals('HStart1_r1', gra.struct_var_name)
        self.assertEquals(['x'], gra[0].body)
        self.assertEquals(['y'], gra[1].body)
        # Other nodes were not added because of depth=2 limit.

        gra = node.args[1] # Start2
        self.assertEquals(2, len(gra.args))
        self.assertEquals(GrammarRuleApplier, type(gra))
        self.assertEquals('HStart2_r2', gra.struct_var_name)
        self.assertEquals(['x'], gra[0].body)
        self.assertEquals(['y'], gra[1].body)
        # Other nodes were not added because of depth=2 limit.

        #--------------------------
        node = tree.root.args[3]
        self.assertEquals(GrammarOp, type(node))
        self.assertEquals(['(', '*', 'Start', 'HStart0_Int0', ')'], node.body)
        self.assertEquals({'HStart0_Int0': 'Int'}, node.vars)
        self.assertEquals(1, len(node.args))
        gra = node.args[0]
        self.assertEquals(2, len(gra.args))
        self.assertEquals(GrammarRuleApplier, type(gra))
        # self.assertEquals('HStart3_r3', gra.struct_var_name) # before rule applier sharing
        self.assertEquals('HStart1_r1', gra.struct_var_name)
        self.assertEquals(['x'], gra[0].body)
        self.assertEquals(['y'], gra[1].body)


    def test_hole_grammar_tree_many_rules_grammar(self):
        grammar = load_gramar_from_SYGUS_spec(TestsTemplate.grammar_spec_4)
        hole = HoleDecl('H', grammar, {'x': 'Int', 'y': 'Int'}, True)
        tree = HoleGrammarTree(hole, 3)

        self.assertEquals({'Start': 2, 'StartInt': 2}, Grammar.get_symbols_usage_in_rule(tree.root.rule, grammar))


        node = tree.root[0]
        self.assertEquals(GrammarOp, type(node))
        self.assertEquals(2, len(node.args))
        self.assertEquals(['(', '>', 'StartInt', 'StartInt', ')'], node.body)

        gra = tree.root[0].args[0]
        self.assertEquals('HStartInt11', gra.function_name)
        self.assertEquals(['x'], gra[0].body)
        self.assertEquals(['y'], gra[1].body)
        self.assertEquals(['(', '+', 'StartInt', 'StartInt', ')'], gra[2].body)
        self.assertEquals(['(', '*', 'StartInt', 'HStartInt11_Int0', ')'], gra[3].body)
        self.assertEquals(2, len(gra[3].args[0].args))
        self.assertEquals(['x'], gra[3].args[0][0].body)
        self.assertEquals(['y'], gra[3].args[0][1].body)

        node = tree.root[1]
        self.assertEquals(GrammarOp, type(node))
        self.assertEquals(2, len(node.args))
        self.assertEquals(['(', 'and', 'Start', 'Start', ')'], node.body)


    def test_grammar_variable_markers(self):
        grammar_spec = """
        (
            (Start Int (
                    (InputVariable Int)
                    (LocalVariable Int)
                    (Variable Int)
                    (+ Start Start)
                    (* Start Start)
            ))
        )
        """
        grammar = load_gramar_from_SYGUS_spec(grammar_spec)
        self.assertEquals(1, len(grammar.rules))
        self.assertTrue('Start' in grammar.rules)

        vars = ProgramVars({'in1': 'Int', 'in2': 'Int'}, {'loc1': 'Int', 'loc2': 'Int'})
        hole = HoleDecl('H', grammar, vars, True, max_depth=2)

        # In HoleDecl grammar is modified - added are rules for variables of certain types.
        self.assertEquals(4, len(grammar.rules))
        self.assertTrue('InputVariable_Int' in grammar.rules)
        self.assertTrue('LocalVariable_Int' in grammar.rules)
        self.assertTrue('Variable_Int' in grammar.rules)
        self.assertTrue('Start' in grammar.rules)


        tree = HoleGrammarTree(hole, 3)


        node = tree.root[0]  # (InputVariable Int)
        self.assertEquals(GrammarOp, type(node))
        self.assertEquals(['InputVariable_Int'], node.body)
        self.assertEquals(1, len(node.args))
        self.assertEquals(GrammarRuleApplier, type(node.args[0]))
        self.assertEquals(2, len(node.args[0].args))
        v_names = {node.args[0][0].body[0],
                   node.args[0][1].body[0]}
        self.assertEquals({'in1', 'in2'}, v_names)

        node = tree.root[1]  # (LocalVariable Int)
        self.assertEquals(['LocalVariable_Int'], node.body)
        self.assertEquals(1, len(node.args))
        self.assertEquals(GrammarRuleApplier, type(node.args[0]))
        self.assertEquals(2, len(node.args[0].args))
        v_names = {node.args[0][0].body[0],
                   node.args[0][1].body[0]}
        self.assertEquals({'loc1', 'loc2'}, v_names)

        node = tree.root[2]  # (Variable Int)
        self.assertEquals(['Variable_Int'], node.body)
        self.assertEquals(['Variable_Int'], node.body)
        self.assertEquals(1, len(node.args))
        self.assertEquals(GrammarRuleApplier, type(node.args[0]))
        self.assertEquals(4, len(node.args[0].args))
        v_names = {node.args[0][0].body[0],
                   node.args[0][1].body[0],
                   node.args[0][2].body[0],
                   node.args[0][3].body[0]}
        self.assertEquals({'in1', 'in2', 'loc1', 'loc2'}, v_names)


    def test_grammar_tree_with_no_nodes(self):
        grammar_spec = """
        (
            (Start Int (
                    (Variable Int)
                    (+ Start Start)
                    (* Start Start)
            ))
        )
        """
        grammar = load_gramar_from_SYGUS_spec(grammar_spec)
        vars = ProgramVars({'in1': 'Int', 'in2': 'Int'}, {'loc1': 'Int', 'loc2': 'Int'})
        hole = HoleDecl('H', grammar, vars, True)
        tree = HoleGrammarTree(hole, max_depth=1)

        # The thing is, for this grammar a tree with depth 1 is impossible, because
        # (Variable Int) marker is interpreted as a call to Variable_Int grammar rule.
        self.assertEquals(None, tree.root)


    def test_grammar_tree_with_only_variables(self):
        grammar_spec = """
        (
            (Start Int (
                    (InputVariable Int)
                    (+ Start Start)
                    (* Start Start)
            ))
        )
        """
        grammar = load_gramar_from_SYGUS_spec(grammar_spec)
        vars = ProgramVars({'in1': 'Int', 'in2': 'Int'}, {'loc1': 'Int', 'loc2': 'Int'})
        hole = HoleDecl('H', grammar, vars, True)
        tree = HoleGrammarTree(hole, max_depth=2)

        # For this grammar only one tree with depth 2 is possible, because
        # (InputVariable Int) marker is interpreted as a call to Variable_Int grammar rule.
        # Thus, this grammar allows to produce only in1 or in2.
        self.assertEquals(1, len(tree.root.args))
        node = tree.root[0]
        self.assertEquals(GrammarOp, type(node))
        self.assertEquals(['InputVariable_Int'], node.rule_symbols)
        self.assertEquals(GrammarRuleApplier, type(node[0]))
        self.assertEquals(2, len(node[0].args))
        self.assertEquals(['in1'], node[0][0].body)
        self.assertEquals(['in2'], node[0][1].body)
