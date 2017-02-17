# ------------------------------------------------------------------
#
#                            Tests
# ------------------------------------------------------------------
import pysv
from pysv import contract
from pysv import smt_synthesis
from pysv import templates
from pysv import utils
from pysv import ast_utils
from pysv.smtlib.common import SMTLIBConstraints


def test_1():
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
	grammar = templates.load_gramar_from_SYGUS_spec(grammar_spec_4)
	hole = smt_synthesis.HoleDecl('H', grammar, {'x': 'Int', 'y': 'Int'}, True)
	tree = templates.HoleGrammarTree(hole, max_depth=3)
	node = tree.root[0]
	gra = tree.root[0].args[0]
	print(gra.function_name) # is HStartInt1



def test_ast():
	code_cond = """
while (x == 0 and y == 0) or z == 0:
	res = 0
"""
	code = """
x = -50
while x < 0:
	x = x + y
	y = y + 1
"""
	pre = "true"
	post = "y > 0"

	ast_tree = ast_utils.get_ast(code_cond)
	ast_utils.print_ast(ast_tree)
	instr_block = ast_utils.py_to_interm_ib(code)
	print('\nRESULT:')
	print(instr_block)


def test_3():
	import z3
	f = z3.Function('f', z3.IntSort(), z3.IntSort())
	s = z3.Solver()
	x = z3.Int('x')
	s.add(f(0) == x, f(1) == 1, f(2) == 0)
	s.check()
	print('Assertions:')
	for a in s.assertions():
		print (str(a))
	print('')
	m = s.model()
	print('Model: ' + str(m))
	print(str(m[f])) #[0 -> 1, 1 -> 1, 2 -> 0, else -> 1]
	print(str(m[f].num_entries())) #3



def test_4():
	code = """
res = x
if x < 0:
	HOLE
return res
"""
	input_vars = contract.ProgramVars({'x' : 'Int', 'res' : 'Double'})
	pre = 'True'
	post = 'res >= 0'

	pysv.smt_synthesis.synthesize(code, pre, post, input_vars)


def test_5():
	"""Testing the generation of SMT-LIB script and solving it with z3.
	"""
	code = """
z = 6
if (y > 4):
	y = x * (x + y)
else:
	z = 6
"""
	input_vars = contract.ProgramVars({'x': 'Int', 'y': 'Int', 'z': 'Int'})
	code_pre = 'x >= 2 and y > 2'
	code_post = 'y > x and y < z'

	# Converting source code into internal code representation
	ib, pre, post = pysv.smt_verifier.process_source_code(code, code_pre, code_post)
	ib, post = pysv.ssa_converter.convert(ib, pre, post, input_vars)

	# Specifying variables and their types
	input_vars.add_marked_variables(ib.collect_variables())
	print('VARIABLES: ' + str(input_vars))

	# Producing SMT-LIB script
	smtlib = SMTLIBConstraints(show_comments=False)
	script = smtlib.produce_script_verification(ib, pre, post, input_vars)
	print('\n\n******** SCRIPT ********:\n'+script)

	# Solving constraints
	solverZ3 = SolverZ3()
	res = solverZ3.apply(script)

	# Printing result
	print('******** Z3 RESULT ********\n'+str(res))
	if res.decision == 'sat':
		print("MODEL FOUND!")
	elif res.decision == 'unsat':
		print("MODEL NOT FOUND!")



def test_6():
	"""Testing the synthesis of a Python program."""
	code = """
trigger = False
newAcc = acc + 1
if newAcc < limit:
	trigger = False
else:
	newAcc = HOLE # should be 0
	newAcc = newAcc - 1
	trigger = True
	"""
	vars = contract.ProgramVars({'acc': 'Int', 'limit': 'Int'}, {'newAcc': 'Int', 'trigger': 'Bool'})
	code_pre = 'acc < limit and acc >= 0 and limit > 0'
	t1 = (['acc == limit - 1'], ['trigger == True', 'newAcc == 0'])
	t2 = (['acc < limit - 1'], ['trigger == False', 'newAcc == acc + 1'])
	code_post = contract.formula_test_cases_py([t1, t2])

	grammar_spec = """
(
	( Start Int
		( ( Constant Int ) acc limit newAcc)
	)
)
	"""
	import pysv.templates
	grammar = pysv.templates.load_gramar_from_SYGUS_spec(grammar_spec)

	hole = pysv.smt_synthesis.HoleDecl('HOLE', grammar, vars.input_vars, True)
	holes_defs = {hole.id: hole}

	res = pysv.smt_synthesis.synthesize(code, code_pre, code_post, vars, holes_defs)

	# Printing result
	print('******** Z3 RESULT ********\n' + str(res))
	if res.decision == 'sat':
		print("MODEL FOUND!")
	elif res.decision == 'unsat':
		print("MODEL NOT FOUND!")



def test_7():
	"""Testing the synthesis of a Python program."""
	code = """
a = HOLE
if x != 5:
	a = a + 1
else:
	a = a - 1
	"""
	vars = contract.ProgramVars({'x': 'Int', 'y': 'Int'}, {'a': 'Int'})
	code_pre = 'x >= 1 and y >= 1'
	code_post = 'a == 6*x + y'

	grammar_spec = """
(
	( Start Int
		( ( Constant Int ) x y (+ Start Start) (* ( Constant Int ) Start) )
	)
)
	"""
	import pysv.templates
	grammar = pysv.templates.load_gramar_from_SYGUS_spec(grammar_spec)
	hole = pysv.smt_synthesis.HoleDecl('HOLE', grammar, {'x': 'Int', 'y': 'Int'}, True, max_depth=3)
	holes_defs = {hole.id: hole}

	res = pysv.smt_synthesis.synthesize(code, code_pre, code_post, vars, holes_defs)

	# Printing result
	print('******** Z3 RESULT ********')
	print(res.text)
	print('--------------------------\n')
	print('SYNTHESIZED PYTHON CODE:')
	print(res.final_code)



def test_8():
	# ------------------------------------------------------------
	# calclex.py
	#
	# tokenizer for a simple expression evaluator for
	# numbers and +,-,*,/
	# ------------------------------------------------------------
	import pysv.parsers.ply.lex as lex

	# List of token names.   This is always required
	tokens = (
		'NUMBER',
		'PLUS',
		'MINUS',
		'TIMES',
		'DIVIDE',
		'LPAREN',
		'RPAREN',
	)

	# Regular expression rules for simple tokens
	t_PLUS = r'\+'
	t_MINUS = r'-'
	t_TIMES = r'\*'
	t_DIVIDE = r'/'
	t_LPAREN = r'\('
	t_RPAREN = r'\)'

	# A regular expression rule with some action code
	def t_NUMBER(t):
		r'\d+'
		t.value = int(t.value)
		return t

	# Define a rule so we can track line numbers
	def t_newline(t):
		r'\n+'
		t.lexer.lineno += len(t.value)

	# A string containing ignored characters (spaces and tabs)
	t_ignore = ' \t'

	# Error handling rule
	def t_error(t):
		print("Illegal character '%s'" % t.value[0])
		t.lexer.skip(1)

	# Build the lexer
	lexer = lex.lex()
	lexer.input('5 + 6 / 6')

	# Tokenize
	# for tok in lexer:
	# 	print(tok.type, tok.value, tok.lineno, tok.lexpos)


	# -------------------------------------------------------------------------------


	# Yacc example

	import pysv.parsers.ply.yacc as yacc

	# Get the token map from the lexer.  This is required.
	# from calclex import tokens

	def p_expression_plus(p):
		'expression : expression PLUS term'
		p[0] = p[1] + p[3]

	def p_expression_minus(p):
		'expression : expression MINUS term'
		p[0] = p[1] - p[3]

	def p_expression_term(p):
		'expression : term'
		p[0] = p[1]

	def p_term_times(p):
		'term : term TIMES factor'
		p[0] = p[1] * p[3]

	def p_term_div(p):
		'term : term DIVIDE factor'
		p[0] = p[1] / p[3]

	def p_term_factor(p):
		'term : factor'
		p[0] = p[1]

	def p_factor_num(p):
		'factor : NUMBER'
		p[0] = p[1]

	def p_factor_expr(p):
		'factor : LPAREN expression RPAREN'
		p[0] = p[2]

	# Error rule for syntax errors
	def p_error(p):
		print("Syntax error in input!")

	# Build the parser
	parser = yacc.yacc()

	s = '9 + 8 / 5'
	x = parser.parse(s)
	print(str(x))


def test_9():
	import pysv.parsers.sygus as sygus
	content = """
(set-logic LIA)

;; rec(x,y,z) \equiv (* (+ x x) (- y z))

(synth-fun rec ((x Int) (y Int) (z Int)) Int
	   (
	   (Start Int (x
	               y
   		       z
		       (* Start Start)
		       (+ Start Start)
		       (- Start Start)
	   ))))

(declare-var x1 Int)
(declare-var x2 Int)
(declare-var x3 Int)

(constraint (= (rec x1 x2 x3) (* (+ x1 x1) (- x2 x3))))

(check-synth)
	"""
	content2 = """
	(set-logic LIA)
	(synth-fun findIdx ( (y1 Int) (y2 Int) (k1 Int)) Int (
	(Start Int ( 0 1 2 y1 y2 k1 (ite BoolExpr Start Start)))
	(BoolExpr Bool ((< Start Start) (<= Start Start) (> Start Start) (>= Start Start)))))

	(declare-var x1 Int)
	(declare-var x2 Int)
	(declare-var k (BitVec 8))
	(constraint (=> (< x1 x2) (=> (< k x1) (= (findIdx x1 x2 k) 0))))
	(constraint (=> (< x1 x2) (=> (> k x2) (= (findIdx x1 x2 k) 2))))
	(constraint (=> (< x1 x2) (=> (and (> k x1) (< k x2)) (= (findIdx x1 x2 k) 1))))
	(check-synth)
	"""
	ast = sygus.parse(content2)
	print(str(ast))


def test_10():
	from pysv import runner
	env = utils.Options(["--synthesize", "--pre", "true", "--post", "(> x 5)", "--program", "true", "--input_vars", "x:Int", "--silent", 1, "--lang", "smt2", "--output_data", "decision", "model"])
	runner.run_from_options(env)


# ------------------------------------------------------------------
#
#                            Main
# ------------------------------------------------------------------

# test_1()

# test_ast()

# test_3()

# test_4()

# test_5()

# test_6()

# test_7()

# test_8()

test_9()

# test_10()