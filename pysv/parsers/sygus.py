import pysv.parsers.ply.yacc as yacc
from pysv import utils
from pysv.parsers.ply.lex import *


def parse(content):
	"""Parses Sygus problem specification into SYGUS AST tree."""

	reserved = {
		'define-sort': 'TK_DEFINE_SORT',
		'define-fun': 'TK_DEFINE_FUN',
		'declare-fun': 'TK_DECLARE_FUN',
		'set-options': 'TK_SET_OPTIONS',
		'check-synth': 'TK_CHECK_SYNTH',
		'declare-var': 'TK_DECLARE_VAR',
		'synth-fun': 'TK_SYNTH_FUN',
		'set-logic': 'TK_SET_LOGIC',
		'constraint': 'TK_CONSTRAINT',
		'BitVec': 'TK_BV',
		'Array': 'TK_ARRAY',
		'Int': 'TK_INT',
		'Bool': 'TK_BOOL',
		'Enum': 'TK_ENUM',
		'Real': 'TK_REAL',
		'Constant': 'TK_CONSTANT',
		'Variable': 'TK_VARIABLE',
		'InputVariable': 'TK_INPUT_VARIABLE',
		'LocalVariable': 'TK_LOCAL_VARIABLE',
		'let': 'TK_LET',
		'true': 'TK_BOOL_LITERAL',
		'false': 'TK_BOOL_LITERAL'
	}

	# List of token names.
	tokens = list(set(['TK_LPAREN',
	                   'TK_RPAREN',
	                   'TK_DOUBLECOLON',
	                   'TK_INT_LITERAL',
	                   'TK_REAL_LITERAL',
	                   'TK_BOOL_LITERAL',
	                   'TK_BV_LITERAL',
	                   'TK_SYMBOL',
	                   'TK_QUOTED_LITERAL'] + list(reserved.values())))
	# Seemingly unnecessary tokens from the original grammar: 'TK_ENUM_LITERAL', 'TK_ERROR'.


	# Regular expression rules for simple tokens.
	WS             =         r"\s"
	DIGIT          =         r"[0-9]"
	HEXDIGIT       =         r"[0-9A-Fa-f]"
	BIT            =         r"[01]"
	INTEGER        =         r"(-?" + DIGIT + r"+)"
	INTCONST       =         INTEGER
	BVCONST        =         r"\#x" + HEXDIGIT + r"+|\#b" + BIT + r"+"
	REALCONST      =         r"(-?" + DIGIT + r"+\." + DIGIT + r"+)"
	SYMBOLCC       =         r"[a-zA-Z\_\+\-\*\&\|\!\~\<\>\=\/\%\?\.\$\^]"
	SYMBOLCCDIGIT  =         r"[0-9a-zA-Z\_\+\-\*\&\|\!\~\<\>\=\/\%\?\.\$\^]"
	SYMBOL         =         SYMBOLCC + SYMBOLCCDIGIT + "*"
	# SYMBOL       =         SYMBOLCC + "(?:" + SYMBOLCC + "|" + DIGIT + ")*"
	QUOTEDLIT      =         r"\"(?:[a-z]|[A-Z]|" + DIGIT + r"|\.)+\""

	t_TK_LPAREN = r"\("
	t_TK_RPAREN = r"\)"
	t_TK_DOUBLECOLON = r"\:\:"

	@TOKEN(WS)
	def t_WS(t):
		return None

	@TOKEN(BVCONST)
	def t_TK_BV_LITERAL(t):
		t.type = 'TK_BV_LITERAL'
		return t

	@TOKEN(REALCONST)
	def t_TK_REAL_LITERAL(t):
		t.type = 'TK_REAL_LITERAL'
		return t

	@TOKEN(INTCONST)
	def t_TK_INT_LITERAL(t):
		t.type = 'TK_INT_LITERAL'
		return t

	@TOKEN(SYMBOL)
	def t_TK_SYMBOL(t):
		t.type = reserved.get(t.value, 'TK_SYMBOL')
		return t

	@TOKEN(QUOTEDLIT)
	def t_TK_QUOTED_LITERAL(t):
		t.type = 'TK_QUOTED_LITERAL'
		return t

	# Define a rule for comments so we can ignore them and track line numbers.
	def t_COMMENT(t):
		r';.*\n*'
		t.lexer.lineno += 1

	# Define a rule so we can track line numbers
	def t_newline(t):
		r'\n+'
		t.lexer.lineno += len(t.value)

	# Error handling rule
	def t_error(t):
		utils.logger.debug("Illegal character '%s'" % t.value[0])
		t.lexer.skip(1)



	# Build the lexer
	lexer = lex()
	lexer.input(content)

	# Print tokens
	for tok in lexer:
		utils.logger.debug('\t' + str(tok.type) + ' ' + str(tok.value) + ' ' + str(tok.lineno) + ' ' + str(tok.lexpos))








	# --------------------------------------------------------------------------------
	#                                   YACC
	# --------------------------------------------------------------------------------

	def p_start(p):
		"""start : Prog
		         | empty"""
		if p[1] is not None:
			# p[1]: list[SygusNode]
			prog = SygusNode(id='Program', args=p[1])
			p[0] = SygusNode(id='Root', args=[prog])
		else:
			p[0] = SygusNode(id='Root')

	def p_empty(p):
		"""empty : """
		pass

	def p_Prog(p):
		"""Prog : SetLogicCmd CmdPlus
		        | CmdPlus"""
		if len(p) == 2:
			p[0] = [p[1]]
		else:
			p[0] = [p[1]]
			p[0].extend(p[2])


	def p_Symbol(p):
		"""Symbol : TK_SYMBOL"""
		p[0] = p[1]

	def p_SetLogicCmd(p):
		"""SetLogicCmd : TK_LPAREN TK_SET_LOGIC Symbol TK_RPAREN"""
		p[0] = SygusNode(id='SetLogicCmd', value=p[3], args=[])

	def p_CmdPlus(p):
		"""CmdPlus : CmdPlus Cmd
		           | Cmd"""
		if len(p) == 2:
			p[0] = [p[1]]
		else:
			p[0] = p[1]
			p[0].append(p[2])

	def p_Cmd(p):
		"""Cmd : FunDefCmd
		       | FunDeclCmd
		       | SynthFunCmd
		       | CheckSynthCmd
		       | ConstraintCmd
		       | SortDefCmd
		       | SetOptsCmd
		       | VarDeclCmd"""
		p[0] = p[1] # Is always a SygusNode.

	def p_VarDeclCmd(p):
		"""VarDeclCmd : TK_LPAREN TK_DECLARE_VAR Symbol SortExpr TK_RPAREN"""
		p[0] = SygusNode(id='VarDeclCmd', value=p[3], args=[p[4]])

	def p_SortDefCmd(p):
		"""SortDefCmd : TK_LPAREN TK_DEFINE_SORT Symbol SortExpr TK_RPAREN"""
		p[0] = SygusNode(id='SortDefCmd', value=p[3], args=[p[4]])

	def p_SortExpr(p):
		"""SortExpr : TK_LPAREN TK_BV IntConst TK_RPAREN
		            | TK_INT
		            | TK_BOOL
		            | TK_REAL
		            | TK_LPAREN TK_ENUM ECList TK_RPAREN
		            | TK_LPAREN TK_ARRAY SortExpr SortExpr TK_RPAREN
		            | Symbol"""
		if len(p) == 2:
			p[0] = SygusNode(id=p[1])
		elif len(p) == 5:
			if p[2] == 'BitVec':
				p[0] = SygusNode(id=p[2], value=p[3].value)
			elif p[2] == 'Array':
				p[0] = SygusNode(id=p[2], args=[p[2], p[3]])
			else: # Enum
				p[0] = SygusNode(id=p[2], args=p[3])
		else:
			p[0] = None

	def p_IntConst(p):
		"""IntConst : TK_INT_LITERAL"""
		p[0] = SygusNode(id="IntConst", value=p[1], args=[])

	def p_BoolConst(p):
		"""BoolConst : TK_BOOL_LITERAL"""
		p[0] = SygusNode(id="BoolConst", value=p[1], args=[])

	def p_BVConst(p):
		"""BVConst : TK_BV_LITERAL"""
		p[0] = SygusNode(id="BVConst", value=p[1], args=[])

	def p_EnumConst(p):
		"""EnumConst : Symbol TK_DOUBLECOLON Symbol"""
		p[0] = SygusNode(id="EnumConst", value=(p[1], p[3]), args=[])

	def p_RealConst(p):
		"""RealConst : TK_REAL_LITERAL"""
		p[0] = SygusNode(id="RealConst", value=p[1], args=[])

	def p_ECList(p):
		"""ECList : TK_LPAREN SymbolPlus TK_RPAREN"""
		p[0] = p[2] # Just return list[SygusNode]

	def p_SymbolPlus(p):
		"""SymbolPlus : SymbolPlus Symbol
		              | Symbol"""
		if len(p) == 2:
			p[0] = [SygusNode(id="Symbol", value=p[1], args=[])]
		else:
			p[0] = p[1]
			p[0].append(p[2])

	def p_SetOptsCmd(p):
		"""SetOptsCmd : TK_LPAREN TK_SET_OPTIONS OptList TK_RPAREN"""
		p[0] = SygusNode(id="SetOptsCmd", args=p[3])  # p[3] is list[SygusNode]

	def p_OptList(p):
		"""OptList : TK_LPAREN SymbolPairPlus TK_RPAREN"""
		p[0] = SygusNode(id="OptList", args=p[2])

	def p_SymbolPairPlus(p):
		"""SymbolPairPlus : SymbolPairPlus SymbolPair
		                  | SymbolPair"""
		if len(p) == 2:
			p[0] = [p[1]]
		else:
			p[0] = p[1]
			p[0].append(p[2])

	def p_SymbolPair(p):
		"""SymbolPair : TK_LPAREN Symbol TK_QUOTED_LITERAL TK_RPAREN"""
		qlit = [SygusNode(id="QuotedLiteral", value=p[3])]
		p[0] = SygusNode(id="SymbolPair", value=p[2], args=[qlit])

	def p_FunDefCmd(p):
		"""FunDefCmd : TK_LPAREN TK_DEFINE_FUN Symbol ArgList SortExpr Term TK_RPAREN"""
		args = [p[4]]
		args.append(p[6])
		p[0] = SygusNode(id="FunDefCmd", value=p[3], sort=p[5], args=args)

	def p_FunDeclCmd(p):
		"""FunDeclCmd : TK_LPAREN TK_DECLARE_FUN Symbol TK_LPAREN SortStar TK_RPAREN SortExpr TK_RPAREN"""
		p[0] = SygusNode(id="FunDefCmd", value=p[3], sort=p[7], args=p[5])

	def p_SortStar(p):
		"""SortStar : SortStar SortExpr
		            | empty"""
		if len(p) == 2:
			p[0] = []
		else:
			p[0] = p[1]
			p[0].append(p[2])

	def p_ArgList(p):
		"""ArgList : TK_LPAREN SymbolSortPairStar TK_RPAREN"""
		p[0] = SygusNode(id='ArgList', args=p[2]) # p[2] is list[SygusNode]

	def p_SymbolSortPairStar(p):
		"""SymbolSortPairStar : SymbolSortPairStar SymbolSortPair
		                      | empty"""
		if len(p) == 2:
			p[0] = []
		else:
			p[0] = p[1]
			p[0].append(p[2])

	def p_SymbolSortPair(p):
		"""SymbolSortPair : TK_LPAREN Symbol SortExpr TK_RPAREN"""
		p[0] = SygusNode(id='SymbolSortPair', value=p[2], sort=p[3])

	def p_Term(p):
		"""Term : TK_LPAREN Symbol TermStar TK_RPAREN
		        | Literal
		        | Symbol
		        | LetTerm"""
		if len(p) > 2:
			p[0] = SygusNode(id='Op', value=p[2], args=p[3]) # p[3] is list[SygusNode]
		else:
			if type(p[1]) == str:
				p[1] = SygusNode(id='Symbol', value=p[1])
			p[0] = p[1]

	def p_LetTerm(p):
		"""LetTerm : TK_LPAREN TK_LET TK_LPAREN LetBindingTermPlus TK_RPAREN Term TK_RPAREN"""
		args = p[4]
		args.append(p[6])
		p[0] = SygusNode(id='LetTerm', args=args)

	def p_LetBindingTermPlus(p):
		"""LetBindingTermPlus : LetBindingTermPlus LetBindingTerm
		                      | LetBindingTerm"""
		if len(p) == 2:
			p[0] = []
		else:
			p[0] = p[1]
			p[0].append(p[2])

	def p_LetBindingTerm(p):
		"""LetBindingTerm : TK_LPAREN Symbol SortExpr Term TK_RPAREN"""
		p[0] = SygusNode(id='LetBindingTerm', value=p[2], sort=p[3], args=[p[4]])

	def p_TermStar(p):
		"""TermStar : TermStar Term
		            | empty"""
		if len(p) == 2:
			p[0] = []
		else:
			p[0] = p[1]
			p[0].append(p[2])

	def p_Literal(p):
		"""Literal : IntConst
		           | BoolConst
		           | BVConst
		           | EnumConst
		           | RealConst"""
		p[0] = SygusNode(id='Literal', value=p[1])

	def p_NTDefPlus(p):
		"""NTDefPlus : NTDefPlus NTDef
		             | NTDef"""
		if len(p) == 2:
			p[0] = [p[1]]
		else:
			p[0] = p[1]
			p[0].append(p[2])

	def p_NTDef(p):
		"""NTDef : TK_LPAREN Symbol SortExpr TK_LPAREN GTermPlus TK_RPAREN TK_RPAREN"""
		p[0] = SygusNode(id='NTDef', value=p[2], sort=p[3], args=p[5])

	def p_GTermPlus(p):
		"""GTermPlus : GTermPlus GTerm
		             | GTerm"""
		if len(p) == 2:
			p[0] = [p[1]]
		else:
			p[0] = p[1]
			p[0].append(p[2])

	def p_CheckSynthCmd(p):
		"""CheckSynthCmd : TK_LPAREN TK_CHECK_SYNTH TK_RPAREN"""
		p[0] = SygusNode(id='CheckSynthCmd')

	def p_ConstraintCmd(p):
		"""ConstraintCmd : TK_LPAREN TK_CONSTRAINT Term TK_RPAREN"""
		p[0] = SygusNode(id='ConstraintCmd', args=[p[3]])

	def p_SynthFunCmd(p):
		"""SynthFunCmd : TK_LPAREN TK_SYNTH_FUN Symbol ArgList SortExpr TK_LPAREN NTDefPlus TK_RPAREN TK_RPAREN"""
		args = [p[4], SygusNode(id='Grammar', args=p[7])] # p[7] is a list[SygusNode]
		p[0] = SygusNode(id='SynthFunCmd', value=p[3], sort=p[5], args=args)

	def p_GTerm(p):
		"""GTerm : Symbol
		         | Literal
		         | TK_LPAREN Symbol GTermStar TK_RPAREN
		         | TK_LPAREN TK_CONSTANT SortExpr TK_RPAREN
		         | TK_LPAREN TK_VARIABLE SortExpr TK_RPAREN
		         | TK_LPAREN TK_INPUT_VARIABLE SortExpr TK_RPAREN
		         | TK_LPAREN TK_LOCAL_VARIABLE SortExpr TK_RPAREN
		         | LetGTerm"""
		if len(p) == 2:
			if type(p[1]) == str:
				p[1] = SygusNode(id='Symbol', value=p[1])
			p[0] = p[1]
		else:
			if p[2] == 'Constant':
				p[0] = SygusNode(id='Constant', args=[p[3]])
			elif p[2] == 'Variable':
				p[0] = SygusNode(id='Constant', args=[p[3]])
			elif p[2] == 'InputVariable':
				p[0] = SygusNode(id='InputVariable', args=[p[3]])
			elif p[2] == 'LocalVariable':
				p[0] = SygusNode(id='LocalVariable', args=[p[3]])
			else: # other symbol
				p[0] = SygusNode(id='GTermOp', value=p[2], args=p[3])

	def p_LetGTerm(p):
		"""LetGTerm : TK_LPAREN TK_LET TK_LPAREN LetBindingGTermPlus TK_RPAREN GTerm TK_RPAREN"""
		args = p[4]
		args.append(p[6])
		p[0] = SygusNode(id='LetGTerm', args=args)

	def p_LetBindingGTermPlus(p):
		"""LetBindingGTermPlus : LetBindingGTermPlus LetBindingGTerm
		                       | LetBindingGTerm"""
		if len(p) == 2:
			p[0] = [p[1]]
		else:
			p[0] = p[1]
			p[0].append(p[2])

	def p_LetBindingGTerm(p):
		"""LetBindingGTerm : TK_LPAREN Symbol SortExpr GTerm TK_RPAREN"""
		p[0] = SygusNode(id='LetBindingGTerm', value=p[2], sort=p[3], args=[p[4]])

	def p_GTermStar(p):
		"""GTermStar : GTermStar GTerm
		             | empty"""
		if len(p) == 2:
			p[0] = []
		else:
			p[0] = p[1]
			p[0].append(p[2])

	# Error rule for syntax errors
	def p_error(p):
		print("Syntax error in input!")



	# Build the parser
	parser = yacc.yacc()
	return parser.parse(content)





class SygusNode(object):
	"""Stores information about given node in the AST of SYGUS benchmark specification."""
	def __init__(self, id, value = None, sort = None, args = None):
		if args is None:
			args = []
		self.id = id
		self.value = value
		self.sort = sort
		self.args = args
		self.is_terminal = len(args) == 0

	def __str__(self):
		return self.to_str(0)

	def to_str(self, indent_level = 0):
		ind = '\t' * indent_level
		text = ind + '(' + str(self.id)
		if self.value is not None:
			text += ' ' + str(self.value)
		if self.sort is not None:
			text += ' ' + str(self.sort) + ''
		if len(self.args) > 0:
			text += '\n'
			text += '\n'.join(a.to_str(indent_level+1) for a in self.args)
		text += ')'
		return text