from pysv import utils


class ProgramSmt2(object):

	def __init__(self, src, constr_list = None, let_declarations = None):
		assert (src.strip()[0] == '(' and src.strip()[-1] == ')') or len(src.split()) == 1, "Source code is not a valid SMT-LIB string! src: " + src
		if let_declarations is None:
			let_declarations = []
		if constr_list is None:
			constr_list = constr_list_from_smt2_code(src)
		self.src = src
		self.constr = constr_list
		self.let_declarations = let_declarations

	def get_wlist(self):
		return utils.str_to_wlist(self.src)

	def get_tree(self):
		return NodeSmt2.from_program_smt2(self)

	def __str__(self):
		return str(self.src)



def constr_list_from_smt2_code(code):
	"""Returns list of commands from SMT-LIB 2.0 source where each unasserted constraint is at its own line."""
	return code.split('\n')




# -------------------------------------------------------------------------------------
#                               SMT2 EXPRESSION TREE
# -------------------------------------------------------------------------------------


LOGIC_OPS = ['=>', 'and', 'or', 'not']

class NodeSmt2(object):

	def __init__(self, name, args, info = None):
		self.name = name
		self.args = args
		self.info = info if info is not None else {}
		self.is_logic_conn = name in LOGIC_OPS
		self.is_terminal = len(self.args) == 0

	def __str__(self):
		return self.str_format(sep=', ', smt2_mode=False)

	def str_smt2(self):
		return self.str_format(sep=' ', smt2_mode=True)

	def str_format(self, sep=' ', lpar='(', rpar=')', smt2_mode=False):
		if self.is_terminal:
			return self.name
		if smt2_mode:
			text = lpar + self.name + ' '
		else:
			text = self.name + lpar
		text += sep.join([a.str_format(sep, lpar, rpar, smt2_mode) for a in self.args])
		text += rpar
		if ':named' in self.info:
			return '(! ' + text + ' :named ' + self.info[':named'] + ')'
		else:
			return text

	def change_args(self, new_args):
		return NodeSmt2(self.name, new_args, self.info.copy())


	@staticmethod
	def from_wlist(words):
		if len(words) == 1:
			return NodeSmt2(words[0], [])
		else:
			assert words[0] == '('
			name = words[1]
			i = 2
			args = []
			while i < len(words)-1:
				if words[i] == '(':
					# Term in parenthesis
					j = utils.index_of_closing_parenthesis(words, i)
					args.append(NodeSmt2.from_wlist(words[i:j + 1]))
					i = j + 1
				else:
					# Term without parenthesis: variable or constant
					args.append(NodeSmt2.from_wlist([words[i]]))
					i += 1
			return NodeSmt2(name, args)

	@staticmethod
	def from_program_smt2(smt2):
		return NodeSmt2.from_wlist(smt2.get_wlist())


class And(NodeSmt2):
	def __init__(self, *args):
		assert len(args) >= 2, 'And needs at least two arguments.'
		NodeSmt2.__init__(self, 'and', args)

class Or(NodeSmt2):
	def __init__(self, *args):
		assert len(args) >= 2, 'Or needs at least two arguments.'
		NodeSmt2.__init__(self, 'or', args)

class Not(NodeSmt2):
	def __init__(self, *args):
		assert len(args) == 1, 'Not needs one argument.'
		NodeSmt2.__init__(self, 'not', args)

class Implies(NodeSmt2):
	def __init__(self, *args):
		assert len(args) >= 2, 'Implies needs at least two arguments.'
		NodeSmt2.__init__(self, '=>', args)

class Fun(NodeSmt2):
	def __init__(self, name, *args):
		NodeSmt2.__init__(self, name, args)

class Var(NodeSmt2):
	def __init__(self, name):
		NodeSmt2.__init__(self, name, [])

class Const(NodeSmt2):
	def __init__(self, name):
		NodeSmt2.__init__(self, name, [])