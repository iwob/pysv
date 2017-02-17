from pysv import utils
from pysv.interm import InstructionBlockTranslator


class SMTLIBConstraints(object):
	"""SMTLIBConstraints is used to convert an abstract representation of a python program
	into the script in SMT-LIB language. This language is a standard accepted by most modern SMT solvers.
	Details of the language may be found here: http://smtlib.cs.uiowa.edu/language.shtml

	For the set of all accessible logics look here: http://smtlib.cs.uiowa.edu/logics.shtml
    """

	def __init__(self, env, assertions = None):
		assert isinstance(env, utils.Options)
		if assertions is None:
			assertions = []
		self.env = env
		self.assertions = assertions
		self.ib_translator = InstructionBlockTranslator(show_comments=self.env.show_comments, assignments_as_lets= self.env.assignments_as_lets)
		self.num_asserts = 0

	def text_epilog(self):
		text = self.env.script_epilog + '\n\n' if self.env.script_epilog else ''
		if self.env.solver_interactive_mode:
			return text + '(check-sat)\n'
		else:
			text += '(check-sat)\n' +\
			        '(get-model)\n'
			if self.env.produce_assignments:
				text += '(get-assignment)\n'
			if self.env.produce_unsat_core:
				text += '(get-unsat-core)\n'
			text += '(exit)\n'
			return text

	def reset_state(self):
		self.num_asserts = 0

	def get_program_constraints(self, ib):
		"""Returns a list of constraints representing program instructions."""
		return self.ib_translator.produce_constr_lists(ib)[0]

	def text_introduction(self):
		text  = '(set-option :print-success false)\n'
		text += '(set-option :produce-models true)\n'
		if self.env.solver_timeout is not None:
			text +=  '(set-option :timeout ' + str(self.env.solver_timeout) + ')\n'
		if self.env.seed is not None:
			text += '(set-option :random-seed ' + str(self.env.seed) + ')\n'
		if self.env.produce_unsat_core:
			text += '(set-option :produce-unsat-cores true)\n'
		if self.env.produce_proofs:
			text += '(set-option :produce-proofs true)\n'
		if self.env.produce_assignments:
			text += '(set-option :produce-assignments true)\n'

		text += '(set-logic ' + self.env.logic + ')'
		text += '\n\n' + self.env.script_prolog if self.env.script_prolog else ''
		return text

	def text_forall(self, in_vars, loc_vars):
		return self.text_quantifier('forall', in_vars, loc_vars)

	def text_exists(self, in_vars, loc_vars):
		return self.text_quantifier('exists', in_vars, loc_vars)

	def text_quantifier(self, quantifier, in_vars, loc_vars):
		text = '(' + quantifier + ' ('
		for v in sorted(in_vars.keys()):
			text += '(' + v + ' ' + in_vars[v] + ')'
		for v in sorted(loc_vars.keys()):
			text += '(' + v + ' ' + loc_vars[v] + ')'
		text += ')'
		return text

	def text_additional_assertions(self):
		if len(self.assertions) == 0:
			return ''
		text = '; Additional assertions\n'
		for a in self.assertions:
			text += a + '\n'
		return text

	def get_text(self, my_list, comment =''):
		"""Produces a string with elements of the list delimited by '\n'.
		"""
		text = ''
		if comment != '':
			text = comment + '\n'
		for el in my_list:
			text += el + '\n'
		return text

	def assertify(self, text, name = ''):
		"""Wraps constraint in a assert clause."""
		if self.env.name_all_assertions:
			if name == '':
				name = self.next_assert_name()
			return '(assert (! ' + text + ' :named ' + name + '))'
		else:
			return '(assert ' + text + ')'

	def next_assert_name(self):
		res = 'A' + str(self.num_asserts)
		self.num_asserts += 1
		return res

	def list_to_text(self, seq, comment = ''):
		text = ''
		if comment != '':
			text += '; ' + comment + '\n'
		for x in seq:
			text += x + '\n'
		return text

	@staticmethod
	def produce_vars_declarations(vars_dict, exclude = None):
		"""Generates declarations in SMT-LIB 2.0 of variables used in the formulas.

		:param vars_dict: Dictionary containing identifiers (keys) and types (values) of all program's variables.
		:param exclude: List of variables for which declaration should not be produced.
		:return (List): A List containing declarations of variables.
		"""
		res = []
		for v in sorted(vars_dict.keys()):
			if exclude is None or v not in exclude:
				t = vars_dict[v]
				res.append('(declare-fun ' + v + ' () ' + t + ')')
		return res

	@staticmethod
	def wrap_in_let_declarations(text, let_decls):
		"""Defines local variables at the beginning of the code using let function.

		:param text: (str) SMT-LIB 2.0 formula.
		:param let_decls: (list[tup[str,str]]) List of tuples, where first element is a variable name and second a term which will be substituted in place of this variable.
		:return: (str) SMT-LIB 2.0 formula enveloped in let declarations.
		"""
		def wrap_in_let_declarations(i, let_decls):
			if i >= len(let_decls):
				return text
			else:
				return '(let ((' + let_decls[i][0] + ' ' + let_decls[i][1] + '))\n' + \
				       wrap_in_let_declarations(i + 1, let_decls) + ')'
		if len(let_decls) > 0:
			return wrap_in_let_declarations(0, let_decls)
		else:
			return text