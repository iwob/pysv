import copy
from pysv.smtlib.common import *
from pysv import contract
from pysv import templates
from pysv import ast_utils
from pysv.interm import Var
from pysv.smt2 import ProgramSmt2


class SynthesisConstr(SMTLIBConstraints):

	def __init__(self, env, assertions = None):
		SMTLIBConstraints.__init__(self, env, assertions)


	def produce_script_synthesis(self, PROGRAM, PRE, POST, program_vars, holes_decls, free_vars = None):
		"""Produces a complete SMT-LIB 2.0 script ready to be used as an input to the solver. This script will contain constraints for solving a **synthesis** task.

		:param PROGRAM: (ProgramSmt2) Instruction block in SSA form for which constraints will be produced.
		:param PRE: (ProgramSmt2) Precondition expression.
		:param POST: (ProgramSmt2) Postcondition expression.
		:param program_vars: (ProgramVars) object containing identifiers and types of all program's variables.
		:param holes_decls: (list[HoleDecl]) List containing declarations of all holes present in the program. If empty, then synthesis is performed only on the free variables.
		:param free_vars: (list[str]) Names of variables in the program which are free and which are part of the final solution together with decisions on how holes should be filled.
		:return: (str) Text of SMT-LIB 2.0 script realizing synthesis task.
		"""
		if free_vars is None:
			free_vars = []
		assert (type(PROGRAM) == ProgramSmt2)
		assert (type(PRE) == ProgramSmt2)
		assert (type(POST) == ProgramSmt2)
		assert (type(program_vars) == contract.ProgramVars)

		self.reset_state()
		struct_vars_decls, hole_funs_defs = self.analyze_all_holes(holes_decls)

		text  = self.text_introduction() + '\n\n'
		text += self.text_decls_free_vars(program_vars, free_vars) + '\n'
		text += self.text_decls_struct_vars(struct_vars_decls) + '\n'
		text += self.text_hole_functions(hole_funs_defs) + '\n\n'
		text += self.get_synthesis_formula_smt2(PROGRAM, PRE, POST, program_vars, free_vars) + '\n\n'
		text += self.text_additional_assertions() + '\n'
		text += self.text_epilog()
		return text

	def text_decls_struct_vars(self, struct_vars_decls):
		return self.list_to_text(struct_vars_decls, 'Structural variables')

	def text_hole_functions(self, hole_funs):
		return self.list_to_text(hole_funs, 'Definitions of hole functions')

	def text_decls_free_vars(self, program_vars, free_vars):
		if free_vars is not None and self.env.synth_substitute_free:
			free_decls = self.produce_vars_declarations(self.free_vars_decls(program_vars, free_vars))
			return self.list_to_text(free_decls, 'Free variables')
		else:
			return ''

	def free_vars_decls(self, program_vars, free_vars):
		res = {}
		all_vars = program_vars.all()
		for v in free_vars:
			if v in all_vars:
				res[v] = all_vars[v]
			else:
				raise Exception("Declared free variable " + str(v) + " was not specified as a program's variable!")
		return res

	def analyze_all_holes(self, hole_decls):
		"""Produces structural var declarations and functions for all holes in the instruction block."""
		synthManager = HolesConstrGenerator(hole_decls,
		                                    name_struct_assertions=self.env.name_struct_assertions,
		                                    allow_commutative_constr=self.env.allow_commutative_constr)
		vars_decls = synthManager.stack_var_declarations
		holes_funs = reversed(synthManager.stack_holes_functions)
		return vars_decls, holes_funs


	def get_synthesis_formula_smt2(self, PROGRAM, PRE, POST, program_vars, free_vars):
		"""Returns asserted text of the synthesis formula.

		:param PROGRAM: (ProgramSmt2) Instruction block of the program's body.
		:param PRE: (ProgramSmt2) Precondition expression.
		:param POST: (ProgramSmt2) Precondition expression.
		:param program_vars: (ProgramVars) Object containing identifiers and types of all program's variables.
		:param free_vars: (list[str]) Names of variables in the program which are free and which are part of the final solution together with decisions on how holes should be filled.
		:return: (str) Final asserted SMT-LIB 2.0 code of the synthesis formula.
		"""
		synth   = self.synthesis_formula_forall_standard(PROGRAM, PRE, POST, program_vars, free_vars)
		synth   = self.assertify(synth, 'SYNTH_FORMULA')
		return synth


	def synthesis_formula_forall_standard(self, PROGRAM, PRE, POST, program_vars, free_vars):
		"""Unasserted synthesis formula in the form of: forall(input_vars and local_vars) PRE and PROGRAM => POST..

		:param PROGRAM: (ProgramSmt2) Instruction block of the program's body.
		:param PRE: (ProgramSmt2) Precondition expression.
		:param POST: (ProgramSmt2) Precondition expression.
		:param program_vars: (ProgramVars) Object containing identifiers and types of all program's variables.
		:return: (str) Unasserted SMT-LIB 2.0 code of the synthesis formula.
		"""
		in_vars, loc_vars = self.synthesis_get_forall_vars(program_vars, PROGRAM.let_declarations, free_vars=free_vars)
		text_forall = self.text_forall(in_vars, loc_vars)
		body_text = '\t(=>\n' + \
		            '\t\t(and\n' + \
		            '\t\t\t;PRECONDITION\n' + \
		            '\t\t\t' + str(PRE) + '\n' + \
		            '\t\t\t;PROGRAM:\n' + \
		            '\t\t\t' + str(PROGRAM) + '\n' + \
		            '\t\t)\n' + \
		            '\t\t;POSTCONDITION:\n' + \
		            '\t\t' + str(POST) + '\n' + \
		            '\t)'
		body_text = SMTLIBConstraints.wrap_in_let_declarations(body_text, PROGRAM.let_declarations)
		body_text = text_forall + '\n' + body_text + '\n)'
		return body_text


	def synthesis_formula_forall_nonstandard(self, PROGRAM, PRE, POST, program_vars):
		"""Synthesis formula in the form of: forall(input_vars and local_vars) PRE => PROGRAM and POST."""
		in_vars, loc_vars = self.synthesis_get_forall_vars(program_vars, PROGRAM.let_declarations)
		text_forall = self.text_forall(in_vars, loc_vars)
		body_text = text_forall + '\n' + \
			       '\t(=>\n' + \
			       '\t\t;PRECONDITION\n' + \
			       '\t\t' + str(PRE) + '\n' + \
			       '\t\t(and\n' + \
			       '\t\t\t;PROGRAM:\n' + \
			       '\t\t\t' + str(PROGRAM) + '\n' + \
			       '\t\t\t;POSTCONDITION:\n' + \
			       '\t\t\t' + str(POST) + '\n' + \
			       '\t\t)\n' + \
			       '\t)\n' + \
			       ')'
		body_text = SMTLIBConstraints.wrap_in_let_declarations(body_text, PROGRAM.let_declarations)
		return body_text


	def synthesis_get_forall_vars(self, program_vars, let_decls, free_vars):
		if self.env.assignments_as_lets:
			# TODO: handle free_vars
			all_vars = program_vars.all().copy()
			let_vars = [v[0] for v in let_decls]
			res = {}
			for k in all_vars:
				if k not in let_vars:
					res[k] = all_vars[k]
			return res, {}
		else:
			loc_vars = {k:v for k, v in program_vars.local_vars.items() if k not in free_vars}
			return program_vars.input_vars, loc_vars







class SynthesisConstrTestCases(SynthesisConstr):

	def __init__(self, test_cases, env, assertions = None, holes_decls = None):
		SynthesisConstr.__init__(self, env, assertions)
		self.test_cases = test_cases
		self.test_binded_vars = []
		if holes_decls is None:
			holes_decls = []
		self.holes_decls = holes_decls
		self.fitness_tpe = 'Int'
		if self.env.logic in {'NRA', 'QF_NRA', 'LRA', 'QF_LRA'}:
			self.fitness_tpe = 'Real'


	def get_synthesis_formula_smt2(self, ib, pre, post, program_vars, free_vars):
		"""Returns asserted text of the synthesis formula for test cases.

		:param ib: (InstructionBlock) Instruction block in SSA form in the intermediary representation.
		:param pre: (InstrExpr) Precondition expression in the intermediary representation.
		:param post: (InstrExpr) Postcondition expression in the intermediary representation.
		:param program_vars: (ProgramVars) Information about identifiers and types of all variables in the program.
		:return: Final SMT-LIB 2.0 code of the asserted synthesis formula.
		"""
		all_vars = program_vars.all()
		self.test_binded_vars = [v for v in all_vars if v not in free_vars]
		num = 0
		text = '; ---------------------------------------------------------------------\n'
		text += '; CONSTRAINTS FOR ALL TEST CASES:\n'
		text += '; ---------------------------------------------------------------------\n\n'
		for tc in self.test_cases:

			# Renaming all variables so they have a suffix of the test case.
			pre_words = self.tc_rename_vars_in_words(pre.get_wlist(), all_vars, num, free_vars)
			post_words = self.tc_rename_vars_in_words(post.get_wlist(), all_vars, num, free_vars)
			program_constr = self.rename_program_constr(ib.constr[:], all_vars, num, free_vars)
			program_vars2 = self.get_tc_renamed_vars(program_vars, all_vars, num, free_vars)

			TC_POST = self.get_post_for_tc(tc, program_vars, all_vars, num, free_vars)
			PRE = ' '.join(pre_words)
			POST = ' '.join(post_words)

			text += self.synthesis_formula_single_test_case(tc, PRE, program_constr, POST, TC_POST,
			                                                program_vars2, num, free_vars)
			num += 1

		if self.env.synth_mode != utils.Options.MODE_NORMAL:
			# Epilog containing optimization formula.
			text += self.get_tc_opt_epilog_formula(num)
		return text


	def rename_program_constr(self, program_constr, all_vars, num, exclude):
		res = []
		for c in program_constr:
			words = utils.str_to_wlist(c)
			words = self.tc_rename_vars_in_words(words, all_vars, num, exclude)
			res.append(' '.join(words).replace('( ', '(').replace(' )', ')'))
		return res


	def get_post_for_tc(self, tc, program_vars, all_vars, testNum, exclude):
		tc_post_pure = ast_utils.py_to_interm_expr(tc.code_outputs())
		for v in contract.ProgramVars.get_base_vars(program_vars.local_vars):
			if exclude is None or v not in exclude:
				new_name = program_vars.get_latest_var_name(v)
				if new_name != v:
					tc_post_pure.src.rename_var(v, new_name)
		tc_post = self.tc_rename_vars_instructions(tc_post_pure, all_vars, testNum, exclude)
		tc_post = tc_post.to_smt2(self.env).src
		return tc_post


	def synthesis_formula_single_test_case(self, tc, PRE, program_constr, POST, TC_POST, program_vars, num, free_vars):
		# Producing var declarations together with definition of test input.
		decls = self.produce_decls_inputs_as_funs(tc, program_vars)
		decls.extend(self.produce_vars_declarations(program_vars.local_vars, free_vars))


		text  = '; DECLARATIONS: Local variables (T' + str(num) + ')\n'
		text += self.list_to_text(decls) + '\n'

		text += '; PRECONDITIONS (T' + str(num) + ')\n'
		if PRE != 'true':
			text += self.assertify(PRE, self.name_assert(num, 'pre')) + '\n'
		text += '\n'


		text += '; PROGRAM (T' + str(num) + ')\n'
		for i in range(0, len(program_constr)):
			c = program_constr[i]
			text += self.assertify(c, self.name_assert(num, 'p' + str(i))) + '\n'
		text += '\n'


		text += '; POSTCONDITION (T' + str(num) + ')\n'
		if self.env.synth_mode == utils.Options.MODE_NORMAL:
			text += self.assertify(TC_POST, self.name_assert(num, 'tpost')) + '\n'
		else:
			# Definition of variable storing information about passing or not a test case.
			if self.env.tc_fitness_mode == 'normal':
				text += '(define-fun itest{0} () Int (ite (! {1} :named pass_itest{0}) 1 0))\n'.format(num, TC_POST)

			elif self.env.tc_fitness_mode == 'L1':
				assert len(tc.outputs) == 1 # Simplifying assumption: for each test case program returns only 1 value.
				real_out = self.new_name(tc.out_vars[0], num)
				expected_out = tc.outputs[0]
				text += '(define-fun itest{0} () {1} (abs (- {2} {3})))\n'.format(num, self.fitness_tpe, real_out, expected_out)


		if POST != 'true': # there is a non-trivial postcondition.
			text += self.assertify(POST, self.name_assert(num, 'post')) + '\n\n'
		text += '; ---------------------------------------------------------------------\n\n'
		return text


	def get_tc_opt_epilog_formula(self, numTests):
		assert self.env.synth_mode != utils.Options.MODE_NORMAL
		text = ''
		if self.env.tc_fitness_mode == 'normal':
			text += '(declare-fun fitness () Int)\n'
		else:
			text += '(declare-fun fitness () {0})\n'.format(self.fitness_tpe)
		text += '(assert (= fitness (+'
		for i in range(0, numTests):
			text += ' itest{0}'.format(str(i))
		text += ')))\n\n'
		if self.env.synth_min_passed_tests is not None:
			# In this mode instead of optimization we allow solution to be imperfect to some degree.
			# synth_tc_min_passed is the minimum number of tests solution must pass.
			limit = abs(self.env.synth_min_passed_tests)
			if limit > numTests:
				limit = numTests
			text += '(assert (>= fitness {0}))\n'.format(limit)
		elif self.env.synth_mode == utils.Options.MODE_MIN:
			text += '(minimize fitness)\n'
		elif self.env.synth_mode == utils.Options.MODE_MAX:
			text += '(maximize fitness)\n'
		return text

	def produce_decls_inputs_as_funs(self, tc, program_vars):
		decls = []
		for v in sorted(program_vars.input_vars.keys()):
			x = tc.get_by_name(self.old_name(v))
			if x is None:
				raise Exception('Cannot produce function definition for variable! Value in tests is missing.')
			else:
				vtype = program_vars.input_vars[v]
				decls.append('(define-fun ' + v + ' () ' + vtype + ' ' + str(x) + ')')
		return decls

	def get_tc_renamed_vars(self, program_vars, vars, num, exclude):
		res_prog_vars = copy.deepcopy(program_vars)
		for v in vars:
			if exclude is None or Var.base_id(v) not in exclude:
				res_prog_vars.rename_var(v, self.new_name(v, num))
		return res_prog_vars

	def tc_rename_vars_instructions(self, obj, vars, num, exclude):
		for v in vars:
			if exclude is None or v not in exclude:
				obj.src.rename_var(v, self.new_name(v, num))
		return obj

	def tc_rename_vars_in_words(self, words, vars, num, exclude):
		for i in range(len(words)):
			if words[i] in vars and (exclude is None or words[i] not in exclude):
				words[i] = self.new_name(words[i], num)
		return words

	def old_name(self, v):
		base = Var.base_id(v)
		i = base.rfind('_')
		return v.replace(base, base[0:i])

	def new_name(self, v, num):
		return Var.change_base_name(v, Var.base_id(v) + '_T' + str(num))

	def name_assert(self, test_num, comment =''):
		res = 'T' + str(test_num) + '_' + comment
		return res

	def text_additional_assertions(self):
		"""Overrides text_additional_assertions method from the SMTLIBConstraints class."""
		if not self.env.tc_rename_vars_in_assignments:
			return SMTLIBConstraints.text_additional_assertions(self)
		else:
			if len(self.assertions) == 0:
				return ''
			text = '; Additional assertions\n'
			processed_assertions = self.preprocess_assertions(self.assertions)
			for a in processed_assertions:
				if self.assert_should_be_test_binded(a):
					# Test-binding of assertion.
					for i in range(len(self.test_cases)):
						a2 = self.tc_rename_vars_in_str(a, self.test_binded_vars, i)
						text += a2 + '\n'
				else:
					text += a + '\n'
			return text

	def assert_should_be_test_binded(self, text):
		for v in self.test_binded_vars:
			if v in text:
				return True
		for h in self.holes_decls:
			if h.id in text:
				return True
		return False

	def preprocess_assertions(self, assertions):
		res = [a.replace(")", " )") for a in assertions]
		return self.interpret_holes_in_assertions(res)

	def interpret_holes_in_assertions(self, assertions):
		"""Expands each hole id found in additional assertions to call to appropriate function. Assertions must be preprocessed."""
		if len(self.holes_decls) == 0:
			return assertions
		else:
			res = []
			for a in assertions:
				text = a
				for h in self.holes_decls:
					text = text.replace(h.id+" ", h.get_function_call()+" ")
				res.append(text.replace(")", " )"))
			return res

	def tc_rename_vars_in_str(self, s, vars, num):
		"""Changes names of variables in string to those appropriate for a given test. String should be preprocessed before passing to this function."""
		for v in vars:
			s = s.replace(v+" ", self.new_name(v, num)+" ")
		return s



class HolesConstrGenerator(object):
	"""HolesConstrGenerator is a helper class for parsing grammar of a hole and generating declarations of structural variables and definitions of hole functions. Generally speaking, a function will be generated for each grammar rule.

	Attributes:
	-----------
	stack_var_declarations : list[string]
		List of complete SMTLIB declarations of all structural variables.
	stack_holes_functions : list[string]
		List of complete SMTLIB definitions of all hole functions.
	"""
	def __init__(self, all_holes, allow_commutative_constr = False, name_struct_assertions = False):
		self.allow_commutative_constr = allow_commutative_constr
		self.name_struct_assertions = name_struct_assertions
		self.all_holes = all_holes
		self.stack_var_declarations = []
		"""Contains declarations of all variables created during production of constraints."""
		self.stack_holes_functions = []
		"""Contains declarations of all hole functions."""
		self.declared_var_names = set()
		self.declared_fun_names = set()
		self.commutative_processed = set()
		self.num_asserts = 0
		self.fill_stacks()

	def fill_stacks(self):
		"""Fills all stacks with constraints in SMTLIB format."""
		for hole in self.all_holes:
			gt = hole.grammar_tree
			# Traversing grammar tree and adding all variables and functions.
			self.push_all_var_declarations(gt.root)
			if self.allow_commutative_constr:
				self.push_all_commutative_constr(gt.root)
			self.push_all_hole_funs(gt.root)

		# print('\n\n[GrammarTree] VAR DECLARATIONS:\n')
		# for vd in self.stack_var_declarations:
		# 	print(vd)
		# print('----------------\n')
		# print('\n\n[GrammarTree] FUNS FOR ALL HOLES:\n')
		# for hf in self.stack_holes_functions:
		# 	print(hf)
		# print('----------------\n')

	def push_all_commutative_constr(self, node):
		if isinstance(node, templates.GrammarOp):
			if len(node.rule_symbols) >= 2:
				self.push_single_commutative_constraint(node)
		for a in node.args:
			self.push_all_commutative_constr(a)

	def push_single_commutative_constraint(self, node):
		assert isinstance(node, templates.GrammarOp)
		rich_body = node.get_rich_body()

		def get_all_from_level(level):
			return [w for w in rich_body if w.level == level]

		def process_level(all_from_level):
			dict_last_rsymb_w = {}
			for wol in all_from_level:
				if wol.is_rule_symb:
					if wol.text in dict_last_rsymb_w:
						prev_arg = dict_last_rsymb_w[wol.text]
						# Generating constraint
						self.push_commutative_constr(prev_arg, wol.rule_symb_arg, node.parent, node.parent_arg_no)
					dict_last_rsymb_w[wol.text] = wol.rule_symb_arg

		for w in rich_body:
			if w.is_commutative_op:
				all_from_level = get_all_from_level(w.level)
				process_level(all_from_level)

	def push_commutative_constr(self, node1, node2, parent_node, production_no):
		assert type(parent_node) == templates.GrammarRuleApplier
		assert type(node1) == templates.GrammarRuleApplier
		assert type(node2) == templates.GrammarRuleApplier
		if (parent_node.struct_var_name, production_no) not in self.commutative_processed:
			text = '(=> (= '
			text += parent_node.struct_var_name + ' ' + str(production_no) + ') '
			text += '(<= '
			text += node1.struct_var_name + ' ' + node2.struct_var_name
			text += '))'
			text = self.assertify(text)
			# Alternative (simpler) form
			# text = '(assert (<= '
			# text += node1.struct_var_name + ' ' + node2.struct_var_name
			# text += '))'
			self.commutative_processed.add((parent_node.struct_var_name, production_no))
			self.stack_var_declarations.append(text)

	def push_all_var_declarations(self, node):
		if type(node) == templates.GrammarRuleApplier:
			self.push_struct_var_declaration(node.struct_var_name, 'Int', node.max_struct_var_value())
		else:
			for v in node.vars:
				self.push_const_var_declaration(v, node.vars[v])
		for a in node.args:
			self.push_all_var_declarations(a)

	def push_all_hole_funs(self, node):
		"""Pushes code of functions for every grammar rule applier found during walk through a grammar tree."""
		if type(node) == templates.GrammarRuleApplier:
			self.create_and_push_single_fun(node)
		for a in node.args:
			self.push_all_hole_funs(a)

	def create_and_push_single_fun(self, gra):
		"""Creates function for a given node."""
		assert type(gra) == templates.GrammarRuleApplier
		if gra.function_name not in self.declared_fun_names: # Safety check for reused functions.
			if len(gra.args) > 0:
				f = self.get_fun_code(gra)
				self.stack_holes_functions.append(f)
				self.declared_fun_names.add(gra.function_name)

	def get_fun_code(self, gra):
		text  = self.get_fun_header(gra) + '\n'
		text += self.get_fun_body(gra) + '\n'
		text += ')'
		return text

	def get_fun_header(self, node):
		"""Produces header of the hole function. Example: "(define-fun hole ((a Int)(b Int)(c Int)) Bool". Ending parenthesis is omitted because other method must first generate body of this hole function.

		:return: Function header in SMTLIB format.
		"""
		assert isinstance(node, templates.GrammarRuleApplier)
		hole = node.hole_decl
		variables = hole.get_used_var_names()
		res = '(define-fun ' + node.function_name + ' '
		res += '('
		for v in sorted(variables.keys()):
			res += '(' + v + ' ' + variables[v] + ')'
		res += ') '
		res += node.rule.sort
		return res

	def get_fun_body(self, node):
		"""Produces a body of the hole function consisting of several ite instructions.

		:return: Function body in SMTLIB format.
		"""
		assert type(node) == templates.GrammarRuleApplier
		if len(node.args) == 0:
			raise Exception('Empty grammar rule applier - function cannot be created!')

		struct_var = node.struct_var_name
		def helper(i):
			gn = node.args[i]
			if i == len(node.args) - 1:
				return '    ' * (i + 1) + gn.get_text()
			text = '    ' * (i + 1) + '(ite (= ' + struct_var + ' ' + str(i) + ')\n'
			text += '    ' * (i + 2) + gn.get_text() + '\n'
			text += helper(i + 1) + ')'
			return text
		return helper(0)

	def push_struct_var_declaration(self, name, type, maxval, minval=0):
		if name not in self.declared_var_names:
			decl = SMTLIBConstraints.produce_vars_declarations({name: type})
			text = self.assertify('(<= ' + str(minval) + ' ' + name + ')') + \
			       self.assertify('(<= ' + name + ' ' + str(maxval) + ')')
			decl.append(text)
			self.declared_var_names.add(name)
			self.stack_var_declarations.extend(decl)

	def push_const_var_declaration(self, name, type):
		if name not in self.declared_var_names:
			decl = SMTLIBConstraints.produce_vars_declarations({name: type})
			self.declared_var_names.add(name)
			self.stack_var_declarations.extend(decl)

	def assertify(self, text):
		"""Wraps constraint in a assert clause."""
		if self.name_struct_assertions:
			return '(assert (! ' + text + ' :named ' + self.next_assert_name() + '))'
		else:
			return '(assert ' + text + ')'

	def next_assert_name(self):
		res = 'Struct' + str(self.num_asserts)
		self.num_asserts += 1
		return res