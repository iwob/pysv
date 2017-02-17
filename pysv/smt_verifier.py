from pysv.smtlib.ver import VerificationConstr
from pysv.smtlib.ver import FindExampleConstr
from pysv import smt_common
from pysv import solvers
from pysv import utils



def _verify_universal(smtlib_constr, code, code_pre, code_post, program_vars, env):
	ib_smt2, pre_smt2, post_smt2 = smt_common.get_code_in_smt2(code, code_pre, code_post, program_vars, env)
	script = smtlib_constr.produce_script_verification(ib_smt2, pre_smt2, post_smt2, program_vars)
	smt_common.write_script_to_file(script, env)
	if env.only_script:
		print(script)
		return None
	else:
		utils.logger.info('\n\n******** SCRIPT ********:\n' + script)
		# Solving constraints
		res = solvers.run_solver(script, env)
		return VerificationResult(res, code, program_vars, env)



def verify(code, code_pre, code_post, program_vars, env, assertions = None):
	"""This function utilizes external solver and runs it for the generated SMT-LIB 2.0 script containing
	constraints. Program is checked for correctness with respect to delivered pre- and
	post-conditions.

	:param code: (str) Source code (in arbitrary language) of the program.
	:param code_pre: (str) Source code (in arbitrary language) of the expression representing all *pre-conditions*.
	:param code_post: (str) Source code (in arbitrary language) of the expression representing all *post-conditions*.
	:param program_vars: (ProgramVars) Information about variables and their types.
	:param env: (Options) Verification options.
	:param assertions: (list[str]) Optional list of SMT-LIB 2.0 commands, which will be appended at the end of the script.
	:return: (SolverResult) Interpreted result of the solver.
	"""
	if assertions is None:
		assertions = env.assertions
	smtlib_constr = VerificationConstr(env, assertions)
	return _verify_universal(smtlib_constr, code, code_pre, code_post, program_vars, env)



def find_example(code, code_pre, code_post, program_vars, env, assertions = None):
	"""This function utilizes external solver and runs it for the generated SMT-LIB 2.0 script containing
	constraints. Solver will search for an example of correct working of the program with respect to delivered
	pre- and post-conditions.

	:param code: (str) Source code (in arbitrary language) of the program.
	:param code_pre: (str) Source code (in arbitrary language) of the expression representing all *pre-conditions*.
	:param code_post: (str) Source code (in arbitrary language) of the expression representing all *post-conditions*.
	:param program_vars: (ProgramVars) Information about variables and their types.
	:param env: (Options) Verification options.
	:param assertions: (list[str]) Optional list of SMT-LIB 2.0 commands, which will be appended at the end of the script.
	:return: (SolverResult) Interpreted result of the solver.
	"""
	if assertions is None:
		assertions = env.assertions
	smtlib_constr = FindExampleConstr(env, assertions)
	return _verify_universal(smtlib_constr, code, code_pre, code_post, program_vars, env)






class VerificationResult(solvers.SolverResult):
	"""VerificationResult contains apart from normal solver result also certain information typical for the verification scenario, e.g. witness (part of the model for input variables, which allows to reproduce erroneous behavior).
	"""
	def __init__(self, solver_result, original_code, program_vars, env):
		solvers.SolverResult.__init__(self, solver_result, env)
		self.original_code = original_code
		if self.decision == solvers.SAT:
			self.witness = {k:self.model[k] for k in self.model if k in program_vars.input_vars}
		else:
			self.witness = {}