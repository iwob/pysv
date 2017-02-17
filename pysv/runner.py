from pysv import smt_verifier
from pysv import smt_synthesis
from pysv import contract



def get_program_vars(env):
	in_vars = {vt.split(":")[0]:vt.split(":")[1] for vt in env.input_vars}
	loc_vars = {vt.split(":")[0]:vt.split(":")[1] for vt in env.local_vars}
	return contract.ProgramVars(in_vars, loc_vars)


def run_from_options(env):
	"""Runs synthesis or verification depending on the provided options."""
	program_vars = get_program_vars(env)

	if env.verify:
		res = smt_verifier.verify(env.program, env.pre, env.post, program_vars, env)
		# Printing the result.
		print(res.str_formatted())
		if not env.silent:  # Additional commentary
			if res.decision == 'unsat':
				print('Counterexample not found! Program is correct.')
			elif res.decision == 'sat':
				print('Counterexample found! Program is not correct.')
		return res

	elif env.example:
		res = smt_verifier.find_example(env.program, env.pre, env.post, program_vars, env)
		# Printing the result.
		print(res.str_formatted())
		if not env.silent:  # Additional commentary
			if res.decision == 'unsat':
				print('Example not found! Program is incorrect for all inputs.')
			elif res.decision == 'sat':
				print('Example found! Program is correct for at least one input.')
		return res

	elif env.synthesize:
		holes = smt_synthesis.HoleDecl.many_from_str(env.synth_holes)
		if env.test_cases == "":
			res = smt_synthesis.synthesize(env.program, env.pre, env.post, program_vars, env, holes, free_vars=env.free_vars)
		else:
			test_cases = contract.TestCases.from_str(env.test_cases)
			res = smt_synthesis.synthesize_tc(test_cases, env.program, env.pre, env.post, program_vars, env, holes, free_vars=env.free_vars)
		# Printing the result.
		print(res.str_formatted())
		return res

	else:
		print("Task was not specified! Use either --verify or --synthesize.")
		exit()