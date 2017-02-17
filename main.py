from pysv import utils
from pysv import runner



def validate_options(env):
	if env.pre is None:
		print("Precondition was not specified! Use: --pre PRE.")
		exit()
	if env.program is None:
		print("Precondition was not specified! Use: --program PROGRAM.")
		exit()
	if env.post is None:
		print("Postcondition was not specified! Use: --post POST.")
		exit()
	if not env.verify and not env.synthesize:
		print("Choose the task with --verify or --synthesize!")
		exit()
	if env.synth_min_passed_tests is not None and env.synth_mode != 'max':
		print("--synth_min_passed_tests option requires the --synth_mode to be set to 'max'!")
		exit()


if __name__ == "__main__":
	# Example usage: python main.py --verify --pre "True" --post "y==5" --program "x=5;y=x" --local_vars x:Int  --input_vars y:Int
	env = utils.Options()
	validate_options(env)
	runner.run_from_options(env)