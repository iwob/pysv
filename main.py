#!/usr/bin/env python
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
    if not env.verify and not env.synthesize and not env.example:
        print("Choose the task with --verify or --synthesize!")
        exit()
    if env.synth_min_passed_tests is not None and env.synth_mode != 'max':
        print("--synth_min_passed_tests option requires the --synth_mode to be set to 'max'!")
        exit()


if __name__ == "__main__":
    # Examples:
    # ./main.py --verify --pre "x>=0" --post "res>0" --program "res=y+x+5" --local_vars res:Int --input_vars y:Int x:Int
    # ./main.py --example --pre "x>=0" --post "res>0" --program "res=y+x+5" --local_vars res:Int --input_vars y:Int x:Int


    env = utils.Options()
    validate_options(env)
    runner.run_from_options(env)
