from __future__ import print_function
import sys
from subprocess import Popen, PIPE, STDOUT
from signal import signal, SIGPIPE, SIG_DFL
from pysv import utils
signal(SIGPIPE,SIG_DFL)

SAT = 'sat'
UNSAT = 'unsat'
UNKNOWN = 'unknown'
TIMEOUT = 'timeout'


class Solver(object):
    """Handles interaction with the solver. Supports both interactive mode and single script run."""

    Z3 = 'z3'
    CVC4 = 'cvc4'
    MathSAT = 'mathsat'
    OTHER = 'other'
    supported_solvers = [Z3, CVC4, MathSAT, OTHER]

    def __init__(self, env):
        self.env = env
        self.solver_type = env.solver
        self.solver_interactive_mode = env.solver_interactive_mode

    def apply(self, script, other_params=None):
        """Runs a solver and passes the script on the standard input.

        :param script: A script in SMT-LIB 2.0 language.
        :param other_params: Optional parameters for the solver.
        :return: SolverResult containing merged output from stdout and stderr.
        """
        if other_params is None:
            other_params = []
        try:
            if self.solver_interactive_mode:
                out_data, err_data = self.run_solver_interactive(script, other_params)
            else:
                out_data, err_data = self.run_solver_script(script, other_params)
        except OSError as e:
            print("Solver binaries not found! Check your solvers_bin folder or --solver_path argument.", file=sys.stderr)
            raise e
        except Exception as e:
            print("Solver could not be executed or critical error occurred!", file=sys.stderr)
            raise e
        else: # no exception.
            text = self.prepare_apply_output(out_data, err_data)
            return SolverResult(text, self.env, script, text_errors=err_data)


    def run_solver_interactive(self, script, other_params):
        script += '\n'  # To avoid situation that lack of \n at the end makes solver run indefinitely.
        cmd_strings = self.get_cmd_strings(other_params)
        p = Popen(cmd_strings, stdout=PIPE, stdin=PIPE, stderr=STDOUT, universal_newlines=True, bufsize=-1)

        # Asserting all constraints and reading output.
        p.stdin.write(script)
        p.stdin.flush()

        auxiliary_output = ''

        # Reading auxiliary outputs and satisfiability decision.
        line = p.stdout.readline()
        decisions = ['sat', 'unsat', 'unknown']
        solver_abort = False
        i = 0
        while line.rstrip() not in decisions:
            if line == '':
                if p.poll() is not None:
                    solver_abort = True # This will be reached if solver process is killed or it exceeds time limit.
                    break
                i += 1
            else:
                i = 0
            if i >= 100:
                r = p.poll()
                raise Exception("Only empty strings read from the solver's output! Check, if solver process ended without any errors. Solver reply to poll function: " + str(r))
            auxiliary_output += line
            line = p.stdout.readline()
            if line[0:6] == '(error':
                raise Exception("Solver returned error! '" + line.rstrip() +"'")

        if solver_abort:
            return 'timeout\n', ''
        else:
            decision = line
            out = ''
            err = ''
            if decision.rstrip() == 'sat':
                # o2, e2 = self.p.communicate(input='(get-model)')
                code = '(get-model)\n'
                if self.env.produce_assignments:
                    code += '(get-assignment)\n'
                code += '\n(exit)\n'
                p.stdin.write(code)
                p.stdin.flush()
                out = p.stdout.read()

            elif decision.rstrip() == 'unsat':
                if self.env.produce_unsat_core:
                    # o2, e2 = self.p.communicate(input='(get-unsat-core)')
                    p.stdin.write('(get-unsat-core)\n(exit)\n')
                    p.stdin.flush()
                    out = p.stdout.read()

            p.terminate()
            return decision + out, auxiliary_output + err


    def run_solver_script(self, script, other_params):
        cmd_strings = self.get_cmd_strings(other_params)
        p = Popen(cmd_strings, stdout=PIPE, stdin=PIPE, stderr=PIPE, universal_newlines=True, bufsize=-1)
        return p.communicate(input=script)  # a tuple (stdout, stderr) is returned

    def get_cmd_strings(self, other_params):
        raise Exception('Function get_cmd_strings is not implemented!')

    def prepare_apply_output(self, out_data, err_data):
        res = out_data
        if err_data != '':
            res += '\n' + err_data
        return res

    @staticmethod
    def get_solver_specific_args(solver_type, env, other_args=None):
        if other_args is None:
            other_args = []
        if solver_type == Solver.Z3:
            res = ['-smt2', '-in']
        elif solver_type == Solver.CVC4:
            res = ['--lang', 'smt']
        elif solver_type == Solver.MathSAT:
            res = ['-input=smt2', '-model_generation=TRUE'] #'-model'
        else:
            res = []
        res.extend(other_args)
        return res

    @staticmethod
    def get_solver_specific_bin_name(solver_type):
        if solver_type == Solver.Z3:
            return 'z3'
        elif solver_type == Solver.CVC4:
            return 'cvc4'
        elif solver_type == Solver.MathSAT:
            return 'mathsat'
        else:
            return None



class SolverBinaries(Solver):

    def __init__(self, env, solver_name=None, args=None):
        if args is None:
            args = []
        if solver_name is None:
            solver_name = Solver.get_solver_specific_bin_name(env.solver)
        self.args = args
        # self.solver_name = solver_name
        if env.solver_path is not None:
            self.solver_name = env.solver_path
        else:
            import os
            BASE_DIR = os.path.abspath(os.path.join(os.path.dirname( __file__ ), '..', 'solvers_bin'))
            self.solver_name = BASE_DIR + os.sep + solver_name
            # print('Solver path: ' + self.solver_name)
        Solver.__init__(self, env)

    def get_cmd_strings(self, other_params):
        cmd = [self.solver_name]
        cmd.extend(Solver.get_solver_specific_args(self.solver_type, self.env, self.args))
        cmd.extend(other_params)
        return cmd





def run_solver(script, env):
    """Runs the SMT-LIB 2.0 script using specified solver."""
    if env.solver in Solver.supported_solvers:
        return SolverBinaries(env).apply(script)
    else:
        raise Exception('The chosen solver is not supported! Supported: {0}.'.format(Solver.supported_solvers))





class SolverResult(object):
    """Processed synthesis result of the solver.

    Attributes:
    -----------
    text : string
        Raw output of the solver.
    decision : string
        Solver decision: sat, unsat, unsupported or unknown.
    model : dict[string,string]
        Dictionary containing values of all variables present in the model.
    """

    def __init__(self, result, env, script=None, text_errors=""):
        self.env = env
        if isinstance(result, SolverResult):
            self.text = result.text
            self.text_errors = result.text_errors
            self.decision = result.decision
            self.model = result.model.copy()
            self.unsat_core = result.unsat_core[:]
            self.assignments = result.assignments.copy()
            self.script = result.script
            self.was_any_error = result.was_any_error
        else:
            self.text = result
            self.text_errors = text_errors
            self.was_any_error = True if text_errors is not None and text_errors != "" else False
            utils.logger.debug('SolverResult.text = ' + self.text)
            self.decision = SolverResult.get_decision(result)
            self.model = {}
            self.assignments = {}
            self.unsat_core = []
            self.script = script
            if self.decision == 'sat':
                self.model = SolverResult.get_model_values(result)
                if env.produce_assignments:
                    self.assignments = SolverResult.get_assignments(result, env.solver_interactive_mode)
            if self.decision == 'unsat' and env.produce_unsat_core:
                self.unsat_core = SolverResult.get_unsat_core(result, env.solver_interactive_mode, env.produce_assignments)


    def __getitem__(self, var_name):
        return self.model[var_name]

    def __str__(self):
        return self.text

    def str_formatted(self):
        """Returns string in the format declared by the output_data option."""
        if not self.env.silent:
            res  = '----------------------------------------------\n'
            res += 'SOLVER RESULT\n'
            res += '----------------------------------------------\n'
        else:
            res = ''
        for s in self.env.output_data:
            if s == 'raw':
                res += str(self.text) + '\n'
            elif s == 'decision':
                res += str(self.decision) + '\n'
            elif s == 'model':
                res += str(self.model) + '\n'
            elif s == 'unsat_core':
                res += str(self.unsat_core) + '\n'
            elif s == 'assignments':
                res += str(self.assignments) + '\n'
            elif s == 'final_code':
                if not self.env.silent:
                    res += '--------------------------\n'
                    res += 'SYNTHESIZED PYTHON CODE:'
                res += str(self.final_code) + '\n'  # final_code will work only for SynthesisResult subclass.
            elif s == "holes_content":
                res += str(self.holes_content)  # final_code will work only for SynthesisResult subclass.
        return res

    @staticmethod
    def get_decision(text):
        """Returns solver decision: sat, unsat, unsupported or unknown."""
        if text == '':
            return ''
        else:
            return text.split()[0]

    @staticmethod
    def get_model_values(text):
        """Returns dictionary with values assigned to variables."""
        words = utils.str_to_wlist(text)
        if len(words) <= 1:
            raise Exception('Trying to get model while presumably only check-sat was invoked!')

        start = 1
        prefix = words[start] + words[start + 1] # On the i=0 always is a decision.
        if prefix == '(objectives':
            start = utils.index_of_closing_parenthesis(words, start) + 1
            prefix = words[start] + words[start + 1]

        if prefix == '(error' or prefix not in ('(model', '(('):
            return {}
        elif prefix == '(model':
            return SolverResult.get_model_explicit(words[start:])
        elif prefix == '((':
            return SolverResult.get_model_simplified(words[start:])

    @staticmethod
    def get_model_explicit(words):
        model_values = {}
        i = 2
        while i < len(words):
            if words[i] == 'define-fun':
                name = words[i + 1]
                # Usually i+2 and i+3 contains parenthesis, but in some scenarios there may be some values
                # in between. They are ignored here.
                i = utils.index_of_closing_parenthesis(words, i + 2)
                # i+1 is a type of the function
                if words[i + 2] == '(':
                    j = utils.index_of_closing_parenthesis(words, i + 2)
                    value = ' '.join(words[i + 2:j + 1])
                    i = j + 1  # j+1 is closing parenthesis of define-fun
                else:
                    value = words[i + 2]
                    i += 3  # i+3 is closing parenthesis of define-fun
                model_values[name] = value
                assert words[i] == ')'  # i should point to the last parenthesis of define-fun
            i += 1
        return model_values

    @staticmethod
    def get_model_simplified(words):
        # raise Exception('Loading model in the simplified form is not supported yet!')
        model_values = {}
        i = 1
        while i < len(words):
            if words[i] == '(':
                name = words[i + 1]
                # i+1 is a type of the function
                if words[i + 2] == '(':
                    j = utils.index_of_closing_parenthesis(words, i + 2)
                    value = ' '.join(words[i + 2:j + 1])
                    i = j + 1  # j+1 is closing parenthesis
                else:
                    value = words[i + 2]
                    i += 3  # i+3 is closing parenthesis
                model_values[name] = value
                assert words[i] == ')'  # i should point to the last parenthesis of value definition
            i += 1
        return model_values

    @staticmethod
    def get_unsat_core(text, interactive_mode, produce_assignments):
        """Returns unsat-core or empty list if it was not obtainable (e.g. decision was sat)."""
        unsat_core = []
        words = utils.str_to_wlist(text)

        # skip model - NOTE: in the interactive mode there is no need to skip the model
        if not interactive_mode:
            j = utils.index_of_closing_parenthesis(words, 1) + 1 # omit model
            if produce_assignments:
                x = words[j:]
                j = utils.index_of_closing_parenthesis(words, j) + 1 # omit assignments
                x = words[j:]
            if j+1 >= len(words):
                return []
        else:
            j = 1

        prefix = words[j] + words[j+1]
        if prefix == '(error':
            return []
        else:
            while j < len(words):
                if words[j] == '(':
                    pass
                elif words[j] == ')':
                    break
                else:
                    unsat_core.append(words[j])
                j += 1
        return unsat_core

    @staticmethod
    def get_assignments(text, interactive_mode):
        """Returns dictionary of assignments if decision was sat."""
        words = utils.str_to_wlist(text)

        j = 1 # On the j=0 is a decision.
        prefix = words[j] + words[j + 1]
        if prefix == '(objectives':
            j = utils.index_of_closing_parenthesis(words, j) + 1
            prefix = words[j] + words[j + 1]
        if prefix == '(model' or prefix == '((': # skip model - assignments are printed after it.
            j = utils.index_of_closing_parenthesis(words, j) + 1
            prefix = words[j] + words[j + 1]

        if j + 1 >= len(words):
            return []
        elif prefix == '(error':
            return {}
        else:
            return utils.wlist_to_dict_parenthesis(words[j:])