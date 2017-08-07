import logging
import sys
import argparse

logging.basicConfig(level=logging.INFO)
logger = logging.getLogger(__name__)


def index_of_closing_parenthesis(words, start, left_enc ='(', right_enc =')'):
    """Returns index of the opening parenthesis of this parenthesis.."""
    num_opened = 1
    for i in range(start + 1, len(words)):
        if words[i] == left_enc:
            num_opened += 1
        elif words[i] == right_enc:
            num_opened -= 1

        if num_opened == 0:
            return i
    return -1


def index_of_opening_parenthesis(words, start, left_enc ='(', right_enc =')'):
    """Returns index of the closing parenthesis of this parenthesis."""
    num_opened = -1
    i = start-1
    while i >= 0:
        if words[i] == left_enc:
            num_opened += 1
        elif words[i] == right_enc:
            num_opened -= 1

        if num_opened == 0:
            return i
        i -= 1
    return -1


def index_closest_left(words, start, what):
    """Returns index of the closest specified element to the left of the starting position or -1 if no such element was present."""
    i = start - 1
    while i >= 0:
        if words[i] == what:
            return i
        i -= 1
    return -1


def index_closest_right(words, start, what):
    """Returns index of the closest specified element to the right of the starting position or -1 if no such element was present."""
    i = start + 1
    while i < len(words):
        if words[i] == what:
            return i
        i += 1
    return -1


def parenthesis_enclosure(words, start, left_enc = '(', right_enc = ')'):
    """For a given position in the list finds left and right parenthesis (there is also an option to specify arbitrary symbols) and returns a list containing those parenthesis and all elements between them."""
    opened = index_of_opening_parenthesis(words, start, left_enc, right_enc)
    if opened == -1:
        return []
    ended = index_of_closing_parenthesis(words, opened, left_enc, right_enc)
    if ended == -1:
        return []
    return words[opened:ended+1]


def assertify(text):
    """Wraps text in the (assert )."""
    return '(assert ' + text + ')'


LANG_PYTHON = 'python'
LANG_SMT2 = 'smt2'


def alternative(seq, lang = LANG_PYTHON):
    """Produces a formula connecting all elements from the provided list with an alternative ('or')."""
    if lang == LANG_PYTHON:
        return merge_elements_by(seq, ' or ')
    elif lang == LANG_SMT2:
        return _join_smt2(seq, 'or')
    else:
        raise Exception("'{0}': Not recognized language!".format(lang))


def conjunction(seq, lang = LANG_PYTHON):
    """Produces a formula connecting all elements from the provided list with a conjunction ('and')."""
    if lang == LANG_PYTHON:
        return merge_elements_by(seq, ' and ')
    elif lang == LANG_SMT2:
        return _join_smt2(seq, 'and')
    else:
        raise Exception("'{0}': Not recognized language!".format(lang))


def conjunct_constrs_smt2(constr_list):
    """Merges constraints list using SMT-LIB 2.0 conjunction operator (and). If the list is empty, 'true' is returned."""
    noncomments = [c for c in constr_list if c.lstrip()[0] != ';']
    if len(noncomments) == 0:
        return 'true'
    elif len(noncomments) == 1:
        return noncomments[0]
    else:
        return _join_smt2(constr_list, 'and')


def _join_smt2(seq, conn):
    """Produces a SMT-LIB 2.0 formula containing all elements of the sequence merged by a provided connective."""
    if len(seq) == 0:
        return ''
    elif len(seq) == 1:
        return seq[0]
    else:
        return '({0} {1})'.format(conn, ' '.join(seq))


def merge_elements_by(seq, conn, wrapped_in_par = True):
    """Produces a string containing all elements of the sequence merged by a provided connective."""
    if len(seq) == 0:
        return ''
    elif len(seq) == 1:
        return seq[0]
    else:
        sf = '({0})' if wrapped_in_par else '{0}'
        return conn.join(sf.format(el) for el in seq)


def str_to_wlist(s, par_open = '(', par_close = ')'):
    """Converts a string to a list of words, where words are delimited by whitespaces."""
    return s.replace(par_open, ' '+par_open+' ').replace(par_close, ' '+par_close+' ').split()


def str_to_dict_parenthesis(s):
    """Converts a string in the format: '((n1 v1)...(nk vk))' to a dictionary {n1:v1, ..., nk:vk}."""
    return wlist_to_dict_parenthesis(str_to_wlist(s))


def wlist_to_dict_parenthesis(words):
    """Converts a list of strings in the format: ['(', '(', 'n1', 'v1', ')', ..., '(', 'nk', 'vk', ')', ')'] to a dictionary {n1:v1, ..., nk:vk}."""
    res = {}
    i = 1
    while True:
        if words[i] == '(':
            res[words[i+1]] = words[i+2]
            i += 4
        else:
            break
    return res



class Options(object):
    """Options contains all settings which are used within the framework."""
    MODE_NORMAL = 'normal'
    MODE_MIN = 'min'
    MODE_MAX = 'max'
    PYTHON = 'python'
    SMT2 = 'smt2'

    def __init__(self, opts = None, merge_with_vargs = True):
        opts = self._preprocess_opts(opts)
        if merge_with_vargs:
            opts.extend(sys.argv[1:])
        args = self._parse_options(opts)
        self.options = vars(args)

        if self.silent:
            logger.disabled = True

    def __str__(self):
        return str(self.options)


    def _parse_options(self, opts):
        parser = argparse.ArgumentParser(description="Synthesize or verify Python programs.", add_help=True)

        parser.add_argument("--assertions", type=str, nargs='*', default=[],
                            help="List of additional assertions to be inserted at the end of the script.")
        parser.add_argument("--allow_commutative_constr", type=int, choices=[0, 1], default=False)
        parser.add_argument("--assignments_as_lets", type=int, choices=[0, 1], default=False)
        parser.add_argument("--lang", type=str, choices=["python", "smt2"], default="python",
                            help="Language, in which written are precondition, program and postcondition. For languages different than SMT-LIB 2.0 (smt2), conversion to correct semantic-preserving SMT-LIB 2.0 constraints is applied before running the solver. If SMT-LIB 2.0 code is provided as input, then it is assummed that it is in the form ready to be used in the final script (certain other options still may modify this code).  (default: python)")
        parser.add_argument("--pre", type=str,
                            help="Precondition of the program.")
        parser.add_argument("--program", type=str,
                            help="Source code of the program.")
        parser.add_argument("--post", type=str,
                            help="Postcondition of the program.")
        parser.add_argument("--post_in_cnf", type=int, choices=[0, 1], default=False,
                            help="If set to 1, postcondition will be transformed to CNF form.")
        parser.add_argument("--input_vars", type=str, nargs='*', default=[],
                            help="List of input variables of the program and their types, in which single element is provided in the form: name:type. (default: [])")
        parser.add_argument("--local_vars", type=str, nargs='*', default=[],
                            help="List of local variables present in the program and their types, in which single element is provided in the form: name:type. (default: [])")
        parser.add_argument("--free_vars", type=str, nargs='*', default=[],
                            help="List of free variables present in the programs, provided as only names. Value of those variables will be determined by solver during verification or synthesis. Free variables should be also properly declared as local variables. (default: [])")
        parser.add_argument("--logic", type=str, default="NIA")
        parser.add_argument("--name_all_assertions", type=int, choices=[0, 1], default=True)
        parser.add_argument("--name_struct_assertions", type=int, choices=[0, 1], default=False)
        parser.add_argument("--only_script", action="store_true",
                            help="SMT-LIB 2.0 script will be produced and printed on the standard output, but solver will not be executed. The script will be printed even if silent mode was set.")
        parser.add_argument("--produce_proofs", type=int, choices=[0, 1], default=False,
                            help="If true, then solver's utility to produce unsatisfiability proofs will be used if decision was unsat. Not all solvers support this functionality. (default: 0)")
        parser.add_argument("--produce_unsat_core", type=int, choices=[0, 1], default=False,
                            help="If true, then solver's utility to produce unsatisfiable core of named top-level variables will be used if decision was unsat. Not all solvers support this functionality. (default: 1)")
        parser.add_argument("--produce_assignments", type=int, choices=[0, 1], default=False,
                            help="If true, then solver's utility to return valuations of named variables will be used. Not all solvers support this functionality. (default: 0)")
        parser.add_argument("--seed", type=int,
                            help="Random seed which will be passed to solver and used within the framework.")
        parser.add_argument("--show_comments", type=int, choices=[0, 1], default=False)
        parser.add_argument("--silent", type=int, choices=[0, 1], default=False,
                            help="Silent mode.")
        parser.add_argument("--solver", choices=["z3", "cvc4", "mathsat", "other"], type=str, default="z3",
                            help="Specifies SMT solver to be used. By default, binaries of the selected solver are looked for in the solvers_bin directory, but you can also pass a path to them with --solver_path argument. Apart from that, this parameter sets some solver-specific parameters which will be passed to the selected SMT solver. (default: z3)")
        parser.add_argument("--solver_interactive_mode", type=int, choices=[0, 1], default=True,
                            help="In the interactive mode, application sends a set of constraints as an input to the solver, waits for the sat/unsat decision, and then asks for decision-specific data (e.g. model, unsat-core). In 'normal' mode, a script is sent once and solver's output is read only once, which means that solver is queried for all decision-specific data regardless of it's actual response. (default: 1)" )
        parser.add_argument("--solver_path", type=str,
                            help="Path to executable binary of the SMT solver.")
        parser.add_argument("--ssa_enabled", type=int, choices=[0, 1], default=True,
                            help="If true, then before running the solver program will be transformed to the SSA form. SSA form of a program generally is necessary for SMT constraints to be correct. Disable only if you know that your program already is in the SSA form (e.g. it is an SMT-LIB expression returning certain value) to speed up production of the script.")
        parser.add_argument("--script_prolog", type=str, default=None,
                            help="Text to be added to the SMT-LIB 2.0 script before any declaration (but after set-options).")
        parser.add_argument("--script_epilog", type=str, default=None,
                            help="Text to be added to the SMT-LIB 2.0 script after all constraints (but before check-sat).")
        parser.add_argument("--solver_timeout", type=int, default=None,
                            help="Time in miliseconds after which solver will abort search for a solution. In such a case a decision will be 'timeout'.")
        parser.add_argument("--save_script_to_file", type=int, default=False,
                            help="If set to true, then last executed script will be saved to 'script.smt2'.")
        parser.add_argument("--test_cases", type=str, default="",
                            help="Test cases from which will be derived appropriate postcondition.")
        parser.add_argument("--output_data", type=str, nargs='*', choices=["decision", "holes_content", "raw", "model", "unsat_core", "assignments", "final_code"], default=["raw"],
                            help="Determines the way in which solver's output will be printed after computations are finished. Elements are printed according to the provided sequence.")
        vs_group = parser.add_mutually_exclusive_group()
        vs_group.add_argument("--verify", action="store_true")
        vs_group.add_argument("--example", action="store_true")
        vs_group.add_argument("--synthesize", action="store_true")

        # Subparser for verification.
        # subparsers = parser.add_subparsers(title="Module",
        #                                    description="Chosen module decides what general task will be realized.")
        # parser_ver = subparsers.add_parser('verify',
        #                                    parents=[parser],
        #                                    help='Module used for verification.')
        v_group = parser.add_argument_group('VERIFICATION OPTIONS')
        self._add_ver_options(v_group)

        # Subparser for synthesis.
        # parser_synth = subparsers.add_parser('synthesize',
        #                                      parents=[parser],
        #                                      help='Module used for synthesis.')
        s_group = parser.add_argument_group('SYNTHESIS OPTIONS')
        self._add_synth_options(s_group)

        args = parser.parse_args(opts, namespace=self)
        # Manual checking of some dependencies.
        if self.ver_annotate_post and (self.post_in_cnf is None or not self.post_in_cnf):
            parser.error("'--ver_annotate_post 1' requires '--post_in_cnf 1'.")
        return args


    def _add_ver_options(self, group):
        group.add_argument("--ver_flat_formula", type=int, choices=[0, 1], default=True)
        group.add_argument("--ver_annotate_post", type=int, choices=[0, 1], default=False)
        group.add_argument("--ver_mode", choices=["normal", "min", "max"], default="normal")

    def _add_synth_options(self, group):
        group.add_argument("--synth_substitute_free", type=int, choices=[0, 1], default=True)
        group.add_argument("--synth_min_passed_tests", type=int, default=None,
                           help="Specifies at least how many test cases a solution to the synthesis problem must pass. This option requires the 'max' value for the --synth_mode option.")
        group.add_argument("--synth_mode", choices=["normal", "min", "max"], type=str, default="normal",
                           help="If set to value different than 'normal' then certain measure of correctness will be optimized by the solver. Such a measure may be for example number of passed test cases.")
        group.add_argument("--synth_holes", type=str, default="",
                           help="Definitions of all holes present in the program. Format: 'H0_id,H0_grammarDepth,H0_grammar;H1_id,H1_grammarDepth,H1_grammar'. grammarDepth is optional and may be omitted.")
        group.add_argument("--tc_rename_vars_in_assignments", type=bool, default=True,
                           help="If set to true, then all variables in assertions specified in the 'assertion' parameter will be duplicated and renamed for each test case.")
        group.add_argument("--tc_fitness_mode", type=str, choices=["normal", "L1"], default="normal",
                           help="Specifies, how fitness will be computed. 'normal' means a sum of passed test cases.")

    def _preprocess_opts(self, opts):
        if opts is None:
            return []
        elif type(opts) == str:
            s = opts.split()
            return self._preprocess_opts(s)
        elif type(opts) == dict:
            opts = self._flatten_dict(opts)
        def convert(x):
            if type(x) == bool:
                return "1" if x else "0"
            else:
                return str(x)
        return [convert(x) for x in opts]

    def _flatten_dict(self, opts):
        new_opts = []
        for k in opts:
            new_opts.append(k)
            if opts[k] is not None:
                new_opts.append(opts[k])
        return new_opts

    def get(self, key, default=None):
        if key not in self.options:
            return default
        else:
            return str(self.options[key])

    def get_float(self, key, default = None):
        if key not in self.options:
            return default
        else:
            return float(self.options[key])

    def get_int(self, key, default = None):
        if key not in self.options:
            return default
        else:
            return int(self.options[key])

    def get_bool(self, key, default = None):
        if key not in self.options:
            return default
        else:
            return str(self.options[key]).lower() == 'true'