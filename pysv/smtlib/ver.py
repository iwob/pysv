from pysv.smtlib.common import *
from pysv import symb_logic


class VerificationConstr(SMTLIBConstraints):

    def __init__(self, env, assertions = None):
        SMTLIBConstraints.__init__(self, env, assertions)
        self.num_postcond = 0
        self.negate_post = True


    def produce_script_verification(self, ib, pre, post, program_vars):
        """Produces a complete SMT-LIB 2.0 script ready to be used as an input to the solver. This script will contain constraints for solving a **verification** task.

        :param ib: (ProgramSmt2) Program in SMT2 representation.
        :param pre: (ProgramSmt2) Precondition in SMT2 representation.
        :param post: (ProgramSmt2) Postcondition in SMT2 representation.
        :param program_vars: (ProgramVars) Information about identifiers and types of all variables in the program.
        :return: (str) Complete text of SMT-LIB 2.0 script realizing verification task.
        """
        self.reset_state()
        decls = self.produce_vars_declarations(program_vars.all())

        text  = self.text_introduction() + '\n\n'
        text += self.list_to_text(decls, 'Normal variables') + '\n\n'
        text += self.text_verification_formula(ib, pre, post) + '\n\n'
        text += self.text_additional_assertions() + '\n'
        if self.env.ver_mode != utils.Options.MODE_NORMAL:
            text += self.text_postcond_opt()
        text += self.text_epilog()
        return text


    def text_verification_formula(self, ib, pre, post):
        if self.env.ver_flat_formula:
            return self.get_flat_verification_formula(ib, pre, post)
        else:
            return self.get_std_verification_formula(ib, pre, post)


    def get_std_verification_formula(self, ib, pre, post):
        """Returns asserted verification formula in the standard form: not (PRE and PROGRAM => POST).

        :param ib: (ProgramSmt2) program in SMT2 representation.
        :param pre: (ProgramSmt2) precondition in SMT2 representation.
        :param post: (ProgramSmt2) postcondition in SMT2 representation.
        :return: (str) Final text of the standard verification formula.
        """
        PRE = pre.src
        PROGRAM = utils.conjunct_constrs_smt2(ib.constr)
        POST = self.get_postcond_core(post)
        text = self.get_std_verification_formula_text(PRE, PROGRAM, POST)
        text = SMTLIBConstraints.wrap_in_let_declarations(text, ib.let_declarations)
        return self.assertify_ver_formula(text)


    def get_std_verification_formula_text(self, PRE, PROGRAM, POST):
        """Returns verification formula in the general form: (not (=> (and PRE PPROGRAM) POST)).

        :param PRE: (str) Text of preconditions.
        :param PROGRAM: (str) Text of a body of a program.
        :param POST: (str) Text of postconditions.
        :return: (str) Verification formula.
        """
        text = '(=>\n' + \
                    '\t(and\n' + \
                    '\t\t;PRECONDITION\n' + \
                    '\t\t' + PRE + '\n' + \
                    '\t\t;PROGRAM:\n' + \
                    '\t\t' + PROGRAM + '\n' + \
                    '\t)\n' + \
                    '\t;POSTCONDITION:\n' + \
                    '\t' + POST + '\n' + \
                ')'
        if self.negate_post:
            return '(not {0})'.format(text)
        else:
            return text


    def get_flat_verification_formula(self, ib, pre, post):
        """Returns asserted verification formula. This formula spans multiple assertions:
         assert(PRE); assert(x) for x in PROGRAM; assert(not(POST)). In other words,
         standard implication-based verification formula was transformed into a set of formulas
         connected by conjunctions.

        :param ib: (ProgramSmt2) program in SMT2 representation.
        :param pre: (ProgramSmt2) precondition in SMT2 representation.
        :param post: (ProgramSmt2) postcondition in SMT2 representation.
        :return: (str) Final text of the standard verification formula.
        """
        PRE = self.assertify(pre.src)
        PROGRAM = self.get_text_program_assertions(ib.constr)
        POST = self.get_postcond_whole(post)

        text = '; PRECONDITION\n'
        text += PRE + '\n\n'
        text += '; PROGRAM\n'
        text += PROGRAM + '\n'
        text += '; POSTCONDITION\n'
        text += self.assertify(POST)
        return text


    def get_postcond_core(self, post):
        """Returns SMT-LIB 2.0 code of postcondition. Certain transformations may me done as specified by options provided by the user."""
        if self.env.post_in_cnf:
            t = symb_logic.canonical_form(post.get_tree())
            t = symb_logic.compute_cnf(t)
            if self.env.ver_annotate_post:
                self.num_postcond = 0
                self.annotate_cnf_tree(t)
            return t.str_smt2()
        else:
            return post.src


    def get_postcond_whole(self, post):
        """Returns not asserted postcondition formula which is negated."""
        if self.negate_post:
            return '(not ' + self.get_postcond_core(post) + ')'
        else:
            return self.get_postcond_core(post)



    def annotate_cnf_tree(self, node):
        if node.name == 'and':
            for a in node.args:
                self.annotate_cnf_tree(a)
        else:
            self.annotate_node(node)


    def annotate_node(self, node):
        node.info[':named'] = 'post_' + str(self.num_postcond)
        self.num_postcond += 1


    def text_postcond_opt(self):
        ctype = 'Int' # this type is required for Z3's minimize and maximize function.
        text = ''
        for i in range(0, self.num_postcond):
            text += '(define-fun post_i{0} () {1} (ite post_{0} 1 0))\n'.format(str(i), ctype)
            # text += '(= post_i{0} (ite post_{0} 1 0)\n'.format(str(i))
        text += '(declare-fun post_sum () {0})\n'.format(ctype)
        text += '(assert (= post_sum (+'
        for i in range(0, self.num_postcond):
            text += ' post_i{0}'.format(str(i))
        text += ')))\n\n'
        if self.env.ver_mode == utils.Options.MODE_MIN:
            text += '(minimize post_sum)\n'
        elif self.env.ver_mode == utils.Options.MODE_MAX:
            text += '(maximize post_sum)\n'
        return text


    def assertify_ver_formula(self, body_text):
        return self.assertify(body_text, 'VER_FORMULA')


    def get_text_program_assertions(self, program_constr):
        text = ''
        for c in program_constr:
            text += self.assertify(c) + '\n'
        return text




class FindExampleConstr(VerificationConstr):
    def __init__(self, env, assertions = None):
        VerificationConstr.__init__(self, env, assertions)
        self.negate_post = False