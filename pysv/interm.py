from pysv import utils
from pysv.smt2 import ProgramSmt2



class ProgramInterm(object):
    """Program in the intermediary representation abstracting concrete
    programming language details. Program consists of a block of instructions."""
    def __init__(self, src):
        assert isinstance(src, InstrBlock)
        self.src = src

    def to_smt2(self, env):
        return self.src.to_smt2(env=env)

    def __str__(self):
        return str(self.src)





# -------------------------------------------------------------------------------------
#                                 INSTRUCTIONS
# -------------------------------------------------------------------------------------


class InstrBlock(object):
    def __init__(self, instrs):
        assert isinstance(instrs, list)
        self.instructions = instrs

    def append(self, instr):
        self.instructions.append(instr)

    def size(self):
        return len(self.instructions)

    def collect_variables(self):
        res = []
        for i in self.instructions:
            res.extend(i.collect_variables())
        return list(set(res))

    def collect_nodes(self):
        res = [self]
        for i in self.instructions:
            res.extend(i.collect_nodes())
        return res

    def rename_var(self, old_id, new_id):  # to be overriden in subclasses
        for i in self.instructions:
            i.rename_var(old_id, new_id)

    def equals(self, other):
        """Checks, if provided instruction block has the same structure and instructions as this one."""
        if not isinstance(other, InstrBlock):
            return False
        n = len(self.instructions)
        m = len(other.instructions)
        if n != m:
            return False
        else:
            for i in range(0, n):
                if not self.instructions[i].equals(other.instructions[i]):
                    return False
            return True

    def update_holes(self, holes):
        """Recursively looks for holes matching those declared in 'holes'. Found holes instructions have their appropriate declaration attached.

        :param holes: List of HoleDecl objects.
        :return: Nothing. Works in place.
        """
        for instr in self.instructions:
            if instr.is_hole:
                for h in holes:
                    if h.id == instr.id:
                        instr.hole_declaration = h
            elif instr.contains_blocks():
                for ib in instr.get_instruction_blocks():
                    ib.update_holes(holes)

    def get_holes_definitions(self):
        """Recursively search for all holes in the instruction block.

        :return: List of HoleDecl's.
        """
        res = []
        for i in self.instructions:
            res.extend(i.get_holes_definitions())
        return res

    def to_smt2(self, env):
        return interm_to_smt2_ib(self, env=env)

    def __len__(self):
        return len(self.instructions)

    def __iter__(self):
        for i in self.instructions:
            yield i

    def __getitem__(self, index):
        return self.instructions[index]

    def __str__(self):
        res = '{\n'
        for instr in self.instructions:
            res += '\t' + instr.__str__() + '\n'
        res += '}'
        return res



class Instruction(object):
    ASSIGN = 'assign'
    WHILE = 'while'
    IF = 'if'
    EXPR = 'expr'
    CALL = 'call'
    ASSERT = 'assert'

    def __init__(self):
        self.is_meta = False
        self.in_type = ''
        self.is_hole = False

    def get_instruction_blocks(self):  # to be overriden in subclasses
        return []

    def contains_blocks(self):
        return len(self.get_instruction_blocks()) > 0

    def rename_var(self, old_id, new_id):  # to be overriden in subclasses
        raise Exception('Instruction.rename_var: method not implemented!')

    def equals(self, other):  # to be overriden in subclasses
        raise Exception('Instruction.equals: method not implemented!')

    def get_holes_definitions(self):  # to be overriden in subclasses
        raise Exception('Instruction.get_holes_definitions: method not implemented!')

    def set_meta(self, new_meta=True):
        self.is_meta = new_meta

    def collect_variables(self):
        return []

    def collect_nodes(self):
        return [self]



class InstrAssert(Instruction):
    def __init__(self, expr):
        Instruction.__init__(self)
        self.in_type = Instruction.ASSERT
        self.expr = expr

    def __str__(self):
        res = 'assert({0})'.format(self.expr)
        if self.is_meta:
            res += '  (meta)'
        return res

    def rename_var(self, old_id, new_id):
        self.expr.rename_var(old_id, new_id)

    def collect_variables(self):
        res = self.expr.collect_variables()
        return list(set(res))

    def collect_nodes(self):
        res = self.expr.collect_nodes()
        return res

    def equals(self, other):
        if isinstance(other, InstrAssert):
            return self.expr.equals(other.expr)
        else:
            return False

    def get_holes_definitions(self):
        return self.expr.get_holes_definitions()



class InstrAssign(Instruction):
    # var: Variable, expr: Expression
    def __init__(self, var, expr, is_meta=False):
        Instruction.__init__(self)
        assert isinstance(var, Var)
        self.in_type = Instruction.ASSIGN
        self.var = var
        self.expr = expr
        self.is_meta = is_meta

    def __str__(self):
        res = self.var.id + ' = ' + str(self.expr)
        if self.is_meta:
            res += '  (meta)'
        return res

    def rename_var(self, old_id, new_id):
        self.var.rename_var(old_id, new_id)
        self.expr.rename_var(old_id, new_id)

    def collect_variables(self):
        res = [self.var.id]
        res.extend(self.expr.collect_variables())
        return list(set(res))

    def collect_nodes(self):
        res = [self, self.var]
        res.extend(self.expr.collect_nodes())
        return res

    def equals(self, other):
        if isinstance(other, InstrAssign):
            return self.var.equals(other.var) and \
                   self.expr.equals(other.expr)
        else:
            return False

    def get_holes_definitions(self):
        return self.expr.get_holes_definitions()



class InstrWhile(Instruction):
    # cond: Expression, body: InstructionBlock
    def __init__(self, cond, body):
        Instruction.__init__(self)
        self.in_type = Instruction.WHILE
        self.condition = cond
        self.body = body

    def get_instruction_blocks(self):
        return [self.body]

    def __str__(self):
        res = 'while ( ' + str(self.condition) + ' )\n'
        res += str(self.body)
        return res

    def rename_var(self, old_id, new_id):
        self.condition.rename_var(old_id, new_id)
        for instr in self.body.instructions:
            instr.rename_var(old_id, new_id)

    def collect_variables(self):
        res = self.condition.collect_variables()
        res.extend(self.body.collect_variables())
        return list(set(res))

    def collect_nodes(self):
        res = [self]
        res.extend(self.condition.collect_nodes())
        res.extend(self.body.collect_nodes())
        return res

    def equals(self, other):
        if isinstance(other, InstrWhile):
            return self.condition.equals(other.condition) and \
                   self.body.equals(other.body)
        else:
            return False

    def get_holes_definitions(self):
        res = self.condition.get_holes_definitions()
        for ib in self.get_instruction_blocks():
            res.extend(ib.get_holes_definitions())
        return res



class InstrIf(Instruction):
    # cond: Expression, body: InstructionBlock, orelse: InstructionBlock
    def __init__(self, cond, body, orelse=None):
        Instruction.__init__(self)
        if orelse is None:
            orelse = InstrBlock([])
        if isinstance(body, list):
            body = InstrBlock(body)
        if isinstance(orelse, list):
            orelse = InstrBlock(orelse)
        self.in_type = Instruction.IF
        self.condition = cond
        self.body = body
        self.orelse = orelse

    def get_instruction_blocks(self):
        return [self.body, self.orelse]

    def __str__(self):
        res = 'if ( ' + str(self.condition) + ' ) {\n'
        res += str(self.body)
        res += '}\n'
        if self.orelse.size() > 0:
            res += 'else {\n'
            res += str(self.orelse)
            res += '}'
        return res

    def rename_var(self, old_id, new_id):
        self.condition.rename_var(old_id, new_id)
        for instr in self.body.instructions:
            instr.rename_var(old_id, new_id)
        for instr in self.orelse.instructions:
            instr.rename_var(old_id, new_id)

    def collect_variables(self):
        res = self.condition.collect_variables()
        res.extend(self.body.collect_variables())
        res.extend(self.orelse.collect_variables())
        return list(set(res))

    def collect_nodes(self):
        res = [self]
        res.extend(self.condition.collect_nodes())
        res.extend(self.body.collect_nodes())
        res.extend(self.orelse.collect_nodes())
        return res

    def equals(self, other):
        if isinstance(other, InstrIf):
            return self.condition.equals(other.condition) and \
                   self.body.equals(other.body) and \
                   self.orelse.equals(other.orelse)
        else:
            return False

    def get_holes_definitions(self):
        res = self.condition.get_holes_definitions()
        for ib in self.get_instruction_blocks():
            res.extend(ib.get_holes_definitions())
        return res



class InstrHole(Instruction):
    """Instruction representing a hole in the program. Hole is considered to be equal to single
    assignment instruction.
    """

    def __init__(self, hole_decl):
        """
        :param hole_decl: HoleDecl object containing basic information about this hole.
        """
        Instruction.__init__(self)
        self.vars = hole_decl.vars
        self.id = hole_decl.id
        self.hole_decl = hole_decl
        self.is_hole = True

    def rename_var(self, old_id, new_id):
        for i in range(0, len(self.vars)):
            if self.vars[i] == old_id:
                self.vars[i] = new_id
                break

    def equals(self, other):
        if isinstance(other, InstrHole):
            return self.id == other.id
        else:
            return False

    def get_holes_definitions(self):
        return [self.hole_decl]

    def __str__(self):
        return '???-' + self.id + ' (hole)'



class InstrCall(Instruction):
    """Represents a call to a function. This class differs from Op in that it may
    potentially produce side effects, and it is not a standard operator in Python.
    For example, a print function would be represented as a call."""

    def __init__(self, fun_name, args=None):
        """
        :param args: (list[Expression]) a list of expressions being arguments
        of this function call.
        """
        Instruction.__init__(self)
        self.in_type = Instruction.CALL
        if args is None:
            args = []
        self.is_variable = False
        self.is_hole = False
        self.id = fun_name
        self.args = args

    def rename_var(self, old_id, new_id):
        for arg in self.args:
            arg.rename_var(old_id, new_id)

    def collect_variables(self):
        res = []
        for arg in self.args:
            res.extend(arg.collect_variables())
        return list(set(res))

    def collect_nodes(self):
        res = [self]
        for arg in self.args:
            res.extend(arg.collect_nodes())
        return res

    def equals(self, other):
        if isinstance(other, InstrCall):
            return self.id == other.id and \
                   len(self.args) == len(other.args) and \
                   all(self.args[i].equals(other.args[i]) for i in range(0, len(self.args)))
        else:
            return False

    def get_holes_definitions(self):
        res = []
        for a in self.args:
            res.extend(a.get_holes_definitions())
        return res

    def to_smt2(self, env):
        return interm_to_smt2_expr(self, env=env)




class Expression(Instruction):
    """Represents an expressions as a tree of operands and their arguments."""

    def __init__(self, args=None):
        """
        :param args: (list[Expression]) a list of expressions being arguments
        of this expression.
        """
        Instruction.__init__(self)
        self.in_type = Instruction.EXPR
        if args is None:
            args = []
        self.arity = len(args)
        self.is_terminal = True if self.arity == 0 else False
        self.is_variable = False
        self.args = args
        self.is_hole = False

    def rename_var(self, old_id, new_id):  # to be overriden in subclasses when necessary
        """Renames variables in a "total" way, e.g. |x''| ---> z."""
        pass

    def collect_variables(self):  # to be overriden in subclasses when necessary
        return []

    def collect_nodes(self):  # to be overriden in subclasses when necessary
        return [self]

    def equals(self, other):  # to be overriden in subclasses
        raise Exception('Expression.equals: method not implemented!')

    def get_holes_definitions(self):
        res = []
        for a in self.args:
            res.extend(a.get_holes_definitions())
        return res

    def to_smt2(self, env):
        return interm_to_smt2_expr(self, env=env)



class Op(Expression):
    """Contains information about a function (operation) being part of an Expression."""

    # id: String, args: List[Expression]
    def __init__(self, opid, args):
        Expression.__init__(self, args)
        self.id = opid
        self.isLogicOp = True if opid in PythonOperators.logic_ops else False

    def __str__(self):
        res = self.id + '('
        for i in range(0, len(self.args)):
            if i != 0:
                res += ', '
            res += str(self.args[i])
        res += ')'
        return res

    def rename_var(self, old_id, new_id):
        for arg in self.args:
            arg.rename_var(old_id, new_id)

    def collect_variables(self):
        res = []
        for arg in self.args:
            res.extend(arg.collect_variables())
        return list(set(res))

    def collect_nodes(self):
        res = [self]
        for arg in self.args:
            res.extend(arg.collect_nodes())
        return res

    def equals(self, other):
        if isinstance(other, Op):
            return self.id == other.id and \
                   len(self.args) == len(other.args) and \
                   all(self.args[i].equals(other.args[i]) for i in range(0, len(self.args)))
        else:
            return False



class Var(Expression):
    ssa_marker = "'"
    """Marker used in SSA form for subsequent versions of variable. Change in your program, if you
    don't want to use the default apostrophe."""

    def __init__(self, id, sort='Int'):
        Expression.__init__(self)
        self.id = id
        self.base_id = Var.base_id(id)
        self.sort = sort
        self.is_variable = True

    def set_id(self, new_id):
        self.id = new_id
        self.base_id = Var.base_id(new_id)

    def __str__(self):
        return self.get_text()

    def get_text(self):
        return self.id

    def __repr__(self):
        return self.id

    def rename_var(self, old_id, new_id):
        if self.id == old_id:
            self.set_id(new_id)
        # self.id = self.id.replace(old_id, new_id)

    def collect_variables(self):
        return [self.id]

    def equals(self, other):
        if isinstance(other, Var):
            return self.id == other.id
        else:
            return False

    @staticmethod
    def base_id(name):
        k = name.find(Var.ssa_marker)
        if k == -1:
            return name
        else:
            return name[:k].replace('|', '')

    @staticmethod
    def change_base_name(old_name, new_base_name):
        base_name = Var.base_id(old_name)
        return old_name.replace(base_name, new_base_name)


class ConstInt(Expression):
    def __init__(self, value):
        Expression.__init__(self)
        self.value = value

    def __str__(self):
        return self.get_text()

    def get_text(self):
        return str(self.value)

    def equals(self, other):
        if isinstance(other, ConstInt):
            return self.value == other.value
        else:
            return False


class ConstBool(Expression):
    def __init__(self, value):
        Expression.__init__(self)
        self.value = value

    def __str__(self):
        return self.get_text()

    def get_text(self):
        if self.value:
            return 'true'
        else:
            return 'false'

    def equals(self, other):
        if isinstance(other, ConstBool):
            return self.value == other.value
        else:
            return False


class ExprHole(Expression):
    def __init__(self, hole_decl):
        """
        :param hole_decl: HoleDecl object containing basic information about this hole.
        """
        Expression.__init__(self)
        self.hole_decl = hole_decl
        self.is_hole = True

    def __str__(self):
        return self.get_text()

    def get_text(self):
        return '?' + self.hole_decl.id + '?'

    def equals(self, other):
        if isinstance(other, ExprHole):
            return self.hole_decl.id == other.hole_decl.id
        else:
            return False

    def get_holes_definitions(self):
        return [self.hole_decl]

    def rename_var(self, old_id, new_id):
        self.hole_decl.rename_var(old_id, new_id)


def rename_base_vars(node, old_bid, new_bid):
    """Changes base names of all variables contained in the node argument.

    :param node: (InstrBlock | Instruction | Expression) Any element of the intermediary program representation.
    :param old_bid: (str) Current base name of a variable.
    :param new_bid: (str) New base name of a variable.
    :return: (type(node)) Node with changed base names of all variables with the specified base name (old_bid).
    """
    nodes = node.collect_nodes()
    for n in nodes:
        if type(n) == Var:
            if n.base_id == old_bid:
                n.set_id(Var.change_base_name(n.id, new_bid))
    return node




# -------------------------------------------------------------------------------------
#                        UTILS FOR CONVERTING TO SMT2 PROGRAM
# -------------------------------------------------------------------------------------



def interm_to_smt2_ib(ib, env):
    """Converts intermediary representation of an instruction block to SMT-LIB
     representation."""
    assert isinstance(ib, InstrBlock)
    smt_tr = SmtlibTranslator(env.show_comments, env.assignments_as_lets)
    program_constr = smt_tr.produce_constr_lists(ib)[0]
    # CODE_SMT = utils.conjunct_constrs_smt2(program_constr)
    # CODE_SMT = smt_tr.produce_text(ib)
    return ProgramSmt2(program_constr, smt_tr.let_declarations)


def interm_to_smt2_expr(expr, env=None):
    """Converts intermediary representation of an expression to SMT-LIB
     representation."""
    assert isinstance(expr, Expression)
    CODE_SMT = ExprTranslator.apply(expr)
    return ProgramSmt2([CODE_SMT])





class PythonOperators:
    op_and = 'and'
    op_or = 'or'
    op_not = 'not'
    logic_ops = [op_and, op_or, op_not]

    op_eq = '=='
    op_neq = '!='
    op_lt = '<'
    op_lte = '<='
    op_gt = '>'
    op_gte = '>='
    cmp_ops = [op_eq, op_neq, op_lt, op_lte, op_gt, op_gte]

    op_add = '+'
    op_sub = '-'
    op_usub = 'unary_-'
    op_mult = '*'
    op_div = '/'
    op_mod = '%'
    op_pow = "**"
    math_ops = [op_add, op_sub, op_mult, op_div, op_mod, op_pow]

    all_ops = logic_ops[:]
    all_ops.extend(cmp_ops)
    all_ops.extend(math_ops)



class ExprTranslator(object):
    """ExprTranslator is used to convert a program in intermediary representation to the equivalent SMT-LIB 2.0 code."""

    OPS_TO_SMTLIB = {PythonOperators.op_add: ('+',''),
                     PythonOperators.op_sub: ('-', ''),
                     PythonOperators.op_usub: ('-', ''),
                     PythonOperators.op_mult: ('*', ''),
                     PythonOperators.op_div: ('/', ''),
                     PythonOperators.op_mod: ('mod', ''),
                     # '^' operator is not part of SMTLIB but is recognized by Z3 as power.
                     PythonOperators.op_pow: ('^', ''),
                     PythonOperators.op_eq: ('=', ''),
                     PythonOperators.op_neq: ('not (=', ')'),
                     PythonOperators.op_lt: ('<', ''),
                     PythonOperators.op_lte: ('<=', ''),
                     PythonOperators.op_gt: ('>', ''),
                     PythonOperators.op_gte: ('>=', ''),
                     PythonOperators.op_not: ('not', ''),
                     PythonOperators.op_and: ('and', ''),
                     PythonOperators.op_or: ('or', ''),
                     }
    # Btw in SMT-LIB: div = integer division, rem = remainder.

    @staticmethod
    def apply(expr, fun_annotate_subexpr = None):
        """Generates SMT-LIB 2.0 code for the given expression.

        :param expr: (Expression) Expression in the intermediary program representation. It may be found for example on right sides of assignments or as function arguments.
        :param fun_annotate_subexpr: (=>str) function for naming logical subexpressions in the formula.
        :return: (str) Expression in SMT-LIB 2.0.
        """
        assert isinstance(expr, Expression)
        t = type(expr)
        if t is Op:
            try:
                pre, suff = ExprTranslator.OPS_TO_SMTLIB[expr.id]
                return ExprTranslator.subexpr_to_smtlib(expr, pre, suff, fun_annotate_subexpr)
            except KeyError:
                raise Exception(str(expr.id) + ': operation not supported!')

        elif t is Var:
            return expr.get_text()
        elif t is ConstInt or t is ConstBool:
            return str(expr.get_text())
        elif t is ExprHole:
            return expr.hole_decl.get_function_call()
        else:
            raise Exception(str(t)+': expression type not supported!')

    @staticmethod
    def subexpr_to_smtlib(expr, pre, suff='', fun_annotate_subexpr = None):
        """Transforms the provided operation subexpression into equivalent subexpression in SMT-LIB 2.0.

        :param expr: (Op) Operation subexpression in the intermediary program representation.
        :param pre: (str) Code in SMT-LIB 2.0 to be added after starting '('.
        :param suff: (str) Code in SMT-LIB 2.0 to be added before closing ')'.
        :param fun_annotate_subexpr: (=>str) function for naming logical subexpressions in the formula.
        :return: (str) Subexpression in SMT-LIB 2.0
        """
        if fun_annotate_subexpr is not None and pre in PythonOperators.logic_ops:
            return '(! (' + pre + ' ' + ExprTranslator.concatenate_args(expr, fun_annotate_subexpr) + suff + \
                   ') :named ' + fun_annotate_subexpr() + ')'
        else:
            return '(' + pre + ' ' + ExprTranslator.concatenate_args(expr, fun_annotate_subexpr) + suff + ')'

    @staticmethod
    def concatenate_args(expr, fun_annotate_subexpr):
        """Merges produced SMT-LIB subexpressions into one string."""
        text = ' '.join([ExprTranslator.apply(arg, fun_annotate_subexpr) for arg in expr.args])
        return text




class SmtlibTranslator(object):

    def __init__(self, show_comments = True, assignments_as_lets = True, loop_unrolling = True,
                 pretty_print_constraints=False, loop_unrolling_level = 2):
        self.show_comments = show_comments
        self.expr_translator = ExprTranslator
        self.assignments_as_lets = assignments_as_lets
        self.loop_unrolling = loop_unrolling
        self.loop_unrolling_level = loop_unrolling_level
        self.pretty_print_constraints = pretty_print_constraints
        self.let_declarations = []

    def reset(self):
        self.let_declarations = []


    def produce_text(self, ib, indent=""):
        """Returns a string containing nicely printed text of the program constraints."""
        assert isinstance(ib, InstrBlock)
        text = ""
        for ins in ib.instructions:
            # text += '; ' + str(ins).replace('\n', '\n;') + '\n' # printing instruction for which constraint was generated
            text += self.produce_text_instr(ins, indent=indent)
        return text


    def produce_constr_lists(self, ib):
        """Returns a tuple of two lists: the first contains only constraints, and the second
         contains also comments."""
        assert isinstance(ib, InstrBlock)
        self.reset()
        return self.produce_constr_lists_internal(ib)


    def produce_constr_lists_internal(self, ib):
        """Returns a tuple of two lists: the first contains only constraints, and the second
         contains also comments."""
        assert isinstance(ib, InstrBlock)
        constr = []
        comm = []
        for instr in ib.instructions:
            comm.append('; ' + str(instr).replace('\n', '\n;') + '\n')
            for c in self.produce_constraints_instr(instr):
                constr.append(c)
                comm.append(c)
        return constr, comm


    def produce_constraints_instr(self, instr):
        """Generates constraints for the given instruction.

        :return (list): A List containing constraints for SMT solver.
        """
        t = type(instr)
        if t is InstrAssign:
            res = self.produce_constraints_assign(instr)
            if self.show_comments:
                res.append('\t\t\t;#ASSIGN: ' + str(instr) + '\n')
            return res
        elif t is InstrIf:
            return self.produce_constraints_if(instr)
        elif t is InstrWhile:
            return self.produce_constraints_while(instr)
        elif t is InstrHole:
            raise Exception('Instruction holes are currently not supported!')
        elif isinstance(instr, Expression):
            # Expression instruction in most cases does not change outcome of the program
            # (exception: calling a function which changes state).
            return ['']  #TODO: perhaps ['true'] should be returned for some constraints to be valid...
        elif isinstance(instr, InstrAssert):
            expr = self.expr_translator.apply(instr.expr)
            return [expr]
        else:
            raise Exception(str(t)+': instruction not supported!')


    def produce_text_instr(self, instr, indent=""):
        """Generates SMT-LIB code for the given instruction in the form of string.

        :return (str): SMT-LIB code representing semantics of the given instruction.
        """
        t = type(instr)
        if t is InstrAssign:
            return self.produce_text_assign(instr, indent=indent)
        elif t is InstrIf:
            return self.produce_text_if(instr, indent=indent)
        elif t is InstrWhile:
            return self.produce_text_while(instr, indent=indent)
        elif t is InstrHole:
            raise Exception('Instruction holes are currently not supported!')
        elif isinstance(instr, Expression):
            # Expression instruction in most cases does not change outcome of the program
            # (exception: calling a function which changes state).
            return ""  #TODO: perhaps ['true'] should be returned for some constraints to be valid...
        elif isinstance(instr, InstrAssert):
            return indent + self.expr_translator.apply(instr.expr)
        else:
            raise Exception(str(t)+': instruction not supported!')


    def produce_constraints_assign(self, instr):
        assert isinstance(instr, InstrAssign)
        if self.pretty_print_constraints:
            return [self.produce_text_assign(instr)]
        else:
            L = instr.var.id
            R = self.expr_translator.apply(instr.expr)
            if self.assignments_as_lets and not instr.is_meta:
                self.let_declarations.append((L,R))
                return []
            else:
                F1 = '(= ' + L + ' ' + R + ')'
                return [F1]

    def produce_text_assign(self, instr, indent=""):
        assert isinstance(instr, InstrAssign)
        L = instr.var.id
        R = self.expr_translator.apply(instr.expr)
        if self.assignments_as_lets and not instr.is_meta:
            self.let_declarations.append((L, R))
            return ""
        else:
            return indent + '(= ' + L + ' ' + R + ')'


    def produce_constraints_if(self, instr):
        assert isinstance(instr, InstrIf)
        cond = self.expr_translator.apply(instr.condition)
        body,cm = self.produce_constr_lists_internal(instr.body)
        orelse,cm = self.produce_constr_lists_internal(instr.orelse)
        impl1 = '(=> ' + cond + ' ' + utils.conjunct_constrs_smt2(body) + ')\n\t\t'
        impl2 = '(=> ' + '(not ' + cond + ')' + ' ' + utils.conjunct_constrs_smt2(orelse) + ')\n\t\t'
        F1 = impl1
        F2 = impl2
        #F3 = '(or ' + cond + ' (not ' + cond + '))'  # at least one branch must be true in IF THEN ELSE
        return [F1, F2]

    def produce_text_if(self, instr, indent=""):
        assert isinstance(instr, InstrIf)
        def text_cond(c, b):
            return indent + '(=> ' + c + '\n' +\
                   indent + b +\
                   indent + ')\n'
        cond = self.expr_translator.apply(instr.condition)
        body = self.produce_text(instr.body, indent=indent + "\t")
        text = text_cond(cond, body)
        if len(instr.orelse) > 0:
            orelse = self.produce_text(instr.orelse, indent=indent + "\t")
            text += text_cond('(not ' + cond + ')', orelse)
        return text


    def produce_constraints_while(self, instr):
        assert isinstance(instr, InstrWhile)
        cond = self.expr_translator.apply(instr.condition)
        body = self.produce_constr_lists_internal(instr.body)
        return "(true)"

    def produce_text_while(self, instr, indent=""):
        assert isinstance(instr, InstrWhile)
        cond = self.expr_translator.apply(instr.condition)
        body = self.produce_text(instr.body, indent=indent)
        return indent + "(true)"