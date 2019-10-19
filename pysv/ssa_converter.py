import copy
from pysv.interm import *
from pysv import contract
from pysv import utils



class ConverterSSA(object):
    """ConverterSSA is used to convert instruction block to the SSA (Single Static Assignment)
     form, in which every new assignment to a variable is equivalent to creating a new ("marked")
     version of this variable. SSA form is necessary in the context of SMT verification and
     synthesis because in logical formulas we must associate each variable with exactly one value.

    Attributes:
    -----------
    :param ssa_marker: (str) Marker being added on the end of a variable name to mark
     subsequent assignments. (default="'")
    :param ssa_quote_marked_vars: (bool) Specifies, if ssa-marked variables should be quoted
     with '|', a special symbol in SMT-LIB which allows for arbitrary characters in names.
     (default=True)
    """

    def __init__(self, ssa_marker = "'", ssa_quote_marked_vars = True, ssa_mark_indexed=True):
        self.ssa_marker = ssa_marker
        self.ssa_quote_marked_vars = ssa_quote_marked_vars
        self.ssa_mark_indexed = ssa_mark_indexed


    def convert(self, ib, program_vars):
        """Returns new instruction block and postcondition converted to SSA
         (Single Static Assignment) form.

        ISSUES:\n
        - all variables are treated as global. Local variables in for example 'if' bodies
         lead to errors if those variables were not declared before 'if'.

        :param ib: (InstrBlock) instruction block representing the whole program.
        :param program_vars: (list[dict]) ProgramVars object containing information about variables
         and their types.
        :return: A tuple containing the SSA form of the given program and index of variable
         assignments.
        """
        assert isinstance(program_vars, contract.ProgramVars)
        # Assignment index tracks how many times variables were assigned to.
        # Input variables are assumed to start with some assigned value.
        assign_index = {v: 1 for v in program_vars.input_vars}
        ib_ssa, index, _ = self.convert_for_assign_index(ib, assign_index)
        return ib_ssa, index


    def convert_for_assign_index(self, main_ib, assign_index, use_index=None):
        """Returns new instruction block and postcondition converted to SSA
         (Single Static Assignment) form.

        :param main_ib: (InstrBlock) instruction block representing the whole program.
        :param assign_index: (dict[str, int]) Dictionary storing the number of times that a
         given variable was assigned to.
        :param use_index: (dict[str, int]) Index to use for variables in expressions. By default
         it is the the same as assign_index. It would differ for example when we want to have
         distinct variable assignments in if-else branches, while some expressions or assertions
         still may depend on values set before the if-else.
        :return: A tuple containing the SSA form of the given program and index of variable
         assignments.
        """
        assert isinstance(main_ib, InstrBlock)
        assert isinstance(assign_index, dict)
        if use_index is None:
            use_index = dict(assign_index)

        main_ib = copy.deepcopy(main_ib)
        assign_index = dict(assign_index)

        for instr in main_ib.instructions:
            if isinstance(instr, InstrAssert):
                self.convert_instr_assert(instr, use_index)
            elif isinstance(instr, InstrAssign):
                _, assign_index, use_index = self.convert_instr_assign(instr, assign_index, use_index)
            elif isinstance(instr, InstrIf):
                _, assign_index, use_index = self.convert_instr_if(instr, assign_index, use_index)
            elif isinstance(instr, InstrWhile):
                _, assign_index, use_index = self.convert_instr_while(instr, assign_index, use_index)
            elif isinstance(instr, InstrCall):
                _, assign_index, use_index = self.convert_instr_call(instr, assign_index, use_index)
            elif isinstance(instr, InstrHole):
                raise Exception('Instruction holes are currently not supported!')
            else:
                raise Exception("Unsupported instruction of type {0} encountered during SSA conversion.".format(type(instr)))

        return main_ib, assign_index, use_index


    def convert_instr_assert(self, instr, parent_use_index):
        assert isinstance(instr, InstrAssert)
        # Converting expression
        self.update_expr(instr.expr, parent_use_index)
        return instr


    def convert_instr_call(self, instr, parent_assign_index, parent_use_index):
        assert isinstance(instr, InstrCall)
        # Converting expression
        for a in instr.args:
            assert isinstance(a, Expression)
            self.update_expr(a, parent_use_index)
        return instr, parent_assign_index, parent_use_index


    def convert_instr_assign(self, instr, parent_assign_index, parent_use_index):
        assert isinstance(instr, InstrAssign)
        parent_assign_index = parent_assign_index.copy()
        parent_use_index = parent_use_index.copy()

        # Converting expression
        self.update_expr(instr.expr, parent_use_index)

        # Converting variable
        x = instr.var.base_id
        self.inc_assign_num(x, parent_assign_index)  # updating global variable dict
        if parent_assign_index[x] > 1:  # not the first (initial) assignment to a variable
            new_id = self.mark_var(x, parent_assign_index[x])
            instr.var.id = new_id
            parent_use_index[x] = parent_assign_index[x]  # equalizing variable between 'use' and 'assign'
        return instr, parent_assign_index, parent_use_index


    def convert_instr_if(self, instr, parent_assign_index, parent_use_index):
        """Converts an if-else instruction to its SSA form.

        :return: A tuple containing the SSA form of the if-else instruction, and updated
         indexes for 'assignments' und 'uses'. Returned 'uses' index is updated in the same way
         as assignments index, since any assignment in one of if's branches results in
         synchronizing variables between branches, and those updated variables are to be
         used in instructions following this if instruction.
        """
        assert isinstance(instr, InstrIf)
        parent_assign_index = parent_assign_index.copy()
        parent_use_index = parent_use_index.copy()

        # Converting condition
        self.update_expr(instr.condition, parent_use_index)

        # Converting both body blocks of IF. Copy of parent_assign_nums dict will be made inside.
        ib, b_assign_index, b_use_index = self.convert_for_assign_index(instr.body, parent_assign_index, parent_use_index)
        instr.body = ib
        ib2, o_assign_index, o_use_index = self.convert_for_assign_index(instr.orelse, b_assign_index, parent_use_index)
        instr.orelse = ib2

        # Balancing (leveling) of IF branches.
        self.balance_var_level_if(instr, b_assign_index, b_use_index, o_assign_index, o_use_index)

        # Updating global assignment index.
        parent_assign_index.update(o_assign_index)
        parent_use_index.update(o_assign_index)
        return instr, parent_assign_index, parent_use_index


    def convert_instr_while(self, instr, parent_assign_index, parent_use_index):
        assert isinstance(instr, InstrWhile)
        parent_assign_index = parent_assign_index.copy()
        parent_use_index = parent_use_index.copy()

        # Converting condition
        self.update_expr(instr.condition, parent_use_index)

        ib, index, use_index = self.convert_for_assign_index(instr.body, parent_assign_index, parent_use_index)
        parent_assign_index.update(index)
        parent_use_index.update(use_index)
        instr.body = ib
        return instr, parent_assign_index, parent_use_index


    def inc_assign_num(self, base_id, dictionary):
        """Updates dictionary of the number of assignments per variable name.

        :param base_id: (str) base ID of a variable which was assigned to, so its counter
        needs to be incremented.
        :param dictionary: (dict) assignment index.
        """
        if base_id in dictionary:
            dictionary[base_id] += 1
        else:
            dictionary[base_id] = 1


    def update_dictionary(self, dictionary, base_id, new_val):
        """Updates dictionary of the number of assignments per variable name.

        :param base_id: base ID of a variable which was assigned to, so its counter needs to be incremented.
        :param dictionary: (dict) assignment index.
        :param new_val: (int) value to be inserted.
        """
        dictionary[base_id] = new_val


    def collect_assigned_vars(self, ib):
        """Returns a set of variable objects which were assigned to."""
        vars = set()
        for ins in ib:
            if ins.in_type == Instruction.ASSIGN:
                vars.add(ins.var)
            elif ins.in_type == Instruction.IF:
                av = self.collect_assigned_vars(ins.body)
                av2 = self.collect_assigned_vars(ins.orelse)
                for v in av.union(av2):
                    vars.add(v)
            elif ins.in_type == Instruction.WHILE:
                av = self.collect_assigned_vars(ins.body)
                for v in av:
                    vars.add(v)
        return vars


    def balance_var_level_if(self, instr, assign_index_body, use_index_body, assign_index_orelse,
                             use_index_orelse):
        """Adds meta-instructions for blocks of IF for all variables in if's bodies.

        Example 1:\n
         x = 0
         if COND1:
            x += 1
         else:
            x -= 1

        After balancing:\n
         x = 0
         if COND1:
            x'1 = x + 1
            x'3 = x'1 (meta)
         else:
            x'2 = x - 1
            x'3 = x'2 (meta)


        Example 2:\n
         x = 0
         if COND1:
            x += 1
            if COND2:
                x += 1

        After balancing:\n
         x = 0
         if COND1:
            x'1 = x + 1
            if COND2:
                x'2 = x'1 + 1
                x'3 = x'2  (meta)
            else:  (meta)
                x'3 = x'1  (meta)
            x'4 = x'3 (meta)
         else:
            x'4 = x

        :param instr: (InstrIf) if-instruction to be balanced.
        :param assign_index_body: (dict[str,int]) Stores the number of times that variables were
         assigned to from the perspective of if's main block.
        :param use_index_body: (dict[str,int]) Stores the last assignment for a given variable
         from the perspective of if's main block. Is not affected by parallel blocks in if instruction,
         while the assign_index'es are.
        :param assign_index_orelse: (dict[str,int]) Stores the number of times that variables were
         assigned to from the perspective of if's else block.
        :param use_index_orelse: (dict[str,int]) Stores the last assignment for a given variable
         from the perspective of if's else block. Is not affected by parallel blocks in if instruction,
         while the assign_index'es are.
        :return: Nothing. Updates 'instr' in place.
        """
        assert isinstance(instr, InstrIf)
        vars1 = self.collect_assigned_vars(instr.body)
        vars2 = self.collect_assigned_vars(instr.orelse)
        vars_base = {v.base_id for v in vars1.union(vars2)}
        for v in sorted(vars_base):
            assert v in assign_index_body and v in assign_index_orelse,\
                "Variable {0} is not initialized!".format(v)  # v was initialized before reaching this if

            # v is known to be assigned some value in at least one branch of if
            n1 = assign_index_body[v]
            n2 = assign_index_orelse[v]
            n = max(n1, n2)
            leftv = self.mark_var(v, n + 1)

            # use_index always contains <= values than the assign_index.
            # use_index after the execution of an if branch contains versions of the variables
            # for the right hand of the balancing assignment instruction.
            rightv1 = self.mark_var_index(v, use_index_body)
            rightv2 = self.mark_var_index(v, use_index_orelse)

            self.update_dictionary(assign_index_body, v, n + 1)
            self.update_dictionary(assign_index_orelse, v, n + 1)
            a1 = InstrAssign(Var(leftv), Var(rightv1), is_meta=True)
            a2 = InstrAssign(Var(leftv), Var(rightv2), is_meta=True)
            instr.body.instructions.append(a1)
            instr.orelse.instructions.append(a2)


    def update_expr(self, expr, dictionary, frozen_vars=None):
        """Updates all variables in the expression to their SSA-form according to a dictionary
         with number of previous assignments of each variable.

        :param expr: (Expression) Expression in which variables will be updated.
        :param dictionary: (dict[str,int]) Contains mapping of variables base names to number of
         their previous assignments, e.g. {'x': 0, 'y': 2}. If variable is not in the dictionary
         than it is treated as occurring for the first time.
        :param frozen_vars: (dict[str,str]) a set of variables which will not be updated. Useful
         for example when converting postcondition for leaving out the input variables.
        :return: Nothing. Works in place on the provided expression.
        """
        if frozen_vars is None:
            frozen_vars = dict()
        if type(expr) is Var:
            if expr.base_id not in frozen_vars:
                expr.id = self.actual_var_id(expr.base_id, dictionary)

        elif type(expr) is ExprHole:
            # Updating variables dictionary of a hole
            new_dict = {}
            old_dict = dict(expr.hole_decl.vars)
            for v in old_dict:
                tpe = expr.hole_decl.vars[v]
                new_id = self.actual_var_id(Var.base_id(v), dictionary)
                new_dict[new_id] = tpe
                del expr.hole_decl.vars[v]
                expr.hole_decl.vars[new_id] = tpe
            # expr.hole_decl.vars = new_dict  # set new variables dict

        elif type(expr) is Op:
            for e in expr.args:
                self.update_expr(e, dictionary, frozen_vars=frozen_vars)

        else: # for constants
            pass


    def mark_var_index(self, base_id, assign_index):
        """Marks variable using the appropriate number from assign_index."""
        if base_id not in assign_index:
            return base_id
        elif self.ssa_mark_indexed:
            return self.mark_var_indexed(base_id, assign_index[base_id])
        else:
            return self.mark_var_quoted(base_id, assign_index[base_id])


    def mark_var(self, base_id, num):
        """Marks variable using the provided number."""
        if self.ssa_mark_indexed:
            return self.mark_var_indexed(base_id, num)
        else:
            return self.mark_var_quoted(base_id, num)


    def mark_var_quoted(self, base_id, num):
        """Returns a new name of the variable with added 'num' markers at the end of
         the variable. Apostrophe is not allowed in simple symbols in SMT-LIB 2.0,
         so variable names with ' must be quoted symbols (marked with '|' at the ends).
        """
        # num - Interpretation: number of assignments. Only 1 assignment means no mark.
        # x = 5  ; num=1
        # x' = 7  ; num=2
        if num == 0:
            return base_id
        name = base_id + (self.ssa_marker * (num-1))
        if num > 1 and self.ssa_quote_marked_vars:
            return '|' + name + '|'
        else:
            return name


    def mark_var_indexed(self, base_id, num):
        """Returns a new name of the variable with added marker and then index at the
         end of the variable. Apostrophe is not allowed in simple symbols in SMT-LIB 2.0,
         so variables names must be quoted symbols (marked with '|' at the ends).
        """
        if num <= 1:
            return base_id
        name = base_id + self.ssa_marker + str(num-1)
        if self.ssa_quote_marked_vars:
            return '|' + name + '|'
        else:
            return name


    def actual_var_id(self, base_id, dictionary):
        if base_id in dictionary:
            return self.mark_var(base_id, dictionary[base_id])
        else:
            return base_id





def convert(program, post, program_vars, ssa_quote_marked_vars = True, ssa_mark_indexed = True):
    """Returns an instruction block and postcondition converted to SSA (Single
    Static Assignment) form. This function acts as a wrapper for ConverterSSA object.

    :param program: (ProgramInterm) instruction block representing the whole program.
    :param post: (Expression) expression representing a postcondition.
    :param program_vars: (ProgramVars) information about variables and their types.
    :return: A tuple containing the SSA form of the given program (block of instructions) and postcondition.
    """
    assert isinstance(program_vars, contract.ProgramVars)
    assert isinstance(program, ProgramInterm)
    assert isinstance(post, Expression)

    ssa_conv = ConverterSSA(ssa_quote_marked_vars = ssa_quote_marked_vars,
                            ssa_mark_indexed=ssa_mark_indexed)
    # Converting program's body.
    src_ib_ssa, assign_index = ssa_conv.convert(program.src, program_vars)
    # Converting postcondition.
    ssa_conv.update_expr(post, assign_index, frozen_vars=program_vars.input_vars)

    utils.logger.debug('------------------------------')
    utils.logger.debug('SSA form:')
    utils.logger.debug('------------------------------')
    utils.logger.debug(str(src_ib_ssa))

    return ProgramInterm(src_ib_ssa), post



def convert_ib(program, program_vars, ssa_quote_marked_vars = True, ssa_mark_indexed = True):
    """Returns an instruction block converted to SSA (Single Static
     Assignment) form. This function acts as a wrapper for ConverterSSA object.

    :param program: (ProgramInterm) instruction block representing the whole program.
    :param program_vars: (ProgramVars) information about variables and their types.
    :return: (ProgramInterm) the SSA form of the given program.
    """
    assert isinstance(program_vars, contract.ProgramVars)
    assert isinstance(program, ProgramInterm)

    ssa_conv = ConverterSSA(ssa_quote_marked_vars = ssa_quote_marked_vars,
                            ssa_mark_indexed=ssa_mark_indexed)
    src_ib_ssa, assign_index = ssa_conv.convert(program.src, program_vars)

    utils.logger.debug('------------------------------')
    utils.logger.debug('SSA form:')
    utils.logger.debug('------------------------------')
    utils.logger.debug(str(src_ib_ssa))

    return ProgramInterm(src_ib_ssa)