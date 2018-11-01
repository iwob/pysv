import copy
from pysv.interm import *
from pysv import contract
from pysv import utils



class ConverterSSA(object):
    """ConverterSSA is used to convert instruction block to the SSA (Single Static Assignment)
     form, in which every new assignment to a variable is equivalent to creating a new ("marked")
     version of this variable. SSA form is necessary in the context of SMT verification and
     synthesis because in logical formulas we must associate each variable with exactly one value.

    TODO:
    - Currently every assignment results in creating marked variable, even if this is the first
     use of this variable. It is important to note that if certain variable is present in the
     precondition, then indeed it's first program assignment must be marked to avoid errors.

    Attributes:
    -----------
    :param ssa_marker: (str) Marker being added on the end of a variable name to mark
     subsequent assignments. (default="'")
    :param ssa_quote_marked_vars: (bool) Specifies, if ssa-marked variables should be quoted
     with '|', a special symbol in SMT-LIB which allows for arbitrary characters in names.
     (default=True)
    :param ssa_quote_unmarked_vars: (bool) Specifies, if normal (unmarked) variables should be
     also quoted (for aesthetic reasons). (default=False)
    """

    def __init__(self, ssa_marker = "'", ssa_quote_marked_vars = True, ssa_quote_unmarked_vars = False,
                 ssa_mark_indexed=False):
        self.ssa_marker = ssa_marker
        self.ssa_quote_marked_vars = ssa_quote_marked_vars
        self.ssa_quote_unmarked_vars = ssa_quote_unmarked_vars
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
        return self.convert_for_index(ib, assign_index)


    def convert_for_index(self, main_ib_0, assign_index):
        """Returns new instruction block and postcondition converted to SSA
         (Single Static Assignment) form.

        ISSUES:\n
        - all variables are treated as global. Local variables in for example 'if' bodies
         lead to errors if those variables were not declared before 'if'.

        :param main_ib_0: (InstrBlock) instruction block representing the whole program.
        :param assign_index: (dict[str, int]) Dictionary storing the number of times that a
         given variable was used. If not specified, it will be automatically initialized so
         that input variables start with 1 assignment.
        :return: A tuple containing the SSA form of the given program and index of variable
         assignments.
        """
        assert isinstance(main_ib_0, InstrBlock)
        assert isinstance(assign_index, dict)

        main_ib = copy.deepcopy(main_ib_0)


        def convert_instr_assert(instr, parent_assign_index):
            assert isinstance(instr, InstrAssert)
            # Converting expression
            self.update_expr(instr.expr, parent_assign_index)


        def convert_instr_call(instr, parent_assign_index):
            assert isinstance(instr, InstrCall)
            # Converting expression
            for a in instr.args:
                assert isinstance(a, Expression)
                self.update_expr(a, parent_assign_index)


        def convert_instr_assign(instr, parent_assign_index):
            assert isinstance(instr, InstrAssign)
            # Converting expression
            self.update_expr(instr.expr, parent_assign_index)

            # Converting variable
            x = instr.var.base_id
            inc_assign_num(x, assign_index)  # updating global variable dict
            if assign_index[x] > 1: # not the first (initial) assignment to a variable
                new_id = self.mark_var(x, assign_index[x] - 1)
                instr.var.id = new_id
                #TODO: update references also in block containing this block
                #self.update_future_references(ib, x, new_id, instr_num+1)


        def convert_instr_if(instr, parent_assign_index):
            assert isinstance(instr, InstrIf)
            dict_before_if = parent_assign_index.copy()

            # Converting condition
            self.update_expr(instr.condition, parent_assign_index)

            # Converting both body blocks of IF. Copy of parent_assign_nums dict will be made inside.
            # print('BODY BRANCH')
            ib, parent_assign_index = self.convert_for_index(instr.body, parent_assign_index)
            instr.body = ib

            # print('ORELSE BRANCH')
            ib, parent_assign_index = self.convert_for_index(instr.orelse, parent_assign_index)
            instr.orelse = ib

            # Balancing (leveling) of IF branches.
            balance_var_level_if(instr, dict_before_if)

            # Finding meta instructions containing if-leveling and updating parent assigns dict.
            # These meta-instructions contain all information needed to update parent assignments.
            for i in instr.body.instructions:
                if i.is_meta and i.in_type is Instruction.ASSIGN:
                    num = i.var.id.count("'") + 1
                    update_dictionary(assign_index, i.var.base_id, num)
                    update_dictionary(parent_assign_index, i.var.base_id, num)


        def convert_instr_while(instr, parent_assign_index):
            global assign_index
            assert isinstance(instr, InstrWhile)

            # Converting condition
            self.update_expr(instr.condition, parent_assign_index)

            ib, assign_index = self.convert_for_index(instr.body, parent_assign_index)
            instr.body = ib


        def inc_assign_num(base_id, dictionary):
            """Updates dictionary of the number of assignments per variable name.

            :param base_id: (str) base ID of a variable which was assigned to, so it's counter
            needs to be incremented.
            :param dictionary: (dict) assignment index.
            """
            if base_id in dictionary:
                dictionary[base_id] += 1
            else:
                dictionary[base_id] = 1


        def update_dictionary(dictionary, base_id, new_val):
            """Updates dictionary of the number of assignments per variable name.

            :param base_id: base ID of a variable which was assigned to, so it's counter needs to be incremented.
            :param dictionary: (dict) assignment index.
            :param new_val: (int) value to be inserted.
            """
            dictionary[base_id] = new_val


        def balance_var_level_if(instr, dict_before_if):
            """Adds meta-instructions for blocks of IF for all variables in if's bodies.

            Example:\n
             x = 0; z = 0
             if b:
                 z' = 1
                 x' = 4
             else:
                 x'' = 5

            After balancing:\n
             x = 0; z = 0
             if b:
                 z' = 1
                 x' = 4
                 x''' = x'  (meta)
                 z'' = z' (meta)
             else:
                 x'' = 5
                 x''' = x''  (meta)
                 z'' = z  (meta)

            :param instr: if-instruction to be balanced.
            :param dict_before_if: Dictionary containing number of previous assignments to
             variables before this if-instruction.
            :return: Nothing. Updates 'instr' in place.
            """
            s = StatsIf(instr)
            for v in sorted(s.vars_dict.keys()):
                level = assign_index[v]
                balance_var_level(instr, v, level, dict_before_if)


        def balance_var_level(if_instr, base_id, level, dict_before_if):
            """Adds meta-instructions for blocks of IF which will introduce a "shared variable" in
            both blocks (similar concept to phi function in SSA form).

            :param if_instr:
            :param base_id: original name of the variable (without "time" markers).
            :param level: exact level of shared variable.
            :param dict_before_if: Dictionary containing number of previous assignments to
             variables before this if-instruction.
            :return:
            """
            id_left = self.mark_var(base_id, level)

            meta1 = get_meta_instr(if_instr.body, base_id, Var(id_left), dict_before_if)
            if_instr.body.append(meta1)

            meta2 = get_meta_instr(if_instr.orelse, base_id, Var(id_left), dict_before_if)
            if_instr.orelse.append(meta2)


        def get_meta_instr(ib, base_id, var_L, dict_before_if):
            """It is assumed here that ib was already converted to SSA form.

            :param ib: Instruction block.
            :param base_id: Original name of the variable (without "time" markers).
            :param var_L: Variable on the left side of the assignment.
            :param dict_before_if: Dictionary containing number of previous assignments to variables before this if-instruction.
            :return: Additional instruction which assigns to var_L last var with a given base name
            from this block.
            """
            last = get_last_id_of_var(ib, base_id, dict_before_if)
            # print('(SSA) ib before last: '+str(ib))
            # print('(SSA) last: '+str(last))
            id_R = self.mark_var(base_id, last.count("'"))
            var_R = Var(id_R)
            meta_in = InstrAssign(var_L, var_R)
            meta_in.set_meta(True)
            return meta_in


        def get_last_id_of_var(ib, base_id, dict_before_if):
            """Returns the last id of a variable (the one with the most time markers).

            :param ib: Instruction block.
            :param base_id: Original name of the variable (without "time" markers).
            :param dict_before_if: Dictionary containing number of previous assignments to variables before this if-instruction.
            :return:
            """
            last_assigned = self.actual_var_id(base_id, dict_before_if)  # last assigned id of a given variable.
            # FIXME: if variable was marked before IF and was not present in the IF's body, then this will produce an error of using old, initial version of the variable...
            for instr in ib.instructions:
                if (instr.in_type == Instruction.ASSIGN and
                    instr.var.base_id == base_id):
                    last_assigned = instr.var.id
            return last_assigned


        for instr in main_ib.instructions:
            if isinstance(instr, InstrAssert):
                convert_instr_assert(instr, assign_index)
            elif isinstance(instr, InstrAssign):
                convert_instr_assign(instr, assign_index)
            elif isinstance(instr, InstrIf):
                convert_instr_if(instr, assign_index)
            elif isinstance(instr, InstrWhile):
                convert_instr_while(instr, assign_index)
            elif isinstance(instr, InstrCall):
                convert_instr_call(instr, assign_index)
            elif isinstance(instr, InstrHole):
                raise Exception('Instruction holes are currently not supported!')
            else:
                raise Exception("Unsupported instruction of type {0} encountered during SSA conversion.".format(type(instr)))

        return main_ib, assign_index


    def update_expr(self, expr, dictionary):
        """Updates all variables in the expression to their SSA-form according to a dictionary with number of previous assignments of each variable.

        :param expr: (Expression) Expression in which variables will be updated.
        :param dictionary: (dict[str,int]) Contains mapping of variables base names to number of their previous assignments, e.g. {'x': 0, 'y': 2}. If variable is not in the dictionary than it is treated as occurring for the first time.
        :return: Nothing. Works in place on the provided expression.
        """
        if type(expr) is Var:
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
                self.update_expr(e, dictionary)

        else: # for constants
            pass


    def mark_var(self, base_id, num):
        if self.ssa_mark_indexed:
            return self.mark_var_indexed(base_id, num)
        else:
            return self.mark_var_quoted(base_id, num)


    def mark_var_quoted(self, base_id, num):
        """Returns a new name of the variable with added 'num' markers at the end of
         the variable. Apostrophe is not allowed in simple symbols in SMT-LIB 2.0,
         so variable names with ' must be quoted symbols (marked with '|' at the ends).
        """
        if num == 0:
            return base_id
        name = base_id + (self.ssa_marker * num)
        if (num > 0 and self.ssa_quote_marked_vars) or \
           (num == 0 and self.ssa_quote_unmarked_vars):
            return '|' + name + '|'
        else:
            return name


    def mark_var_indexed(self, base_id, num):
        """Returns a new name of the variable with added marker and then index at the
         end of the variable. Apostrophe is not allowed in simple symbols in SMT-LIB 2.0,
         so variables names must be quoted symbols (marked with '|' at the ends).
        """
        if num == 0:
            return base_id
        name = base_id + self.ssa_marker + str(num)
        if self.ssa_quote_marked_vars:
            return '|' + name + '|'
        else:
            return name


    def actual_var_id(self, base_id, dictionary):
        if base_id in dictionary:
            return self.mark_var(base_id, dictionary[base_id] - 1)
        else:
            return base_id





class StatsIf(object):

    def __init__(self, if_instr):
        self.body = StatsBlock(if_instr.body)
        self.orelse = StatsBlock(if_instr.orelse)
        self.vars_dict = self.body.vars_dict.copy()
        self.vars_dict.update(self.orelse.vars_dict)



class StatsBlock(object):

    def __init__(self, ib):
        self.base_var_ids = []
        self.assigned_unique_vars = []
        self.assigned_vars = []
        self.vars_dict = {}

        for instr in ib.instructions:
            if instr.in_type is Instruction.IF:
                pass # TODO: handle ifs in instruction blocks
            elif instr.in_type is Instruction.ASSIGN:
                self.add_var_to_list(instr.var)
                self.update_vars_dict(instr.var)

    def add_var_to_list(self, var):
        for v in self.assigned_vars:
            if var.id == v.id:
                return
        self.assigned_vars.append(var)
        self.base_var_ids.append(var.base_id)

    def update_vars_dict(self, var):
        base_id = var.base_id
        if base_id in self.vars_dict:
            self.vars_dict[base_id] += 1
        else:
            self.vars_dict[base_id] = 1

    # def base(self, var_id):
    #     return var_id.replace("'", "")

    def update_unique_vars(self, var_list):
        for uv in var_list:
            if uv not in self.assigned_vars:
                self.assigned_vars.append(uv)




def convert(ib, post, program_vars, ssa_quote_marked_vars = True, ssa_quote_unmarked_vars = False,
            ssa_mark_indexed = False):
    """Returns an instruction block and postcondition converted to SSA (Single
    Static Assignment) form. This function acts as a wrapper for ConverterSSA object.

    :param ib: (ProgramInterm) instruction block representing the whole program.
    :param post: (Expression) expression representing a postcondition.
    :param program_vars: (ProgramVars) information about variables and their types.
    :return: A tuple containing the SSA form of the given program (block of instructions) and postcondition.
    """
    assert isinstance(program_vars, contract.ProgramVars)
    assert isinstance(ib, ProgramInterm)
    assert isinstance(post, Expression)

    ssa_conv = ConverterSSA(ssa_quote_marked_vars = ssa_quote_marked_vars,
                            ssa_quote_unmarked_vars = ssa_quote_unmarked_vars,
                            ssa_mark_indexed=ssa_mark_indexed)
    # Converting program's body.
    src_ib_ssa, assign_index = ssa_conv.convert(ib.src, program_vars)
    # Converting postcondition.
    ssa_conv.update_expr(post, assign_index)

    utils.logger.debug('------------------------------')
    utils.logger.debug('SSA form:')
    utils.logger.debug('------------------------------')
    utils.logger.debug(str(src_ib_ssa))

    return ProgramInterm(src_ib_ssa), post



def convert_ib(ib, program_vars, ssa_quote_marked_vars = True, ssa_quote_unmarked_vars = False,
               ssa_mark_indexed = False):
    """Returns an instruction block converted to SSA (Single Static
     Assignment) form. This function acts as a wrapper for ConverterSSA object.

    :param ib: (ProgramInterm) instruction block representing the whole program.
    :param program_vars: (ProgramVars) information about variables and their types.
    :return: (ProgramInterm) the SSA form of the given program.
    """
    assert isinstance(program_vars, contract.ProgramVars)
    assert isinstance(ib, ProgramInterm)

    ssa_conv = ConverterSSA(ssa_quote_marked_vars = ssa_quote_marked_vars,
                            ssa_quote_unmarked_vars = ssa_quote_unmarked_vars,
                            ssa_mark_indexed=ssa_mark_indexed)
    src_ib_ssa, assign_index = ssa_conv.convert(ib.src, program_vars)

    utils.logger.debug('------------------------------')
    utils.logger.debug('SSA form:')
    utils.logger.debug('------------------------------')
    utils.logger.debug(str(src_ib_ssa))

    return ProgramInterm(src_ib_ssa)