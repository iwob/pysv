import copy
from pysv.interm import *
from pysv import contract
from pysv import utils

class ConverterSSA(object):
    """ConverterSSA is used to convert instruction block to the SSA form, in which every new assignment to a variable is equivalent with creating new ("marked") version of this variable. SSA form is necessary in the context of SMT verification and synthesis because of representing a program in the form of logical formulas.


    TODO:
    - Currently every assignment results in creating marked variable, even if this is the first use of this variable. It is important to note that if certain variable is present in the precondition, then indeed it's first program assignment must be marked to avoid errors.

    Attributes:
    -----------
    :param ssa_marker: (str) Marker being added on the end of a variable name to mark subsequent assignments. (default="'")
    :param ssa_quote_marked_vars: (bool) Specifies, if ssa-marked variables should be quoted with |, a special symbol in SMT-LIB. (default=True)
    :param ssa_quote_unmarked_vars: (bool) Specifies, if normal (unmarked) variables should be quoted (for aesthetic reasons). (default=False)
    """

    def __init__(self, ssa_marker = "'", ssa_quote_marked_vars = True, ssa_quote_unmarked_vars = False):
        self.ssa_marker = ssa_marker
        self.ssa_quote_marked_vars = ssa_quote_marked_vars
        self.ssa_quote_unmarked_vars = ssa_quote_unmarked_vars

    # ib: InstructionBlock; old_id, new_id: String, start_from: Int.
    # def update_future_references(self, ib, old_id, new_id, start_from = 0):
    #     """Changes a name of the given variable starting from the specified instruction in the block."""
    #     for i in range(start_from, len(ib.instructions)):
    #         instr = ib.instructions[i]
    #         instr.rename_var(old_id, new_id)

    # main_assign_nums and its copies store for example 'y':2, where 2 means, that next assignment to y will be
    # marked with 2 markers (in other words, y was assigned 2 times before and versions y and y' exist).


    def convert(self, main_ib_0, program_vars):
        """Returns new instruction block and postcondition converted to SSA (Single Static Assignment) form.

        ISSUES:\n
        - all variables are treated as global. Local variables in for example 'if' bodies lead to errors if
        those variables were not declared before 'if'.

        :param main_ib_0: instruction block representing the whole program.
        :param program_vars: ProgramVars object containing information about variables and their types.
        :return: A tuple containing the SSA form of the given program (block of instructions) and postcondition.
        """
        assert type(main_ib_0) == InstrBlock
        assert type(program_vars) == contract.ProgramVars

        main_ib = copy.deepcopy(main_ib_0)
        main_assign_nums = {v: 1 for v in program_vars.input_vars}


        def convert_instr_block(ib, parent_assign_nums):
            assert(type(ib) == InstrBlock)
            local_assign_nums = parent_assign_nums.copy()
            # local_assign_nums is to be appropriately updated for every instruction
            for i in range(len(ib.instructions)):
                instr = ib.instructions[i]
                # print('(SSA) processing instr: '+str(instr))
                t = type(instr)
                if t is InstrAssign:
                    convert_instr_assign(instr, ib, i, local_assign_nums)
                    # print('local after InstrAssign: '+str(local_assign_nums))
                elif t is InstrIf:
                    convert_instr_if(instr, local_assign_nums)
                    # print('local after InstrIf: '+str(local_assign_nums))
                elif len(instr.instruction_blocks) > 0: # other instruction with >0 contained blocks
                    for instr_block in instr.instruction_blocks:
                        convert_instr_block(instr_block, local_assign_nums)

        def convert_instr_assign(instr, ib, instr_num, parent_assign_nums):
            assert(type(instr) == InstrAssign)
            # Converting expression part
            self.update_expr(instr.expr, parent_assign_nums)

            # Converting variable part
            x = instr.var.base_id
            inc_assign_num(x, main_assign_nums) # updated is global variable dict
            update_dictionary(parent_assign_nums, x, main_assign_nums[x]) # for further occurrences of variable in block.
            if main_assign_nums[x] > 1: # not the first (initial) assignment to a variable
                new_id = self.mark_var(x, main_assign_nums[x]-1)
                instr.var.id = new_id
                #TODO: update references also in block containing this block
                #self.update_future_references(ib, x, new_id, instr_num+1)

        def convert_instr_if(instr, parent_assign_nums):
            assert (type(instr) == InstrIf)
            dict_before_if = parent_assign_nums.copy()

            # Converting condition part
            self.update_expr(instr.condition, parent_assign_nums)

            # Converting both body blocks of IF. Copy of parent_assign_nums dict will be made inside.
            # print('BODY BRANCH')
            convert_instr_block(instr.body, parent_assign_nums)
            # print('ORELSE BRANCH')
            convert_instr_block(instr.orelse, parent_assign_nums)

            # Balancing (leveling) IF branches.
            balance_var_level_if(instr, dict_before_if)

            # Finding meta instructions containing if-leveling and updating parent assigns dict.
            # These meta-instructions contain all information needed to update parent assignments.
            for i in instr.body.instructions:
                if i.is_meta and i.in_type is Instruction.ASSIGN:
                    num = i.var.id.count("'") + 1
                    update_dictionary(main_assign_nums, i.var.base_id, num)
                    update_dictionary(parent_assign_nums, i.var.base_id, num)



        def inc_assign_num(base_id, dictionary):
            """Updates dictionary with the number of subsequent assignments per variable name.

            :param base_id: base ID of a variable which was assigned to, so it's counter
            needs to be incremented.
            :param dictionary
            """
            if base_id in dictionary:
                dictionary[base_id] += 1
            else:
                dictionary[base_id] = 1

        def update_dictionary(dictionary, base_id, new_val):
            """Updates dictionary with the number of subsequent assignments per variable name.

            :param base_id: base ID of a variable which was assigned to, so it's counter needs to be incremented.
            :param dictionary:
            :param new_val:
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
            :param dict_before_if: Dictionary containing number of previous assignments to variables before this if-instruction.
            :return: Nothing. Updates 'instr' in place.
            """
            s = StatsIf(instr)
            for v in sorted(s.vars_dict.keys()):
                level = main_assign_nums[v]
                balance_var_level(instr, v, level, dict_before_if)

        # if_instr: InstrIf, varid: String, nl: Int, stats: StatsIf
        def balance_var_level(if_instr, base_id, level, dict_before_if):
            """Adds meta-instructions for blocks of IF which will introduce a "shared variable" in
            both blocks (similar concept to phi function in SSA form).

            :param if_instr:
            :param base_id: original name of the variable (without "time" markers).
            :param level: exact level of shared variable.
            :param dict_before_if: Dictionary containing number of previous assignments to variables before this if-instruction.
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


        convert_instr_block(main_ib, main_assign_nums)
        return  main_ib, main_assign_nums


    def update_expr(self, expr, dictionary):
        """Updates all variables in the expression to their SSA-form according to a dictionary with number of previous assignments of each variable.

        :param expr: (Expression) Expression in which variables will be updated.
        :param dictionary: (dict[str,int]) Contains mapping of variables base names to number of their previous assignments, e.g. {'x': 0, 'y': 2}. If variable is not in the dictionary than it is treated as occurring for the first time.
        :return: Nothing. Works in place on the provided expression.
        """
        if type(expr) is Var:
            expr.id = self.actual_var_id(expr.base_id, dictionary)
        elif type(expr) is ExprHole:
            # Updating variables dictionary for a hole
            for v in expr.hole_decl.vars:
                var_type = expr.hole_decl.vars[v]
                del expr.hole_decl.vars[v]
                new_id = self.actual_var_id(Var.base_id(v), dictionary)
                expr.hole_decl.vars[new_id] = var_type
        elif type(expr) is Op:
            for e in expr.args:
                self.update_expr(e, dictionary)
        else: # for constants
            pass


    def mark_var(self, base_id, num):
        """Returns a new name of the variable with added 'num' markers at the end of the variable.
        Apostrophe is not allowed in simple symbols in SMT-LIB 2.0, so variable names with ' must
        be quoted symbols (marked with '|' at the ends).
        """
        name = base_id + (self.ssa_marker * num)
        if (num > 0 and self.ssa_quote_marked_vars) or \
           (num == 0 and self.ssa_quote_unmarked_vars):
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




def convert(ib, post, program_vars):
    """Returns new instruction block and postcondition converted to SSA (Single Static Assignment) form.
    This function acts as a wrapper for ConverterSSA object.

    :param ib: (ProgramInterm) instruction block representing the whole program.
    :param post: (ProgramInterm) expression instruction for postcondition.
    :param program_vars: ProgramVars object containing information about variables and their types.
    :return: A tuple containing the SSA form of the given program (block of instructions) and postcondition.
    """
    assert isinstance(program_vars, contract.ProgramVars)
    assert isinstance(ib, ProgramInterm)
    assert isinstance(post, Expression)

    ssa_conv = ConverterSSA()
    # Converting program's body.
    src_ib_ssa, dict_assign_nums = ssa_conv.convert(ib.src, program_vars)
    # Converting postcondition.
    ssa_conv.update_expr(post, dict_assign_nums)

    utils.logger.debug('------------------------------')
    utils.logger.debug('SSA form:')
    utils.logger.debug('------------------------------')
    utils.logger.debug(str(src_ib_ssa))

    return ProgramInterm(src_ib_ssa), post
