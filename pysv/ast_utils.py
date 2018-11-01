import sys
import ast
from pysv.interm import *


# info_data = ast.literal_eval(info_string) - can be used to evaluate arbitrary python code.


class ASTToInstrBlockConverter(ast.NodeVisitor):
    """ASTToInstrBlockConverter is able to convert python AST into high-level logical program representation used in this framework."""
    instr_block = InstrBlock([])

    def __init__(self, holes_decls = None):
        if holes_decls is None:
            holes_decls = {}
        elif type(holes_decls) == list:
            holes_decls = {h.id: h for h in holes_decls}
        self.holes_decls = holes_decls

    def my_visit(self, node):
        """Returns a list of instructions of the given AST node."""
        if type(node) == ast.Module:
            res = [] # list of instructions
            for b in node.body:
                res = res + self.my_visit_internal(b)
            return res
        else:
            raise Exception('Provided object of class ' + str(type(node)) + ' is not a Module instance!')


    def my_visit_internal(self, node):
        """Returns a list of instructions of the given AST node."""
        # print('[mv] ' + ast.dump(node))
        t = type(node)
        if t == ast.Assign:
            var = Var(node.targets[0].id) # TODO: check what if there are several targets
            expr = ASTExprConverter.create_expr(node.value, self.holes_decls)
            instr = InstrAssign(var, expr)
            return [instr]

        if t == ast.AugAssign:
            var1 = Var(node.target.id)
            var2 = Var(node.target.id)
            opid = ""
            if isinstance(node.op, ast.Add):
                opid = "+"
            elif isinstance(node.op, ast.Sub):
                opid = "-"
            elif isinstance(node.op, ast.Mult):
                opid = "*"
            elif isinstance(node.op, ast.Div):
                opid = "/"
            elif isinstance(node.op, ast.Mod):
                opid = "mod"
            else:
                raise Exception("Unknown operand in python augmented assignment. Supported: '+=', '-=', '*=', '/=', '%='.")
            expr = ASTExprConverter.create_expr(node.value, self.holes_decls)
            instr = InstrAssign(var1, Op(opid, [var2, expr]))
            return [instr]

        elif t == ast.While:
            cond = ASTExprConverter.create_expr(node.test, self.holes_decls)
            body = InstrBlock([])
            for b in node.body:
                body.instructions += self.my_visit_internal(b)
            instr = InstrWhile(cond, body)
            return [instr]

        elif t == ast.If:
            cond = ASTExprConverter.create_expr(node.test, self.holes_decls)
            body = InstrBlock([])
            for b in node.body:
                body.instructions += self.my_visit_internal(b)
            orelse = InstrBlock([])
            for b in node.orelse:
                orelse.instructions += self.my_visit_internal(b)
            instr = InstrIf(cond, body, orelse)
            return [instr]

        elif t == ast.Expr:
            expr = ASTExprConverter.create_expr(node.value, self.holes_decls)
            if expr.is_hole:
                return [InstrHole(expr.hole_decl)]
            else:
                return [expr]

        elif t == ast.Assert:
            expr = ASTExprConverter.create_expr(node.test, self.holes_decls)
            return [InstrAssert(expr)]

        else:
            print('NODE: '+str(node)+' (not analysed)')
            return []



# ast - AST tree, e.g., created by ast.parse.
def convert_AST_to_instruction_block(ast, holes_decls = None):
    converter = ASTToInstrBlockConverter(holes_decls)
    instrs = converter.my_visit(ast)
    converter.instr_block = InstrBlock(instrs)
    return converter.instr_block

def convert_AST_to_expr(ast):
    """Creates expression from the AST."""
    converter = ASTToInstrBlockConverter()
    instrs = converter.my_visit(ast)
    return instrs[0]

def get_ast(code):
    node = ast.parse(code)
    ast_tree = ast.fix_missing_locations(node) # patching lineno and col_offset attributes
    return ast_tree

def py_to_interm_ib(code, holes_decls = None):
    """Returns an instruction block. The code is first converted to AST and then to internal representation."""
    ast_tree = get_ast(code)
    # print_ast(ast_tree)
    instr_block = convert_AST_to_instruction_block(ast_tree, holes_decls)
    return ProgramInterm(instr_block)

def py_to_interm_expr(code):
    """Returns an instruction containing a simple expression. The code is first converted
     to AST and then to internal representation."""
    ast_tree = get_ast(code)
    # print_ast(ast_tree)
    expr = convert_AST_to_expr(ast_tree)
    assert isinstance(expr, Expression)
    return expr

def print_ast(tree):
    print('AST: ' + str(ast.dump(tree)))

def process_source_code(code, code_pre, code_post, holes_decls = None):
    pre  = py_to_interm_expr(code_pre)
    post = py_to_interm_expr(code_post)
    ib   = py_to_interm_ib(code, holes_decls)
    return ib, pre, post






class ASTExprConverter:
    is_python_3 = sys.version_info.major == 3

    @staticmethod
    def get_id(node):
        """Returns operation identifier for op of a given AST node (e.g. Compare)."""
        t = type(node)
        if t == ast.Compare:
            return ASTExprConverter._get_id(node.ops[0])
        elif t == ast.BinOp or t == ast.BoolOp or t == ast.UnaryOp:
            return ASTExprConverter._get_id(node.op)
        else:
            raise Exception('Unrecognized "function" class: ' + str(type(node)))

    @staticmethod
    def _get_id(op):
        t = type(op)
        if t == ast.And:
            return PythonOperators.op_and
        elif t == ast.Or:
            return PythonOperators.op_or
        elif t == ast.Not:
            return PythonOperators.op_not
        # ------------------------------
        elif t == ast.Eq:
            return PythonOperators.op_eq
        elif t == ast.NotEq:
            return PythonOperators.op_neq
        elif t == ast.Lt:
            return PythonOperators.op_lt
        elif t == ast.LtE:
            return PythonOperators.op_lte
        elif t == ast.Gt:
            return PythonOperators.op_gt
        elif t == ast.GtE:
            return PythonOperators.op_gte
        # ------------------------------
        elif t == ast.Add:
            return PythonOperators.op_add
        elif t == ast.Sub:
            return PythonOperators.op_sub
        elif t == ast.USub:
            return PythonOperators.op_usub
        elif t == ast.Mult:
            return PythonOperators.op_mult
        elif t == ast.Div:
            return PythonOperators.op_div
        elif t == ast.Mod:
            return PythonOperators.op_mod
        elif t == ast.Pow:
            return PythonOperators.op_pow
        else:
            raise Exception('Unrecognized type of comparison function: ' + str(t))

    @staticmethod
    def create_expr(node, holes_decls=None):
        """Creates Expression for a given AST node (e.g. BinOp, BoolOp, Name, Num).

        :param node: Node of the AST tree.
        :param holes_decls: Dictionary of HoleDecl objects, where the keys are hole names.
        :return: Internal logical program representation.
        """
        if holes_decls is None:
            holes_decls = {}
        t = type(node)
        if t == ast.Name:
            # node.ctx here most likely is Load. Generally, ctx tells us in which context name is used.
            if node.id == 'False':
                return ConstBool(False)
            elif node.id == 'True':
                return ConstBool(True)
            elif node.id in holes_decls:
                return ExprHole(holes_decls[node.id])
            else:
                return Var(node.id)
        elif t == ast.Num:
            return ConstInt(node.n)
        elif t == ast.BinOp:
            op_id = ASTExprConverter.get_id(node)
            args = [ASTExprConverter.create_expr(node.left), ASTExprConverter.create_expr(node.right)]
            return Op(op_id, args)
        elif t == ast.UnaryOp:
            op_id = ASTExprConverter.get_id(node)
            args = [ASTExprConverter.create_expr(node.operand)]
            return Op(op_id, args)
        elif t == ast.BoolOp:
            op_id = ASTExprConverter.get_id(node)
            args = [ASTExprConverter.create_expr(val) for val in node.values]
            return Op(op_id, args)
        elif t == ast.Compare:
            op_id = ASTExprConverter.get_id(node)
            args = [ASTExprConverter.create_expr(node.left)]
            for c in node.comparators:
                args.append(ASTExprConverter.create_expr(c))
            return Op(op_id, args)
        elif t == ast.Call:
            fun_name = node.func.id
            args = []
            for val in node.args:
                args.append(ASTExprConverter.create_expr(val))
            return InstrCall(fun_name, args)
        elif ASTExprConverter.is_python_3 and t == ast.NameConstant:
            if str(node.value) == 'False':
                return ConstBool(False)
            elif str(node.value) == 'True':
                return ConstBool(True)
            else:
                raise Exception("Python3 NameConstant with value: " + str(node.value) + ' is not currently supported!')
        else:
            raise Exception('Error: Unrecognized type of AST node!' + str(type(node)))
