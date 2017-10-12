from pysv import ast_utils
from pysv import ssa_converter
from pysv import utils
from pysv.smt2 import ProgramSmt2


def get_code_in_smt2(code, code_pre, code_post, program_vars, env, holes_decls = None):
    """Converts source codes of specification elements into program in SMT-LIB 2.0 language.

    :param code: (str) Source code (in arbitrary language) of the program.
    :param code_pre: (str) Source code (in arbitrary language) of the expression representing all *pre-conditions*.
    :param code_post: (str) Source code (in arbitrary language) of the expression representing all *post-conditions*.
    :param program_vars: (ProgramVars) Information about variables and their types.
    :param env: (Options) Options of the currently realized task.
    :param holes_decls: (list[HoleDecl]) Declarations of all holes in the case of synthesis scenario.
    :return: (ProgramSmt2) Program in the SMT-LIB 2.0 language.
    """
    if env.lang == utils.Options.PYTHON:
        return convert_py_to_smt2(code, code_pre, code_post, program_vars, env, holes_decls)
    elif env.lang == utils.Options.SMT2:
        main = ProgramSmt2(processHoles(code, holes_decls))
        return main, ProgramSmt2(code_pre), ProgramSmt2(code_post)
    else:
        raise Exception(str(env.lang) + ": unsupported language!")


def processHoles(code, holes_decls):
    """Finds all hole symbols in the SMT-LIB code of the program and replaces them with
    appropriate references to their synthesis functions. Does nothing in case of
    verification.

    :param code: (str) Source code (in arbitrary language) of the program.
    :param holes_decls: (list[HoleDecl]) Declarations of all holes.
    :return: (str) Source code with SMT replacement of holes by appropriate functions.
    """
    if holes_decls is None or len(holes_decls) == 0:
        return code
    else:
        code = code.replace(")", " )")
        for h in holes_decls:
            if h.id in code:
                code = code.replace(h.id+" ", h.get_function_call()+" ")
        return code


def convert_py_to_smt2(code, code_pre, code_post, program_vars, env, holes_decls):
    # Python source code --> internal abstract program representation.
    ib, pre, post = ast_utils.process_source_code(code, code_pre, code_post, holes_decls)
    utils.logger.debug('\n\n******** PROGRAM REPR ********:\n' + str(ib))

    # Abstract program representation --> abstract program representation in SSA form.
    if env.ssa_enabled:
        ib, post = ssa_converter.convert(ib, post, program_vars)
        program_vars.add_marked_variables(ib.src.collect_variables())  # Updating variable list

    # Producing SMT-LIB code for program's elements.
    ib_smt2 = ib.to_smt2(env)
    pre_smt2 = pre.to_smt2(env)
    post_smt2 = post.to_smt2(env)
    return ib_smt2, pre_smt2, post_smt2


def write_script_to_file(script, env):
    if env.save_script_to_file:
        with open('script.smt2', 'w') as file_:
            file_.write(script)