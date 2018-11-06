import copy
from .interm import *


def unroll_loops(ib, n=5):
    """Returns instruction block with all while instructions unrolled."""
    assert isinstance(ib, InstrBlock)
    for i, ins in enumerate(ib.instructions):
        if isinstance(ins, InstrWhile):
            ib.instructions[i] = unroll_while_instr(ins, n=n)
    return ib


def unroll_while_instr(while_instr, n=5):
    """Unrolls a single while instruction by producing a nested if-instruction."""
    assert isinstance(while_instr, InstrWhile)
    assert isinstance(n, int) and n > 0
    body = []
    orelse = []
    while_cond = copy.deepcopy(while_instr.condition)
    while_body = copy.deepcopy(while_instr.body)
    if n == 1:
        body.append(while_body)
        orelse.append(InstrAssert(Op("not", [while_cond])))
    else:
        body.append(while_body)
        body.append(unroll_while_instr(while_cond, n=n-1))
    return InstrIf(while_cond, body, orelse)
