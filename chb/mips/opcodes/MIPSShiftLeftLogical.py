# ------------------------------------------------------------------------------
# CodeHawk Binary Analyzer
# Author: Henny Sipma
# ------------------------------------------------------------------------------
# The MIT License (MIT)
#
# Copyright (c) 2016-2020 Kestrel Technology LLC
# Copyright (c) 2020-2021 Henny Sipma
# Copyright (c) 2021-2023 Aarno Labs LLC
#
# Permission is hereby granted, free of charge, to any person obtaining a copy
# of this software and associated documentation files (the "Software"), to deal
# in the Software without restriction, including without limitation the rights
# to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
# copies of the Software, and to permit persons to whom the Software is
# furnished to do so, subject to the following conditions:
#
# The above copyright notice and this permission notice shall be included in all
# copies or substantial portions of the Software.
#
# THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
# IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
# FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
# AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
# LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
# OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
# SOFTWARE.
# ------------------------------------------------------------------------------

from typing import cast, List, Sequence, TYPE_CHECKING

from chb.app.InstrXData import InstrXData

import chb.ast.ASTNode as AST
from chb.astinterface.ASTInterface import ASTInterface

from chb.invariants.XXpr import XXpr
import chb.invariants.XXprUtil as XU

from chb.mips.MIPSDictionaryRecord import mipsregistry
from chb.mips.MIPSOpcode import MIPSOpcode, simplify_result
from chb.mips.MIPSOperand import MIPSOperand

import chb.simulation.SimSymbolicValue as SSV
import chb.simulation.SimUtil as SU
import chb.simulation.SimValue as SV

import chb.util.fileutil as UF

from chb.util.IndexedTable import IndexedTableValue

if TYPE_CHECKING:
    from chb.mips.MIPSDictionary import MIPSDictionary
    from chb.simulation.SimulationState import SimulationState


@mipsregistry.register_tag("sll", MIPSOpcode)
class MIPSShiftLeftLogical(MIPSOpcode):
    """SLL rd, rt, sa

    Shift Word Left Logical.
    Left-shift a word by a fixed number of bits.

    args[0]: index of rd in mips dictionary
    args[1]: index of rt in mips dictionary
    args[2]: index of sa in mips dictionary
    """

    def __init__(
            self,
            mipsd: "MIPSDictionary",
            ixval: IndexedTableValue) -> None:
        MIPSOpcode.__init__(self, mipsd, ixval)

    @property
    def operands(self) -> Sequence[MIPSOperand]:
        return [self.mipsd.mips_operand(i) for i in self.args]

    def annotation(self, xdata: InstrXData) -> str:
        """data format a:vxxx

        vars[0]: lhs
        xprs[0]: rhs (rt)
        xprs[1]: rhs (sa)
        xprs[2]: rhs * 2^sa (syntactic)
        xprs[3]: rhs * 2^sa (simplified)
        """

        lhs = str(xdata.vars[0])
        result = xdata.xprs[2]
        rresult = xdata.xprs[3]
        xresult = simplify_result(xdata.args[3], xdata.args[4], result, rresult)
        return lhs + ' := ' + xresult

    def ast(
            self,
            astree: ASTInterface,
            iaddr: str,
            bytestring: str,
            xdata: InstrXData) -> List[AST.ASTInstruction]:
        lhss = XU.xvariable_to_ast_lvals(xdata.vars[0], xdata, astree)
        rhss = XU.xxpr_to_ast_exprs(xdata.xprs[2], xdata, iaddr, astree)
        if len(lhss) == 1 and len(rhss) == 1:
            lhs = lhss[0]
            rhs = rhss[0]
            assign = astree.mk_assign(lhs, rhs)
            astree.add_instruction_span(assign.locationid, iaddr, bytestring)
            return [assign]
        else:
            raise UF.CHBError(
                "MIPSShiftLeftLogical: multiple expressions/lvals in ast")

    @property
    def dst_operand(self) -> MIPSOperand:
        return self.mipsd.mips_operand(self.args[0])

    @property
    def src_operand(self) -> MIPSOperand:
        return self.mipsd.mips_operand(self.args[1])

    @property
    def imm_operand(self) -> MIPSOperand:
        return self.mipsd.mips_operand(self.args[2])

    # --------------------------------------------------------------------------
    # Operation:
    #   s <- sa
    #   temp <- GPR[rt][31-s..0] || 0[s]
    #   GPR[rd] <- temp
    # --------------------------------------------------------------------------
    def simulate(self, iaddr: str, simstate: "SimulationState") -> str:
        dstop = self.dst_operand
        srcop = self.src_operand
        immop = self.imm_operand
        srcval = simstate.rhs(iaddr, srcop)
        immval = immop.opkind.to_unsigned_int()

        if srcval.is_undefined:
            result = cast(SV.SimValue, SV.simUndefinedDW)
            simstate.add_logmsg(
                "warning",
                "sll: operand is not defined: " + str(srcop))

        elif srcval.is_literal:
            v = SV.mk_simvalue(srcval.literal_value)
            result = v.bitwise_sll(immval)

        elif srcval.is_symbol:
            srcval = cast(SSV.SimSymbol, srcval)
            if srcval.value is not None:
                v = SV.mk_simvalue(srcval.value)
                result = v.bitwise_sll(immval)

            else:
                raise SU.CHBSymbolicExpression(
                    simstate,
                    iaddr,
                    dstop,
                    str(srcval) + " << " + str(immval) + " (val(" + str(srcop) + "))")

        else:
            result = SV.simUndefinedDW
            simstate.add_logmsg(
                "warning",
                "sll: operand not recognized: " + str(srcval))

        lhs = simstate.set(iaddr, dstop, result)
        simstate.increment_programcounter()
        return SU.simassign(
            iaddr,
            simstate,
            lhs,
            result,
            "(val(" + str(srcop) + ") = " + str(srcval) + ")")
