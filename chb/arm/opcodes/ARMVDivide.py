# ------------------------------------------------------------------------------
# CodeHawk Binary Analyzer
# Author: Henny Sipma
# ------------------------------------------------------------------------------
# The MIT License (MIT)
#
# Copyright (c) 2021-2022 Aarno Labs LLC
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

from typing import List, Tuple, TYPE_CHECKING

from chb.app.InstrXData import InstrXData

import chb.ast.ASTNode as AST
from chb.astinterface.ASTInterface import ASTInterface

from chb.arm.ARMDictionaryRecord import armregistry
from chb.arm.ARMOpcode import ARMOpcode, simplify_result
from chb.arm.ARMOperand import ARMOperand

import chb.invariants.XXprUtil as XU

import chb.util.fileutil as UF

from chb.util.IndexedTable import IndexedTableValue

if TYPE_CHECKING:
    from chb.arm.ARMDictionary import ARMDictionary


@armregistry.register_tag("VDIV", ARMOpcode)
class ARMVDivide(ARMOpcode):
    """Divides one floating point value by another floating point value.

    tags[1]: <c>
    args[0]: index of datatype in armdictionary
    args[1]: index of destination in armdictionary
    args[2]: index of source 1 in armdictionary
    args[3]: index of source 2 in armdictionary
    """

    def __init__(
            self,
            d: "ARMDictionary",
            ixval: IndexedTableValue) -> None:
        ARMOpcode.__init__(self, d, ixval)
        self.check_key(2, 4, "VDivide")

    @property
    def operands(self) -> List[ARMOperand]:
        return [self.armd.arm_operand(self.args[i]) for i in [1, 2, 3]]

    @property
    def opargs(self) -> List[ARMOperand]:
        return [self.armd.arm_operand(self.args[i]) for i in [1, 2, 3]]

    def annotation(self, xdata: InstrXData) -> str:
        return (
            str(xdata.vars[0])
            + " := "
            + str(xdata.xprs[0])
            + " / "
            + str(xdata.xprs[1]))

    def ast_prov(
            self,
            astree: ASTInterface,
            iaddr: str,
            bytestring: str,
            xdata: InstrXData) -> Tuple[
                List[AST.ASTInstruction], List[AST.ASTInstruction]]:

        annotations: List[str] = [iaddr, "VDIV"]

        lhs = xdata.vars[0]
        rhs1 = xdata.xprs[0]
        rhs2 = xdata.xprs[1]
        rdefs = xdata.reachingdefs
        defuses = xdata.defuses
        defuseshigh = xdata.defuseshigh

        (ll_lhs, _, _) = self.opargs[0].ast_lvalue(astree)
        (ll_rhs1, _, _) = self.opargs[1].ast_rvalue(astree)
        (ll_rhs2, _, _) = self.opargs[2].ast_rvalue(astree)
        ll_result = astree.mk_binary_op("div", ll_rhs1, ll_rhs2)
        ll_assign = astree.mk_assign(
            ll_lhs,
            ll_result,
            iaddr=iaddr,
            bytestring=bytestring,
            annotations=annotations)

        hl_lhss = XU.xvariable_to_ast_lvals(lhs, xdata, astree)
        hl_rhss1 = XU.xxpr_to_ast_def_exprs(rhs1, xdata, iaddr, astree)
        hl_rhss2 = XU.xxpr_to_ast_def_exprs(rhs2, xdata, iaddr, astree)
        if len(hl_lhss) == 1 and len(hl_rhss1) == 1 and len(hl_rhss2) == 1:
            hl_lhs = hl_lhss[0]
            hl_rhs1 = hl_rhss1[0]
            hl_rhs2 = hl_rhss2[0]
            hl_result = astree.mk_binary_op("div", hl_rhs1, hl_rhs2)
            hl_assign = astree.mk_assign(
                hl_lhs,
                hl_result,
                iaddr=iaddr,
                bytestring=bytestring,
                annotations=annotations)

            astree.add_reg_definition(iaddr, hl_lhs, hl_result)
            astree.add_instr_mapping(hl_assign, ll_assign)
            astree.add_instr_address(hl_assign, [iaddr])
            astree.add_expr_mapping(hl_rhs1, ll_rhs1)
            astree.add_expr_mapping(hl_rhs2, ll_rhs2)
            astree.add_lval_mapping(hl_lhs, ll_lhs)
            astree.add_expr_reachingdefs(ll_rhs1, [rdefs[0]])
            astree.add_expr_reachingdefs(ll_rhs2, [rdefs[1]])
            astree.add_expr_reachingdefs(hl_result, rdefs[2:])
            astree.add_lval_defuses(hl_lhs, defuses[0])
            astree.add_lval_defuses_high(hl_lhs, defuseshigh[0])

            return ([hl_assign], [ll_assign])

        else:
            raise UF.CHBError(
                "VDivide (VDIV): multiple lval/expressions in ast")
