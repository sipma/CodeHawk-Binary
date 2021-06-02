# ------------------------------------------------------------------------------
# CodeHawk Binary Analyzer
# Author: Henny Sipma
# ------------------------------------------------------------------------------
# The MIT License (MIT)
#
# Copyright (c) 2016-2020 Kestrel Technology LLC
# Copyright (c) 2020      Henny Sipma
# Copyright (c) 2021      Aarno Labs LLC
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

from typing import cast, List, TYPE_CHECKING

from chb.app.InstrXData import InstrXData

from chb.invariants.XXpr import XXpr

import chb.util.fileutil as UF

from chb.util.IndexedTable import IndexedTableValue

from chb.x86.X86DictionaryRecord import x86registry
from chb.x86.X86Opcode import X86Opcode
from chb.x86.X86Operand import X86Operand

if TYPE_CHECKING:
    from chb.x86.X86Dictionary import X86Dictionary
    

@x86registry.register_tag("jmp*", X86Opcode)
class X86IndirectJmp(X86Opcode):
    """JMP op

    args[0]: index of op in x86dictionary
    """

    def __init__(
            self,
            x86d: "X86Dictionary",
            ixval: IndexedTableValue) -> None:
        X86Opcode.__init__(self, x86d, ixval)

    @property
    def operand(self) -> X86Operand:
        return self.x86d.get_operand(self.args[0])

    def get_operands(self) -> List[X86Operand]:
        return [self.operand]

    def is_indirect_jump(self) -> bool:
        return True

    # xdata: [ "a:xx": tgtop, tgtop-simplified ]
    def get_annotation(self, xdata: InstrXData) -> str:
        """data format a:xxi or a:xx or a:x .

        xprs[0]: target
        xprs[1]: target (simplified)
        """
        
        if len(xdata.xprs) == 1:
            tgtop = str(xdata.xprs[0])
            return 'jmp*  ' + tgtop
        elif len(xdata.xprs) == 2:
            tgtop = str(xdata.xprs[0])
            vx = str(xdata.xprs[1])
            reg = self.bd.get_register(xdata.args[2])
            base = self.bd.get_address(xdata.args[3])
            return str(reg) + ' ' + str(base)
        elif len(xdata.xprs) == 3:
            '''
            tgtop = str(xdata.xprs[0])
            vx = str(xdata.xprs[1])
            rng = str(xdata.xprs[2])
            reg = self.bd.get_register(xargs[3])
            base = str(self.bd.get_address(xargs[4]))
            if self.app.has_jump_table(base):
                jt = self.app.get_jump_table(base)
                tgts = jt.get_targets()
                ptgts = (vx + ': '
                             +  ','.join([ '(' + str(i) + ':' + str(t) + ')'
                                               for (i,t) in enumerate(tgts) ]))
                return ptgts
            return '++++' + str(rng)  + '  ' + str(reg) + '  ' +  str(base)
            '''
            return "jmp* ?"
        else:
            return 'jmp* ?'

    def get_targets(self, xdata: InstrXData) -> List[str]:
        '''
        if len(xprs) == 2:
            base = self.bd.get_address(xargs[3])
        elif len(xprs) == 3:
            base = self.bd.get_address(xargs[4])
        else:
            raise UF.CHBError('No jumptable targets available')
        if self.app.has_jump_table(base):
            jt = self.app.get_jump_table(str(base))
            return jt.get_targets()
        '''
        raise UF.CHBError('Jumptable not found')

    def get_selector_expr(self, xdata: InstrXData) -> XXpr:
        if len(xdata.xprs) == 2:
            return xdata.xprs[1]
        else:
            raise UF.CHBError('Selector expression not found')
