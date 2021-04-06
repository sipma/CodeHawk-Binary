# ------------------------------------------------------------------------------
# CodeHawk Binary Analyzer
# Author: Henny Sipma
# ------------------------------------------------------------------------------
# The MIT License (MIT)
#
# Copyright (c) 2021 Aarno Labs LLC
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
"""Operand of an ARM assembly instruction."""


from typing import List, TYPE_CHECKING

import chb.arm.ARMDictionaryRecord as D
import chb.arm.ARMOperandKind as K

if TYPE_CHECKING:
    import chb.arm.ARMDictionary


class ARMOperand(D.ARMDictionaryRecord):

    def __init__(
            self,
            d: "chb.arm.ARMDictionary.ARMDictionary",
            index: int,
            tags: List[str],
            args: List[int]) -> None:
        D.ARMDictionaryRecord.__init__(self, d, index, tags, args)

    @property
    def arm_opkind(self) -> K.ARMOperandKind:
        return self.d.get_arm_opkind(self.args[0])

    def __str__(self) -> str:
        return str(self.arm_opkind)