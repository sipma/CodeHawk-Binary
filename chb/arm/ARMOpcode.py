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
"""ARM opcodes."""

from typing import List, Tuple, TYPE_CHECKING

import chb.arm.ARMOpcodeBase as X

if TYPE_CHECKING:
    import chb.arm.ARMDictionary

arm_opcode_constructors = {
    "ADD": lambda x: ARMAdd(*x)
    }


def get_arm_opcode(
        tag: str,
        args: Tuple["chb.arm.ARMDictionary.ARMDictionary",
                    int,
                    List[str],
                    List[int]]) -> X.ARMOpcodeBase:
    if tag in arm_opcode_constructors:
        return arm_opcode_constructors[tag](args)
    else:
        return X.ARMOpcodeBase(*args)


class ARMAdd(X.ARMOpcodeBase):

    def __init__(
            self,
            d: "chb.arm.ARMDictionary.ARMDictionary",
            index: int,
            tags: List[str],
            args: List[int]) -> None:
        X.ARMOpcodeBase.__init__(self, d, index, tags, args)

    def get_operands(self):
        return [self.d.get_arm_operand(i) for i in self.args[1:]]
