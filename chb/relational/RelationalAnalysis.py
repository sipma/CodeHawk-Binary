# ------------------------------------------------------------------------------
# CodeHawk Binary Analyzer
# Author: Henny Sipma
# ------------------------------------------------------------------------------
# The MIT License (MIT)
#
# Copyright (c) 2021 Aarno Labs, LLC
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
"""Compares two binaries."""

from typing import Dict, List, Mapping, Sequence, Tuple, TYPE_CHECKING

from chb.relational.CallgraphMatcher import CallgraphMatcher
from chb.relational.FunctionRelationalAnalysis import FunctionRelationalAnalysis
import chb.util.fileutil as UF

if TYPE_CHECKING:
    from chb.app.AppAccess import AppAccess


class RelationalAnalysis:
    """Establishes relationships between functions in two related binaries.

    A function mapping is established as follows:

    1. If the number of functions is the same in both binaries, it is assumed
       (for now) that their order in both binaries is the same (we are
       dealing with micropatches, and so we don't expect large changes between
       the two binaries). In this case functions are mapped directly by their
       relative position in the binary.

    2. If the number of functions is different in the two binaries, a
       combination of criteria is used to map functions. They get mapped directly
       - if they are at the same address, or
       - if they have identical md5 hash

       For the remaining functions the callgraph is used to determine relationships
       between the functions in each binary, and a function mapping is obtained from
       matching the two call graphs.
    """

    def __init__(
            self,
            app1: "AppAccess",
            app2: "AppAccess",
            faddrs1: List[str] = [],
            faddrs2: List[str] = []) -> None:
        self._app1 = app1
        self._app2 = app2
        if faddrs1:
            self._faddrs1 = sorted(faddrs1)
        else:
            self._faddrs1 = sorted(app1.appfunction_addrs)
        if faddrs2:
            self._faddrs2 = sorted(faddrs2)
        else:
            self._faddrs2 = sorted(app2.appfunction_addrs)
        self._functionmapping: Dict[str, str] = {}  # potentially partial map
        self._functionanalyses: Dict[str, FunctionRelationalAnalysis] = {}
        self._fnmd5s: Dict[str, Tuple[List[str], List[str]]] = {}

    @property
    def app1(self) -> "AppAccess":
        return self._app1

    @property
    def app2(self) -> "AppAccess":
        return self._app2

    @property
    def faddrs1(self) -> Sequence[str]:
        return self._faddrs1

    @property
    def faddrs2(self) -> Sequence[str]:
        return self._faddrs2

    @property
    def fncount1(self) -> int:
        return len(self._faddrs1)

    @property
    def fncount2(self) -> int:
        return len(self._faddrs2)

    @property
    def function_analyses(self) -> Mapping[str, FunctionRelationalAnalysis]:
        if len(self._functionanalyses) == 0:
            for faddr1 in self.faddrs1:
                if faddr1 in self.function_mapping:
                    faddr2 = self.function_mapping[faddr1]
                    fn1 = self.app1.function(faddr1)
                    fn2 = self.app2.function(faddr2)
                    self._functionanalyses[faddr1] = FunctionRelationalAnalysis(
                        self.app1, fn1, self.app2, fn2)
        return self._functionanalyses

    def function_analysis(self, faddr: str) -> FunctionRelationalAnalysis:
        if faddr in self.function_analyses:
            return self.function_analyses[faddr]
        else:
            raise UF.CHBError("Address not found in function relational analyses")

    @property
    def function_mapping(self) -> Mapping[str, str]:
        if len(self._functionmapping) > 0:
            return self._functionmapping
        elif self.fncount1 == self.fncount2:
            result: Dict[str, str] = {}
            diff1 = sorted(set(self.faddrs1) - set(self.faddrs2))
            diff2 = sorted(set(self.faddrs2) - set(self.faddrs1))
            for (faddr1, faddr2) in zip(diff1, diff2):
                result[faddr1] = faddr2
            for faddr1 in self.faddrs1:
                if faddr1 not in result:
                    result[faddr1] = faddr1
            self._functionmapping = result
            return self._functionmapping
        else:
            callgraphmatcher = CallgraphMatcher(
                self.app1,
                self.faddrs1,
                self.app1.callgraph(),
                self.app2,
                self.faddrs2,
                self.app2.callgraph())
            self._functionmapping = callgraphmatcher.function_mapping

        return self._functionmapping

    def functions_changed(self) -> List[str]:
        """Return a list of functions that moved or are not md5-equivalent."""

        result: List[str] = []
        for (faddr, fra) in self.function_analyses.items():
            if fra.moved or not fra.is_md5_equal:
                result.append(faddr)

        for faddr in self.faddrs1:
            if faddr not in self.function_mapping:
                result.append(faddr)

        return result

    def blocks_changed(self, faddr: str) -> List[str]:
        if faddr in self.function_analyses:
            fra = self.function_analyses[faddr]
            if fra.is_structurally_equivalent:
                return fra.blocks_changed()
        return []

    def report(self, showfunctions: bool, showinstructions: bool) -> str:
        lines: List[str] = []
        lines.append("Summary Report")
        lines.append("=" * 80)
        lines.append("")

        fnames: Dict[str, str] = {}
        for faddr in self.functions_changed():
            if self.app1.has_function_name(faddr):
                fnames[faddr] = self.app1.function_name(faddr) + " (" + faddr + ")"
            else:
                fnames[faddr] = faddr

        maxnamelen = max(len(n) for n in fnames.values()) + 3

        lines.append(
            "function".ljust(maxnamelen)
            + "moved to".ljust(12)
            + "md5-equal".ljust(12)
            + "cfg-isomorphic".ljust(18)
            + "blocks-changed".ljust(12))
        lines.append("-" * 88)

        fnotfound: List[str] = []  # not found in patched version
        fnotmapped: List[str] = []  # not found in original version

        totalinstrs: int = 0
        totalblocks: int = 0

        for faddr in self.functions_changed():
            if faddr in self.function_mapping:
                fra = self.function_analyses[faddr]
                if faddr != self.function_mapping[faddr]:
                    moved = self.function_mapping[faddr]
                else:
                    moved = "not moved"
            else:
                moved = "not found"
            if faddr in self.function_analyses:
                md5eq = "yes" if fra.is_md5_equal else "no"
                if fra.is_cfg_isomorphic:
                    streq = "yes"
                    blockschanged = len(fra.blocks_changed())
                    totalinstrs += fra.instructions_changed()
                    allblocks = len(fra.basic_blocks1)
                    totalblocks += blockschanged
                    blchg = str(blockschanged) + "/" + str(allblocks)
                else:
                    streq = "no"
                    blchg = str(len(fra.cfg_blocks1)) + " -> " + str(len(fra.cfg_blocks2))

                lines.append(
                    fnames[faddr].ljust(maxnamelen)
                    + moved.ljust(16)
                    + md5eq.ljust(12)
                    + streq.ljust(18)
                    + blchg.ljust(12))
            else:
                fnotfound.append(faddr)

        lines.append("\nTotal blocks changed: " + str(totalblocks))
        lines.append("Total instructions changed: " + str(totalinstrs))
        lines.append("")

        if len(self.function_mapping) < len(self.faddrs2):
            for faddr2 in sorted(self.faddrs2):
                if faddr2 not in self.function_mapping.values():
                    fnotmapped.append(faddr2)
            lines.append(
                "\nFunctions mapped from original to patched: "
                + str(len(self.function_mapping)))
            lines.append(
                "Functions not found in patched version: " + str(len(fnotfound)))
            lines.append(
                "Functions in patched version not mapped: " + str(len(fnotmapped)))

        if showfunctions or showinstructions:
            lines.append("")
            lines.append("=" * 80)
            lines.append("Functions changed")
            lines.append("=" * 80)
            for faddr in self.functions_changed():
                if faddr in self.function_analyses:
                    fra = self.function_analyses[faddr]
                    lines.append("\nFunction " + fnames[faddr])
                    lines.append(fra.report(showinstructions))
                else:
                    lines.append(
                        "\nFunction "
                        + fnames[faddr]
                        + " not mapped to patched version")

        return "\n".join(lines)