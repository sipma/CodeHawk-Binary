#!/usr/bin/env python3
# ------------------------------------------------------------------------------
# CodeHawk Binary Analyzer
# Author: Henny Sipma
# ------------------------------------------------------------------------------
# The MIT License (MIT)
#
# Copyright (c) 2021-2024  Aarno Labs, LLC
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
"""Support functions for the command-line interpreter."""

import argparse
import json

from typing import (
    Any,
    Callable,
    cast,
    Dict,
    List,
    Mapping,
    NoReturn,
    Optional,
    Sequence,
    Tuple,
    TYPE_CHECKING)

from chb.api.AppFunctionSignature import AppFunctionSignature

from chb.app.Callgraph import Callgraph
from chb.app.Instruction import Instruction

from chb.arm.ARMInstruction import ARMInstruction

from chb.buffer.LibraryCallCallsites import LibraryCallCallsites

import chb.cmdline.commandutil as UC
import chb.cmdline.jsonresultutil as JU
import chb.cmdline.XInfo as XI

from chb.invariants.XXpr import XprCompound, XprConstant, XXpr

from chb.jsoninterface.JSONResult import JSONResult

from chb.models.ModelsAccess import ModelsAccess

import chb.util.fileutil as UF
from chb.util.loggingutil import chklogger

if TYPE_CHECKING:
    from chb.api.CallTarget import (
        StubTarget, CallTarget)
    from chb.api.FunctionStub import SOFunction
    from chb.app.AppAccess import AppAccess
    from chb.app.BasicBlock import BasicBlock
    from chb.app.Instruction import Instruction
    from chb.mips.MIPSInstruction import MIPSInstruction
    from chb.models.BTerm import BTerm, BTermArithmetic
    from chb.models.FunctionSummary import FunctionSummary
    from chb.models.FunctionPrecondition import (
        FunctionPrecondition, PreDerefWrite)


def reportcommand(args: argparse.Namespace) -> NoReturn:
    print("The report command can be followed by the following subcommands:")
    print("  (all commands take the name of the executable as first argument)")
    print("")
    print("  calls <xname>      output all calls to a particular target function")
    print("~" * 80)
    exit(0)


def dst_stack_arg_offset(instr: Instruction, dstargix: int) -> Optional[int]:
    try:
        dstarg = instr.call_arguments[dstargix]
        if dstarg.is_stack_address:
            dstarg = cast(XprCompound, dstarg)
            return (-dstarg.stack_address_offset())
        else:
            print("Not a stack address: " + str(dstarg))
            return None
    except Exception as e:
        print("Exception in " + str(instr) + ": " + str(e))
        return None


def get_role_value(role: str, arg: XXpr) -> str:
    s_arg = str(arg)
    if role in ["reads-from"] and arg.is_string_reference:
        return "constant-str"
    elif role in ["writes-to", "reads-from"]:
        if arg.is_stack_address:
            return "stack"
        elif arg.is_heap_address:
            return "heap"
        elif arg.is_global_address:
            return "global"
        elif arg.is_global_variable:
            return "global-var"
        elif arg.is_function_return_value:
            return "fn retval"
        elif arg.is_argument_value:
            return "fn arg"
        else:
            return "unknown"
    elif role in ["length"]:
        if arg.is_constant:
            return "constant"
        elif arg.is_argument_value:
            return "fn_arg"
        elif arg.is_function_return_value:
            return "fn retval"
        else:
            return "unknown"
    else:
        return "unknown"


class TargetFunctionParameter:

    def __init__(self, name: str, paramroles: List[str]) -> None:
        self._name = name
        self._paramroles = paramroles

    @property
    def name(self) -> str:
        return self._name

    @property
    def parameter_roles(self) -> List[str]:
        return self._paramroles

    def to_json_result(self) -> JSONResult:
        content: Dict[str, Any] = {}
        schema = "callsitetgtparameter"

        content["name"] = self.name
        content["parameter-roles"] = self.parameter_roles
        return JSONResult(schema, content, "ok")


class CallsiteTargetFunction:

    def __init__(
            self,
            name: str,
            isvarargs: bool,
            parameters: List[TargetFunctionParameter]) -> None:
        self._name = name
        self._isvarargs = isvarargs
        self._parameters = parameters

    @property
    def name(self) -> str:
        return self._name

    @property
    def is_varargs(self) -> bool:
        return self._isvarargs

    @property
    def parameters(self) -> List[TargetFunctionParameter]:
        return self._parameters

    @property
    def parametercount(self) -> int:
        return len(self.parameters)

    def parameter(self, n: int) -> TargetFunctionParameter:
        """Return n'th parameter (zero-based)."""

        if n < len(self.parameters):
            return self.parameters[n]

        elif self.is_varargs:
            argix = n - len(self.parameters)
            return TargetFunctionParameter("vararg_" + str(argix), [])
        else:
            raise UF.CHBError(
                "Index: "
                + str(n)
                + " exceeds number of parameters for "
                + self.name
                + " ("
                + str(len(self.parameters))
                + ")")

    def to_json_result(self) -> JSONResult:
        content: Dict[str, Any] = {}
        schema = "callsitetgtfunction"

        content["name"] = self.name
        content["parameters"] = [p.to_json_result().content for p in self.parameters]
        content["varargs"] = self.is_varargs
        return JSONResult(schema, content, "ok")


class CallsiteArgument:

    def __init__(
            self,
            name: str,
            value: str,
            rolevalues: List[Dict[str, str]] = []) -> None:
        self._name = name
        self._value = value
        self._rolevalues = rolevalues

    @property
    def name(self) -> str:
        return self._name

    @property
    def value(self) -> str:
        return self._value

    @property
    def rolevalues(self) -> List[Dict[str, str]]:
        return self._rolevalues

    def to_json_result(self) -> JSONResult:
        content: Dict[str, Any] = {}
        schema = "callsiteargument"

        content["name"] = self.name
        content["value"] = self.value
        if len(self.rolevalues) > 0:
            content["roles"] = self.rolevalues
        return JSONResult(schema, content, "ok")


class CallRecord:

    def __init__(
            self,
            faddr: str,
            instr: Instruction,
            tgtfunction: CallsiteTargetFunction,
            callgraph: Optional[Callgraph] = None) -> None:
        self._faddr = faddr
        self._instr = instr
        self._cs_arguments: Optional[List[CallsiteArgument]] = None
        self._tgtfunction = tgtfunction
        self._callgraph = callgraph

    @property
    def instr(self) -> Instruction:
        return self._instr

    @property
    def faddr(self) -> str:
        return self._faddr

    @property
    def iaddr(self) -> str:
        return self.instr.iaddr

    @property
    def tgtfunction(self) -> CallsiteTargetFunction:
        return self._tgtfunction

    @property
    def arguments(self) -> Sequence["XXpr"]:
        return self.instr.call_arguments

    @property
    def cs_arguments(self) -> List[CallsiteArgument]:
        if self._cs_arguments is None:
            self._cs_arguments = []
            if (
                    (len(self.arguments) <= self.tgtfunction.parametercount)
                    or self.tgtfunction.is_varargs):
                for (argix, arg) in enumerate(self.arguments):
                    param = self.tgtfunction.parameter(argix)
                    rolevalues: List[Dict[str, str]] = []
                    for rn in param.parameter_roles:
                        rv = get_role_value(rn, arg)
                        rolevalues.append({"rn": rn, "rv": rv})
                    csarg = CallsiteArgument(param.name, str(arg), rolevalues)
                    self._cs_arguments.append(csarg)
            else:
                for (argix, arg) in enumerate(self.arguments):
                    name = "arg_" + str(argix)
                    csarg = CallsiteArgument(name, str(arg))
                    self._cs_arguments.append(csarg)
        return self._cs_arguments

    def has_callgraph(self) -> bool:
        return self._callgraph is not None

    @property
    def callgraph(self) -> Callgraph:
        if self._callgraph is not None:
            return self._callgraph
        else:
            raise UF.CHBError("No callgraph available")

    def has_nonempty_callgraph(self) -> bool:
        if self.has_callgraph():
            return len(self.callgraph.edges) > 0
        else:
            return False

    def to_json_result(self) -> JSONResult:
        content: Dict[str, Any] = {}
        schema = "callsiterecord"
        content["faddr"] = self.faddr
        content["iaddr"] = self.iaddr
        content["arguments"] = [a.to_json_result().content for a in self.cs_arguments]
        if self.has_callgraph():
            jcg = self.callgraph.to_json_result()
            if jcg.is_ok:
                content["cgpath"] = jcg.content
            else:
                return JSONResult(schema, {}, "fail", jcg.reason)
        return JSONResult(schema, content, "ok")


# temporary stub!!
def report_calls_json_to_string(result: Dict[str, Any]) -> str:
    return str(result)


def get_parameter_attributes_from_roles(paramroles: List[str]) -> List[str]:

    if "deref-write:destination" in paramroles:
        return ["writes-to"]

    if "deref-write-null:destination" in paramroles:
        return ["writes-to-if-nonnull"]

    if "deref-read:source" in paramroles:
        return ["reads-from"]

    if "deref-read:length" in paramroles:
        return ["length"]

    if "deref-write:length" in paramroles:
        return ["length"]

    return paramroles


def callsite_target_function(
        xcallee: str,
        function_names: Dict[str, str],
        app: "AppAccess",
        models: "ModelsAccess") -> CallsiteTargetFunction:

    targetname: Optional[str] = None
    if xcallee.startswith("0x"):
        if app.has_function(xcallee):
            if app.has_function_name(xcallee):
                targetname = app.function_name(xcallee)
                function_names[xcallee] = targetname
            else:
                targetname = "sub_" + xcallee[2:]
        else:
            raise UF.CHBError("No function found with address " + xcallee)

    elif app.is_unique_app_function_name(xcallee):

        callee_hex = app.function_address_from_name(xcallee)
        if app.has_function(callee_hex):
            targetname = xcallee
            function_names[callee_hex] = xcallee

        else:
            raise UF.CHBError(
                "No function found with name " + xcallee + " (" + callee_hex + ")")

    if targetname is not None:
        return CallsiteTargetFunction(targetname, False, [])

    else:
        # dynamically linked library function (assume ELF here)
        parameters: List[TargetFunctionParameter] = []
        isvarargs: bool = False
        if models.has_so_function_summary(xcallee):
            fnsum = models.so_function_summary(xcallee)
            fnparams = fnsum.signature.parameters
            isvarargs = fnsum.signature.is_varargs
            for fparam in fnparams:
                paramroles = fnsum.semantics.parameter_roles(fparam.name)
                paramattrs = get_parameter_attributes_from_roles(paramroles)
                parameters.append(TargetFunctionParameter(fparam.name, paramattrs))

        else:
            UC.print_status_update("No model found for " + xcallee)

        return CallsiteTargetFunction(xcallee, isvarargs, parameters)


def report_calls(
        path: str,
        xfile: str,
        xcallee: str,
        xcgpathsrc: Optional[str] = None) -> JSONResult:
    """Collect and return all callsites where xcallee is called.

    xcallee: the target function
      this can be one of the following:
      - hex address of application function
      - symbolic name of application function
      - symbolic name of dynamically linked library function

    xcgpathsrc: optional function to use as source for callgraph path to callsite
      this can be one of the following:
      - hex address of application function
      - symbolic name of application function
      if None: no callgraph path is included in the callsite records.

    The result has json schema callsiterecords.
    """

    xinfo = XI.XInfo()
    xinfo.load(path, xfile)

    app = UC.get_app(path, xfile, xinfo)
    models = ModelsAccess()

    content: Dict[str, Any] = {}
    schema: str = "callsiterecords"

    # keep track of application functions that have a symbolic name
    function_names: Dict[str, str] = {}

    # construct callsite target function record from xcallee
    try:
        tgtfunction = callsite_target_function(
            xcallee, function_names, app, models)
    except UF.CHBError as e:
        UC.print_error("Failure: " + str(e))
        return JSONResult(schema, {}, "fail", str(e))

    content["tgt-function"] = tgtfunction.to_json_result().content

    # determine source for callgraph paths to callsite
    hexcgpathsrc: Optional[str] = None
    callgraph: Optional[Callgraph] = None
    if xcgpathsrc is not None:
        if xcgpathsrc.startswith("0x"):
            hexcgpathsrc = xcgpathsrc
            if not app.has_function(xcgpathsrc):
                UC.print_error(
                    "No source function found with address " + xcgpathsrc)
                return JSONResult(
                    schema,
                    {},
                    "fail",
                    "No source function found with address " + xcgpathsrc)

        elif app.is_unique_app_function_name(xcgpathsrc):
            hexcgpathsrc = app.function_address_from_name(xcgpathsrc)
            function_names[hexcgpathsrc] = xcgpathsrc
        else:
            UC.print_error(
                "Failure: No application function found with name " + xcgpathsrc)
            return JSONResult(
                schema,
                {},
                "fail",
                "No application function found with name " + xcgpathsrc)
        content["cgpath-src"] = hexcgpathsrc
        callgraph = app.callgraph()
        callgraph = callgraph.constrain_sources([hexcgpathsrc])

    else:
        # no callgraph paths
        pass

    # iterate through callsites
    calls = app.call_instructions()
    callcount = 0
    content["callsites"] = callsites = []

    for faddr in sorted(calls):
        fname = (
            app.function_name(faddr)
            if app.has_function_name(faddr)
            else None)
        for baddr in calls[faddr]:
            for instr in calls[faddr][baddr]:
                callcount += 1
                if instr.call_target.name == tgtfunction.name:
                    tgtpath: Optional[Callgraph] = None
                    if fname is not None:
                        function_names[faddr] = fname
                    if callgraph is not None:
                        UC.print_status_update("Generating callgraph for callsite at " + str(instr))
                        tgtpath = callgraph.constrain_sink_edge(src=faddr, dst=tgtfunction.name)
                    callrec = CallRecord(
                        faddr, instr, tgtfunction, callgraph=tgtpath).to_json_result()
                    if callrec.is_ok:
                        callsites.append(callrec.content)
                    else:
                        UC.print_error("Failure: " + str(callrec.reason))
                        return JSONResult(schema, {}, "fail", str(callrec.reason))

    if len(function_names) > 0:
        dfnames: List[Dict[str, str]] = []
        for (fnaddr, fnname) in sorted(function_names.items()):
            dfnames.append({"addr": fnaddr, "name": fnname})
        content["function-names"] = dfnames

    UC.print_status_update(
        "Found "
        + str(len(callsites))
        + " callsites for "
        + tgtfunction.name
        + " (out of "
        + str(callcount)
        + " calls)")
    if callgraph is not None:
        cgcount = len([cs for cs in callsites if len(cs["cgpath"]["edges"]) > 0])
        UC.print_status_update(
            "Nonempty callgraph path from: "
            + str(xcgpathsrc)
            + ": "
            + str(cgcount)
            + " out of "
            + str(len(callsites))
            + " callsites")

    return JSONResult(schema, content, "ok")


def report_calls_cmd(args: argparse.Namespace) -> NoReturn:

    # arguments
    xname: str = args.xname
    xcallee: str = args.callee
    xjson: bool = args.json
    xoutput: Optional[str] = args.output
    xcgpathsrc: Optional[str] = args.cgpathsrc

    try:
        (path, xfile) = UC.get_path_filename(xname)
        UF.check_analysis_results(path, xfile)
    except UF.CHBError as e:
        print(str(e.wrap()))
        exit(1)

    result = report_calls(path, xfile, xcallee, xcgpathsrc)
    schema = "callsiterecords"

    if result.is_ok:
        jsonresult = JU.jsonok(schema, result.content)
    else:
        jsonresult = JU.jsonfail(
            "Error in collecting calls for "
            + xcallee
            + ": "
            + str(result.reason))

    if xoutput is not None:
        if xjson:
            outputfilename = xoutput + ".json"
            with open(outputfilename, "w") as fp:
                json.dump(jsonresult, fp)
        else:
            outputfilename = xoutput + ".txt"
            with open(outputfilename, "w") as fp:
                fp.write(report_calls_json_to_string(jsonresult))

        if result.is_ok:
            UC.print_status_update(
                "Success. Results for report calls saved in " + outputfilename)
            exit(0)
        else:
            UC.print_status_update(
                "Failure. Reason reported in " + outputfilename)
            exit(1)

    else:
        if xjson:
            print(json.dumps(jsonresult))
        else:
            print(report_calls_json_to_string(jsonresult))

    if result.is_ok:
        exit(0)
    else:
        exit(1)


def report_function_apis(args: argparse.Namespace) -> NoReturn:

    # arguments
    xname: str = args.xname
    xdetails: bool = args.details

    try:
        (path, xfile) = UC.get_path_filename(xname)
        UF.check_analysis_results(path, xfile)
    except UF.CHBError as e:
        print(str(e.wrap()))
        exit(1)

    xinfo = XI.XInfo()
    xinfo.load(path, xfile)

    app = UC.get_app(path, xfile, xinfo)

    signatures: Dict[str, AppFunctionSignature] = {}

    nosignatures: List[str] = []

    preconditions: Dict[str, int] = {}   # tag -> count
    sideeffects: Dict[str, int] = {}

    for (faddr, fn) in app.functions.items():
        appsum = fn.finfo.appsummary
        if appsum is not None:
            fintf = appsum.function_interface
            fnsig = fintf.signature
            if len(fnsig.parameter_list) > 0:
                signatures[faddr] = fnsig
            else:
                nosignatures.append(faddr)
            fsem = appsum.function_semantics
            for pre in fsem.precondition_list:
                preconditions.setdefault(pre.tags[0], 0)
                preconditions[pre.tags[0]] += 1
            for se in fsem.sideeffect_list:
                sideeffects.setdefault(se.tags[0], 0)
                sideeffects[se.tags[0]] += 1


    print("Functions with signatures: " + str(len(signatures)))
    print("Functions without        : " + str(len(nosignatures)))
    print("\nPreconditions: " + str(sum(preconditions.values())))
    for (tag, count) in sorted(preconditions.items()):
        print("  " + tag.ljust(7) + str(count).rjust(5))
    print("\nSide effects: " + str(sum(sideeffects.values())))
    for (tag, count) in sorted(sideeffects.items()):
        print("  " + tag.ljust(7) + str(count).rjust(5))

    if xdetails:
        print("\nNo signatures (or empty parameter list):")
        for faddr in sorted(nosignatures):
            print("  " + faddr)

    exit(0)


def report_proofobligations(args: argparse.Namespace) -> NoReturn:

    # arguments
    xname: str = args.xname

    try:
        (path, xfile) = UC.get_path_filename(xname)
        UF.check_analysis_results(path, xfile)
    except UF.CHBError as e:
        print(str(e.wrap()))
        exit(1)

    xinfo = XI.XInfo()
    xinfo.load(path, xfile)

    app = UC.get_app(path, xfile, xinfo)

    proofobligations: Dict[str, Dict[str, int]] = {} #  type -> status -> count

    for fn in app.functions.values():
        polist = fn.proofobligations.proofobligations.values()
        for pos in polist:
            for po in pos:
                proofobligations.setdefault(po.xpo.tags[0], {})
                proofobligations[po.xpo.tags[0]].setdefault(po.status.tag, 0)
                proofobligations[po.xpo.tags[0]][po.status.tag] += 1

    print("Proof obligation counts")
    print("type".ljust(8) + "discharged".rjust(10) + "delegated".rjust(10) +
          "global".rjust(10) + "request".rjust(10) + "open".rjust(10))
    print("-" * 58)
    for (xpotag, xpodata) in sorted(proofobligations.items()):
        line: List[str] = []
        line.append(xpotag.ljust(8))
        for x in ["dis", "del", "glob", "req", "o"]:
            if x in xpodata:
                line.append(str(xpodata[x]).rjust(10))
            else:
                line.append(" ".rjust(10))
        print("".join(line))

    exit(0)


def report_memops(args: argparse.Namespace) -> NoReturn:

    # arguments
    xname: str = args.xname

    try:
        (path, xfile) = UC.get_path_filename(xname)
        UF.check_analysis_results(path, xfile)
    except UF.CHBError as e:
        print(str(e.wrap()))
        exit(1)

    xinfo = XI.XInfo()
    xinfo.load(path, xfile)

    app = UC.get_app(path, xfile, xinfo)

    memloads = app.load_instructions()
    memstores = app.store_instructions()

    loadstats: Dict[str, Tuple[int, int]] = {}
    storestats: Dict[str, Tuple[int, int]] = {}

    def add_load_unknown(faddr: str) -> None:
        loadstats.setdefault(faddr, (0, 0))
        v = loadstats[faddr]
        loadstats[faddr] = (v[0] + 1, v[1])

    def add_load_known(faddr: str) -> None:
        loadstats.setdefault(faddr, (0, 0))
        v = loadstats[faddr]
        loadstats[faddr] = (v[0] + 1, v[1] + 1)

    loadxrefs: Dict[str, List[str]] = {}

    def add_load_xref(gv: str, faddr: str) -> None:
        loadxrefs.setdefault(gv, [])
        loadxrefs[gv].append(faddr)

    print("Load instructions")
    print("-----------------")
    for faddr in sorted(memloads):
        print("\nFunction " + faddr)
        for baddr in memloads[faddr]:
            print("  Block: " + baddr)
            for instr in memloads[faddr][baddr]:
                print("     " + str(instr))
                for rhs in instr.rhs:
                    add_load_xref(str(rhs), faddr)
                    if str(rhs) == "?":
                        add_load_unknown(faddr)
                    else:
                        add_load_known(faddr)

    def add_store_unknown(faddr: str) -> None:
        storestats.setdefault(faddr, (0, 0))
        v = storestats[faddr]
        storestats[faddr] = (v[0] + 1, v[1])

    def add_store_known(faddr: str) -> None:
        storestats.setdefault(faddr, (0, 0))
        v = storestats[faddr]
        storestats[faddr] = (v[0] + 1, v[1] + 1)

    storexrefs: Dict[str, List[str]] = {}

    def add_store_xref(gv: str, faddr: str) -> None:
        storexrefs.setdefault(gv, [])
        storexrefs[gv].append(faddr)

    print("\n\nStore instructions")
    print("----------------------")
    for faddr in sorted(memstores):
        print("\nFunction " + faddr)
        for baddr in memstores[faddr]:
            print("  Block: " + baddr)
            for instr in memstores[faddr][baddr]:
                print("     " + str(instr))
                for lhs in instr.lhs:
                    add_store_xref(str(lhs), faddr)
                    if str(lhs) in ["?", "??operand??"]:
                        add_store_unknown(faddr)
                    else:
                        add_store_known(faddr)

    print("\nLoad xreferences")
    print("------------------")
    for gv in sorted(loadxrefs):
        if gv.startswith("gv_"):
            print(gv.ljust(24) + "[" + ", ".join(loadxrefs[gv]) + "]")

    print("\nStore xreferences")
    print("-------------------")
    for gv in sorted(storexrefs):
        if gv.startswith("gv"):
            print(gv.ljust(24) + "[" + ", ".join(storexrefs[gv]) + "]")

    print("\nLoad statistics")
    print("-----------------")
    loadtotal: int = 0
    loadknown: int = 0
    for faddr in sorted(loadstats):
        ftotal = loadstats[faddr][0]
        fknown = loadstats[faddr][1]
        loadtotal += ftotal
        loadknown += fknown
        print(
            faddr
            + ": "
            + str(fknown).rjust(4)
            + " / "
            + str(ftotal).ljust(4))

    if loadtotal > 0:
        perc = (loadknown / loadtotal) * 100
        fperc = "{:.2f}".format(perc)
        print(
            "\nTotal: "
            + str(loadknown)
            + " / "
            + str(loadtotal)
            + " ("
            + fperc
            + "%)")

    print("\nStore statistics")
    print("------------------")
    storetotal = 0
    storeknown = 0
    for faddr in sorted(storestats):
        ftotal = storestats[faddr][0]
        fknown = storestats[faddr][1]
        storetotal += ftotal
        storeknown += fknown
        print(
            faddr + ": " + str(fknown).rjust(4) + " / " + str(ftotal).ljust(4))

    if storetotal > 0:
        perc = (storeknown / storetotal) * 100
        fperc = "{:.2f}".format(perc)
        print(
            "\nTotal: "
            + str(storeknown)
            + " / "
            + str(storetotal)
            + " ("
            + fperc
            + "%)")
    exit(0)


def report_unresolved(args: argparse.Namespace) -> NoReturn:

    # arguments
    xname: str = args.xname
    xoutput: str = args.outputfile
    xverbose: bool = args.verbose

    try:
        (path, xfile) = UC.get_path_filename(xname)
        UF.check_analysis_results(path, xfile)
    except UF.CHBError as e:
        print(str(e.wrap()))
        exit(1)

    xinfo = XI.XInfo()
    xinfo.load(path, xfile)

    results: Dict[str, Any] = {}
    results["memory-operations"] = {}

    app = UC.get_app(path, xfile, xinfo)

    calls = app.call_instructions()
    jumps = app.jump_instructions()

    memloads = app.load_instructions()
    memstores = app.store_instructions()

    unknownloads: Dict[str, List[str]] = {}
    unknownstores: Dict[str, List[str]] = {}
    unknowncalls: Dict[str, List[str]] = {}
    unknownjumps: Dict[str, List[str]]  = {}

    def vprint(faddr: str, instr: Instruction) -> None:
        if xverbose:
            print(faddr + ":" + instr.iaddr + "  " + str(instr))

    def add_unknown_load(faddr: str, instr: Instruction) -> None:
        vprint(faddr, instr)
        unknownloads.setdefault(faddr, [])
        unknownloads[faddr].append(instr.iaddr)

    def add_unknown_store(faddr: str, instr: Instruction) -> None:
        vprint(faddr, instr)
        unknownstores.setdefault(faddr, [])
        unknownstores[faddr].append(instr.iaddr)

    def add_unknown_call(faddr: str, instr: Instruction) -> None:
        vprint(faddr, instr)
        unknowncalls.setdefault(faddr, [])
        unknowncalls[faddr].append(instr.iaddr)

    def add_unknown_jump(faddr: str, instr: Instruction) -> None:
        vprint(faddr, instr)
        unknownjumps.setdefault(faddr, [])
        unknownjumps[faddr].append(instr.iaddr)

    for faddr in sorted(memloads):
        for baddr in memloads[faddr]:
            for instr in memloads[faddr][baddr]:
                for rhs in instr.rhs:
                    if "?" in str(rhs):
                        add_unknown_load(faddr, instr)

    for faddr in sorted(memstores):
        for baddr in memstores[faddr]:
            for instr in memstores[faddr][baddr]:
                for lhs in instr.lhs:
                    if "?" in str(lhs):    # in ["?", "??operand??"]:
                        add_unknown_store(faddr, instr)

    for faddr in sorted(calls):
        for baddr in calls[faddr]:
            for instr in calls[faddr][baddr]:
                if instr.mnemonic == "BLX":
                    instr = cast("ARMInstruction", instr)
                    if not instr.xdata.has_call_target():
                        add_unknown_call(faddr, instr)

    for faddr in sorted(jumps):
        for baddr in jumps[faddr]:
            for instr in jumps[faddr][baddr]:
                if instr.mnemonic == "BX":
                    instr = cast("ARMInstruction", instr)
                    if str(instr.xdata.xprs[0]) not in  ["LR", "PC"]:
                        add_unknown_jump(faddr, instr)

    results["calls"] = unknowncalls
    results["jumps"] = unknownjumps
    results["memory-operations"]["loads"] = unknownloads
    results["memory-operations"]["stores"] = unknownstores

    data: Dict[str, Any] = {}
    data["program"] = xinfo.file
    data["md5"] = xinfo.md5
    data["unresolved"] = results

    numcalls = sum(len(unknowncalls[f]) for f in unknowncalls)
    numjumps = sum(len(unknownjumps[f]) for f in unknownjumps)
    numloads = sum(len(unknownloads[f]) for f in unknownloads)
    numstores = sum(len(unknownstores[f]) for f in unknownstores)

    def count_instrs(
            d: Mapping[str, Mapping[str, Sequence[Instruction]]]) -> int:
        result: int = 0
        for faddr in d:
            for baddr in d[faddr]:
                result += len(d[faddr][baddr])

        if result == 0:
            result = 1
        return result

    perccalls = float(numcalls) / float(count_instrs(calls))
    percjumps = float(numjumps) / float(count_instrs(jumps))
    percloads = float(numloads) / float(count_instrs(memloads))
    percstores = float(numstores) / float(count_instrs(memstores))

    def perc(v: float) -> str:
        return (" (" + "{:.1f}".format(100.0 * v) + "%)").rjust(8)

    print("\nResults:")
    print("Unresolved calls : " + str(numcalls).rjust(5) + perc(perccalls))
    print("Unresolved jumps : " + str(numjumps).rjust(5) + perc(percjumps))
    print("Unresolved loads : " + str(numloads).rjust(5) + perc(percloads))
    print("Unresolved stores: " + str(numstores).rjust(5) + perc(percstores))

    filename = xoutput + ".json"
    with open(filename, "w") as fp:
        json.dump(data, fp, indent=2)

    exit(0)


def write_json_result(xfilename: Optional[str],
                      jresult: JSONResult,
                      schema_name: str,
                     ) -> None:
    if jresult.is_ok:
        okresult = JU.jsonok(schema_name, jresult.content)
        if xfilename is not None:
            filename = xfilename + ".json"
            with open(filename, "w") as fp:
                json.dump(okresult, fp, indent=2)
            chklogger.logger.info("JSON output written to " + filename)
        else:
            print(json.dumps(okresult))
    else:
        failresult = JU.jsonfail(jresult.reason)
        if xfilename is not None:
            filename = xfilename + ".json"
            with open(filename, "w") as fp:
                json.dump(failresult, fp, indent=2)
            chklogger.logger.warning(
                "JSON failure output written to " + filename)
        else:
            print(json.dumps(failresult))

def report_buffer_bounds(args: argparse.Namespace) -> NoReturn:

    # arguments
    xname: str = args.xname
    xoutput: Optional[str] = args.output
    xjson: bool = args.json
    xverbose: bool = args.verbose

    try:
        (path, xfile) = UC.get_path_filename(xname)
        UF.check_analysis_results(path, xfile)
    except UF.CHBError as e:
        print(str(e.wrap()))
        exit(1)

    xinfo = XI.XInfo()
    xinfo.load(path, xfile)

    app = UC.get_app(path, xfile, xinfo)

    n_calls: int = 0
    libcalls = LibraryCallCallsites()

    for (faddr, blocks) in app.call_instructions().items():
        fn = app.function(faddr)

        for (baddr, instrs) in blocks.items():
            for instr in instrs:
                n_calls += 1
                calltgt = instr.call_target
                if calltgt.is_so_target:
                    libcalls.add_library_callsite(faddr, baddr, instr)

    if xjson:
        content: Dict[str, Any] = {}
        xinfodata = xinfo.to_json_result()
        if xinfodata.is_ok:
            content["identification"] = xinfodata.content
        else:
            write_json_result(xoutput, xinfodata, "bufferboundsassessment")
        analysisstats = app.result_metrics.to_json_result()
        if analysisstats.is_ok:
            content["analysis"] = analysisstats.content
        else:
            write_json_result(xoutput, analysisstats, "bufferboundsassessment")

        libcallsresult = libcalls.to_json_result()
        if libcallsresult.is_ok:
            content["bounds"] = libcallsresult.content
        else:
            write_json_result(xoutput, libcallsresult, "bufferboundsassessment" )

        write_json_result(xoutput, JSONResult(
            "libcboundsanalysis", content, "ok"), "bufferboundsassessment")

    if not xverbose:
        exit(0)

    print(f"Calls               : {n_calls}")
    print(f"Library calls       : {libcalls.n_librarycalls()}")
    print(f"Summarized          : {libcalls.n_summarized()}")
    print(f"Writing side effect : {libcalls.n_writing_sideeffect()}")

    print("\nSide effect destination types:")
    for (name, count) in sorted(
            libcalls.sideeffect_destination_types().items(),
            key=lambda i:(i[1], i[0]),
            reverse=True):
        print(name.ljust(24) + str(count).rjust(5))

    print("\nSide effect length types:")
    for (name, count) in sorted(
            libcalls.sideeffect_length_types().items(),
            key=lambda i:(i[1], i[0]),
            reverse=True):
        print(name.ljust(24) + str(count).rjust(5))

    print("\nKnown input length side effect writes")
    for (name, count) in sorted(
            libcalls.known_input_length_sideeffect_writes().items(),
            key=lambda i:(i[1], i[0]),
            reverse=True):
        print(name.ljust(24) + str(count).rjust(5))

    print("\nLength expressions:")
    for (name, count) in sorted(
            libcalls.sideeffect_length_exprs().items(),
            key=lambda i:(i[1], i[0]),
            reverse=True):
        print(str(count).rjust(5) + "  " + name)

    patchcandidates = libcalls.patch_candidates()
    print("\nPatch candidates (" + str(len(patchcandidates)) + "):")
    for pc in sorted(patchcandidates, key=lambda pc:pc.iaddr):
        print("  " + pc.iaddr + "  " + pc.annotation)

    print("\nPatch candidate distribution")
    for (name, count) in sorted(
            libcalls.patch_candidates_distribution().items(),
            key=lambda i:(i[1], i[0]),
            reverse=True):
        print(name.ljust(24) + str(count).rjust(5))

    print("\nMissing summaries")
    for (name, count) in sorted(
            libcalls.missing_summaries().items(),
            key=lambda i:(i[1], i[0]),
            reverse=True):
        print(name.ljust(24) + str(count).rjust(5))
    exit(0)


def collect_known_fn_addrs(app: "AppAccess", patchcallsites: list) -> dict:
    function_addr: Dict[str, str] = {}
    def consider_pair(faddr: str, fname: Optional[str]):
        if fname and fname not in function_addr:
            function_addr[fname] = faddr
    def consider(faddr: str):
        fname = (
            app.function_name(faddr)
            if app.has_function_name(faddr)
            else None)
        consider_pair(faddr, fname)

    for (faddr, blocks) in app.call_instructions().items():
        consider(faddr)
        for (baddr, instrs) in blocks.items():
            for instr in instrs:
                calltgt = instr.call_target
                # The main thing we're trying to capture here is any
                # name->address mappings that CodeHawk recovered with
                # heuristics, which (for now) means shared object stubs.
                if calltgt.is_so_target:
                    opcode = instr.opcode # type: ignore
                    if app.is_mips:
                        # No support (or need?) for MIPS just yet
                        continue
                    optgt = opcode.opargs[0]
                    tgtname = cast("StubTarget", calltgt).stub.name
                    if optgt.is_absolute:
                        tgtaddr = optgt.opkind.address.get_hex()
                        consider_pair(tgtaddr, tgtname)

    return function_addr


def report_patch_candidates(args: argparse.Namespace) -> NoReturn:

    # arguments
    xname = args.xname
    xoutput: Optional[str] = args.output
    xjson: bool = args.json
    xverbose: bool = args.verbose
    xtargets: List[str] = args.targets
    loglevel: str = args.loglevel
    logfilename: Optional[str] = args.logfilename
    logfilemode: str = args.logfilemode

    try:
        (path, xfile) = UC.get_path_filename(xname)
        UF.check_analysis_results(path, xfile)
    except UF.CHBError as e:
        print(str(e.wrap()))
        exit(1)

    UC.set_logging(
        loglevel,
        path,
        logfilename=logfilename,
        mode=logfilemode,
        msg="report_patch_candidates invoked")

    xinfo = XI.XInfo()
    xinfo.load(path, xfile)

    def find_spare_instruction(
            block: "BasicBlock", iaddr: str) -> Optional[str]:
        if xinfo.is_mips:
            found = None
            for (addr, instr) in block.instructions.items():
                instr = cast("MIPSInstruction", instr)
                if instr.iaddr > iaddr:
                    break
                if instr.is_load_instruction:
                    if str(instr.operands[0]) == "t9":
                        found = instr.iaddr
            return found
        return None

    app = UC.get_app(path, xfile, xinfo)

    n_calls: int = 0
    libcalls = LibraryCallCallsites()

    include_all = xtargets == ['all']

    def include_target(target: 'CallTarget') -> bool:
        if include_all:
            return True
        return target.name in xtargets

    for (faddr, blocks) in app.call_instructions().items():
        for (baddr, instrs) in blocks.items():
            for instr in instrs:
                n_calls += 1
                calltgt = instr.call_target
                if calltgt.is_so_target and include_target(calltgt):
                    libcalls.add_library_callsite(faddr, baddr, instr)

    chklogger.logger.debug("Number of calls: %s", n_calls)

    patchcallsites = libcalls.patch_callsites()

    function_addr = collect_known_fn_addrs(app, patchcallsites)

    content: Dict[str, Any] = {}
    if xjson:
        xinfodata = xinfo.to_json_result()
        if xinfodata.is_ok:
            content["identification"] = xinfodata.content
        else:
            write_json_result(xoutput, xinfodata, "patchcandidates")

    patch_records = []

    for pc in sorted(patchcallsites, key=lambda pc:pc.faddr):
        instr = pc.instr
        dstarg = pc.dstarg
        if dstarg is None:
            chklogger.logger.warning(
                "No expression found for destination argument: %s",
                str(instr))
            continue
        dstoffset = dstarg.stack_address_offset()
        fn = app.function(pc.faddr)
        stackframe = fn.stackframe
        stackbuffer = stackframe.get_stack_buffer(dstoffset)
        if stackbuffer is None:
            chklogger.logger.warning(
                "No stackbuffer found for %s at offset %s",
                str(instr), str(dstoffset))
            continue
        buffersize = stackbuffer.size
        basicblock = fn.block(pc.baddr)
        spare = find_spare_instruction(basicblock, instr.iaddr)

        jresult = pc.to_json_result(dstoffset, buffersize, spare)
        if not jresult.is_ok:
            chklogger.logger.warning("Couldn't process patch callsite %s", pc)
            continue

        patch_records.append(jresult.content)

    content["function-addr"] = function_addr
    content["patch-records"] = patch_records
    chklogger.logger.debug("Number of patch callsites: %s", len(content['patch-records']))

    if xjson:
        jcontent = JSONResult("patchcandidates", content, "ok")
        write_json_result(xoutput, jcontent, "patchcandidates")
        exit(0)

    for patch_record in content["patch-records"]:
        print("  " + patch_record['iaddr'] + "  " + patch_record['annotation'])
        print("  - faddr: %s" % patch_record['faddr'])
        print("  - iaddr: %s" % patch_record['iaddr'])
        print("  - target function: %s" % patch_record['target-function'])
        print("  - stack offset: %s" % patch_record['stack-offset'])
        print("  - length argument: %s" % patch_record['length-argument'])
        print("  - buffersize: %s" % patch_record['buffersize'])
        print("  - spare: %s" % patch_record['spare'])
        print("")

    print("Generated %d patch records from %d library calls" %
          (len(content['patch-records']), n_calls))

    exit(0)
