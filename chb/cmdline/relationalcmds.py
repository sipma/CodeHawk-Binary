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
"""Initiate relational analysis of two binaries."""

import logging

import argparse
import datetime
import importlib
import json
import os
import subprocess

from typing import Any, cast, Dict, List, NoReturn, Optional, Tuple

from chb.cmdline.AnalysisManager import AnalysisManager
import chb.cmdline.commandutil as UC
import chb.cmdline.jsonresultutil as JU
from chb.cmdline.PatchResults import PatchResults, PatchEvent
from chb.cmdline.XComparison import XComparison
import chb.cmdline.XInfo as XI

from chb.elfformat.ELFSectionHeader import ELFSectionHeader

from chb.graphics.DotCfg import DotCfg

from chb.invariants.InvariantFact import NRVFact
from chb.invariants.NonRelationalValue import NonRelationalValue

from chb.jsoninterface.JSONAppComparison import JSONAppComparison
from chb.jsoninterface.JSONRelationalReport import JSONRelationalReport
from chb.jsoninterface.JSONResult import JSONResult

from chb.relational.PatchParticulars import PatchParticulars
from chb.relational.RelationalAnalysis import RelationalAnalysis

import chb.util.dotutil as UD
import chb.util.fileutil as UF
from chb.util.loggingutil import chklogger, LogLevel


def relational_header(xname1: str, xname2: str, md5: str, header: str) -> str:
    lines: List[str] = []
    lines.append("=" * 80)
    lines.append(
        "||"
        + ("CodeHawk Relational Analysis: " + header).ljust(76)
        + "||")
    lines.append("||" + "  - " + str(xname1).ljust(72) + "||")
    lines.append("||" + "  - " + str(xname2).ljust(72) + "||")
    lines.append("||" + "    md5 (patched): " + md5.ljust(57) + "||")
    lines.append("=" * 80)
    return "\n".join(lines)


def check_hints_for_thumb(hints: List[str]) -> bool:

    for f in hints:
        try:
            with open(f, "r") as fp:
                fuserdata = json.load(fp)
            if "userdata" in fuserdata:
                if "arm-thumb" in fuserdata["userdata"]:
                    return True
        except Exception as e:
            UC.print_error("Error in reading " + f + ": " + str(e))
            exit(1)
    return False


def compare_executable_content(
        path1: str,
        xfile1: str,
        path2: str,
        xfile2: str,
        is_thumb: bool,
        pdfiledata: Optional[Dict[str, Any]]) -> XComparison:
    """Compares the section headers of the second app with those of the first app.

    If additional code is added to one of the sections, it is assumed to be a
    trampoline. If the original application's architecture is Thumb, arm-thumb
    switches are returned, to be added to the user data for disassembly.

    In addition, text is returned that reports the changes.
    """

    xinfo1 = XI.XInfo()
    xinfo1.load(path1, xfile1)
    xinfo2 = XI.XInfo()
    xinfo2.load(path2, xfile2)

    if not (xinfo1.is_elf and xinfo2.is_elf):
        UC.print_error("No support yet for non-elf files")
        exit(1)

    app1 = UC.get_app(path1, xfile1, xinfo1)
    app2 = UC.get_app(path2, xfile2, xinfo2)

    sectionheaders1 = app1.header.sectionheaders
    sectionheaders2 = app2.header.sectionheaders

    xcomparison = XComparison(
        is_thumb,
        path1,
        xfile1,
        path2,
        xfile2,
        app1,
        app2,
        pdfiledata)

    xcomparison.compare_sections()
    xcomparison.compare_segments()

    return xcomparison


def relational_prepare_command(args: argparse.Namespace) -> NoReturn:

    # arguments
    xname1: str = args.xname1
    xname2: str = args.xname2
    hints: List[str] = args.hints
    headers: List[str] = args.headers
    xjson: bool = args.json
    xoutput: str = args.output
    save_aux_userdata: str = args.save_aux_userdata
    xsave_asm: bool = args.save_asm
    xpatchresults: Optional[str] = args.patch_results_file
    xprint: bool = not args.json
    xssa: bool = args.ssa
    collectdiagnostics = args.collect_diagnostics
    xconstruct_all_functions: bool = args.construct_all_functions
    loglevel: str = args.loglevel
    logfilename: Optional[str] = args.logfilename
    logfilemode: str = args.logfilemode

    try:
        (path1, xfile1) = UC.get_path_filename(xname1)
        UF.check_analysis_results(path1, xfile1)
        (path2, xfile2) = UC.get_path_filename(xname2)
    except UF.CHBError as e:
        print(str(e.wrap()))
        exit(1)

    UC.set_logging(
        loglevel,
        path1,
        logfilename=logfilename,
        mode=logfilemode,
        msg="relational prepare invoked")

    is_thumb: bool = check_hints_for_thumb(hints)
    userhints = UC.prepare_executable(path2, xfile2, True, True, hints=hints)

    patchresultsdata: Optional[Dict[str, Any]] = None
    if xpatchresults is not None:
        with open(xpatchresults, "r") as fp:
            patchresultsdata = json.load(fp)

    xcomparison = compare_executable_content(
        path1, xfile1, path2, xfile2, is_thumb, patchresultsdata)

    newuserdata = xcomparison.new_userdata()

    if xjson:
        jresult = xcomparison.to_json_result()
        jsonokresult = JU.jsonok("xcomparison", jresult.content)
        if xoutput:
            UC.print_status_update(
                "Structural difference report saved in " + xoutput)
            with open(xoutput, "w") as fp:
                json.dump(jsonokresult, fp)
        else:
            print(json.dumps(jsonokresult))

    else:
        if xoutput:
            UC.print_status_update(
                "Structural difference report saved in " + xoutput)

    userhints.add_hints(newuserdata)
    userhints.save_userdata(path2, xfile2)

    xinfo1 = XI.XInfo()
    xinfo1.load(path1, xfile1)

    xinfo2 = XI.XInfo()
    xinfo2.load(path2, xfile2)

    if save_aux_userdata is not None:
        with open(save_aux_userdata + ".json", "w") as fp:
            json.dump(userhints.hints, fp, indent=2)

    if len(xcomparison.newsegments) > 0:
        tmpfilename = os.path.join(path2, "tmp_userdata.json")
        tmpuserdata: Dict[str, Any] = {}
        tmpuserdata["userdata"] = userhints.hints
        with open(tmpfilename, "w") as fp:
            json.dump(tmpuserdata, fp, indent=2)
        userhints = UC.prepare_executable(
            path2, xfile2, True, True, hints=[tmpfilename])

    if not xjson:
        lines: List[str] = []
        lines.append(relational_header(
            xname1, xname2, xinfo2.md5, "executable sections"))
        lines.append(str(xcomparison))

        lines.append("\nAdditions to user data:")
        lines.append("~" * 80)
        if len(xcomparison.switchpoints) > 0:
            lines.append(
                " - New arm-thumb switch points: "
                + ", ".join(xcomparison.switchpoints) + "\n")

        if len(xcomparison.newcode) > 0:
            lines.append(" - New code inserted in the following memory regions:")
            for (x, y) in xcomparison.newcode:
                lines.append("    * From " + x + " to " + y)
        if len(xcomparison.messages) > 0:
            lines.append("\nMessages:")
            lines.append("\n".join(xcomparison.messages))
        lines.append("=" * 80)
        lines.append(
            "||" + (str(datetime.datetime.now()) + "  ").rjust(76) + "||")
        lines.append("=" * 80)
        print("\n".join(lines))

    # preprocess c files
    ifilenames: List[str] = []
    headerfilenames = [os.path.abspath(s) for s in headers]
    if len(headers) > 0:
        for f in headerfilenames:
            if os.path.isfile(f):
                ifilename = f[:-2] + ".i"
                ifilenames.append(ifilename)
                gcccmd = ["gcc", "-std=gnu99", "-m32", "-E", "-o", ifilename, f]
                chklogger.logger.debug("execute command %s", " ".join(gcccmd))
                p = subprocess.call(gcccmd, cwd=path2, stderr=subprocess.STDOUT)
                if not (p == 0):
                    UC.print_error("Error in " + str(gcccmd))
                    exit(1)
            else:
                UC.print_error("Header file " + f + " not found")
                exit(1)

    # Determine functions analyzed in original binary
    fns_include: List[str] = []
    fns_exclude: List[str] = []
    app1 = UC.get_app(path1, xfile1, xinfo1)
    stats1 = app1.result_metrics
    fncount1 = stats1.function_count
    if len(stats1.fns_included) > 0:
        fns_include = stats1.fns_included
        UC.print_status_update(
            "Only analyzing "
            + str(len(fns_include))
            + " out of "
            + str(fncount1)
            + " functions")
    elif len(stats1.fns_excluded) > 0:
        fns_exclude = stats1.fns_excluded
        UC.print_status_update(
            "Excluding functions "
            + ", ".join(fns_exclude)
            + " from the analysis")
    else:
        UC.print_status_update("Analyzing all functions")

    UC.print_status_update(
        "Analyzing patched version with updated user data ...")
    am = AnalysisManager(
        path2,
        xfile2,
        xsize=xinfo2.size,
        arm=True,
        elf=True,
        ifilenames=ifilenames,
        fns_include=fns_include,
        fns_exclude=fns_exclude,
        use_ssa=xssa,
        thumb=xcomparison.is_thumb)

    try:
        am.analyze(
            iterations=10,
            save_asm=xsave_asm,
            collectdiagnostics=collectdiagnostics,
            construct_all_functions=xconstruct_all_functions)
    except subprocess.CalledProcessError as e:
        print(e.output)
        print(e.args)
        exit(1)
    except UF.CHBError as e:
        print(str(e.wrap()))
        exit(1)

    chklogger.logger.info("relational prepare completed")
    exit(0)


def _relational_compare_generate_json(xname1: str,
                                      xname2: str,
                                      xpatchresults: Optional[str],
                                      usermappingfile: Optional[str],
                                      addresses: List[str],
                                      loglevel: str,
                                      logfilename: Optional[str],
                                      logfilemode: str,
                                     ) -> JSONResult:
    try:
        (path1, xfile1) = UC.get_path_filename(xname1)
        UF.check_analysis_results(path1, xfile1)
        (path2, xfile2) = UC.get_path_filename(xname2)
        UF.check_analysis_results(path2, xfile2)
    except UF.CHBError as e:
        print(str(e.wrap()))
        exit(1)

    UC.set_logging(
        loglevel,
        path1,
        logfilename=logfilename,
        mode=logfilemode,
        msg="relational compare all")

    usermapping: Dict[str, str] = {}
    if usermappingfile is not None:
        if os.path.isfile(usermappingfile):
            with open(usermappingfile, "r") as fp:
                userdata = json.load(fp)
                usermapping = userdata["function-mapping"]
        else:
            UC.print_error(
                "Usermapping file " + usermappingfile + " not found")
            exit(1)

    patchresultsdata: Optional[Dict[str, Any]] = None
    if xpatchresults is not None:
        with open(xpatchresults, "r") as fp:
            patchresultsdata = json.load(fp)

    patchevents: Dict[str, PatchEvent] = {} # start of wrapper -> patch event

    if patchresultsdata is not None:
        patchresults = PatchResults(patchresultsdata)
        for event in patchresults.events:
            if (
                    event.is_trampoline
                    or event.is_trampoline_pair_minimal_2_and_3):
                if event.has_wrapper():
                    startaddr = event.wrapper.vahex
                    patchevents[startaddr] = event

    xinfo1 = XI.XInfo()
    xinfo2 = XI.XInfo()
    xinfo1.load(path1, xfile1)
    xinfo2.load(path2, xfile2)
    app1 = UC.get_app(path1, xfile1, xinfo1)
    app2 = UC.get_app(path2, xfile2, xinfo2)

    relanalysis = RelationalAnalysis(
        app1,
        app2,
        faddrs1=addresses,
        usermapping=usermapping,
        patchevents=patchevents)
    return relanalysis.to_json_result()


def relational_compare_all_cmd(args: argparse.Namespace) -> NoReturn:
    """Compares everything in the binary and puts the results in a json file"""

    # arguments
    xname1: str = args.xname1
    xname2: str = args.xname2
    xpatchresults: Optional[str] = args.patch_results_file
    xoutput: str = args.output
    usermappingfile: Optional[str] = args.usermapping
    loglevel: str = args.loglevel
    logfilename: Optional[str] = args.logfilename
    logfilemode: str = args.logfilemode

    result = _relational_compare_generate_json(xname1, xname2, xpatchresults,
                                               usermappingfile, [],
                                               loglevel, logfilename, logfilemode)
    if result.is_ok:
        jsonresult = JU.jsonok("compareall", result.content)
        exitval = 0
    else:
        UC.print_error(
            "Error in constructing json format: " + str(result.reason))
        jsonresult = JU.jsonfail(result.reason)
        exitval = 1

    if xoutput:
        UC.print_status_update(
            "Relational analysis results saved in " + xoutput)
        with open(xoutput, "w") as fp:
            json.dump(jsonresult, fp)
    else:
        print(json.dumps(jsonresult))

    exit(exitval)


def relational_compare_app_cmd(args: argparse.Namespace) -> NoReturn:
    """Comparison of all functions that have analysis results."""

    # arguments
    xname1: str = args.xname1
    xname2: str = args.xname2
    xpatchresults: Optional[str] = args.patch_results_file
    xoutput: str = args.output
    usermappingfile: Optional[str] = args.usermapping
    loglevel: str = args.loglevel
    logfilename: Optional[str] = args.logfilename
    logfilemode: str = args.logfilemode

    result = _relational_compare_generate_json(xname1, xname2, xpatchresults,
                                               usermappingfile, [],
                                               loglevel, logfilename, logfilemode)
    if not result.is_ok:
        print("ERROR: Couldn't generate app comparison results")
        exit(1)

    output = JSONRelationalReport().summary_report(JSONAppComparison(result.content))
    if xoutput:
        with open(xoutput, "w") as fp:
            fp.write(output)
    else:
        print(output)

    exit(0)


def relational_compare_function_cmd(args: argparse.Namespace) -> NoReturn:

    # arguments
    xname1: str = args.xname1
    xname2: str = args.xname2
    xoutput: str = args.output
    blocks: bool = args.blocks
    xpatchresults: Optional[str] = args.patch_results_file
    details: bool = args.details
    addresses: List[str] = args.addresses
    usermappingfile: Optional[str] = args.usermapping
    loglevel: str = args.loglevel
    logfilename: Optional[str] = args.logfilename
    logfilemode: str = args.logfilemode

    UC.set_logging(
        loglevel,
        # This feels a bit gnarly
        UC.get_path_filename(xname1)[0],
        logfilename=logfilename,
        mode=logfilemode,
        msg="relational compare function invoked")


    patchresultsdata: Optional[Dict[str, Any]] = None
    if xpatchresults is not None:
        with open(xpatchresults, "r") as fp:
            patchresultsdata = json.load(fp)

    if patchresultsdata is None:
        UC.print_error("Patch results data is missing.")
        exit(1)

    patchresults = PatchResults(patchresultsdata)

    try:
        (path1, xfile1) = UC.get_path_filename(xname1)
        UF.check_analysis_results(path1, xfile1)
        (path2, xfile2) = UC.get_path_filename(xname2)
        UF.check_analysis_results(path2, xfile2)
    except UF.CHBError as e:
        print(str(e.wrap()))
        exit(1)

    xinfo1 = XI.XInfo()
    xinfo2 = XI.XInfo()
    xinfo1.load(path1, xfile1)
    xinfo2.load(path2, xfile2)
    app1 = UC.get_app(path1, xfile1, xinfo1)
    app2 = UC.get_app(path2, xfile2, xinfo2)

    patchparticulars = PatchParticulars(patchresults, app1, app2)

    content: Dict[str, Any] = {}
    content["patchevents"] = []

    for faddr in addresses:
        if app1.has_function(faddr) and app2.has_function(faddr):
            fn1 = app1.function(faddr)
            fn2 = app2.function(faddr)
            if fn1.md5 == fn2.md5:
                chklogger.logger.warning(
                    "original function %s and its patched version are identical; "
                    + "both have md5 %s",
                    faddr, fn1.md5)
                continue
            if patchparticulars.has_patch_event(fn1):
                fnpeparticulars = patchparticulars.patchevent_particulars(
                    fn1, fn2)
                if fnpeparticulars is None:
                    chklogger.logger.critical(
                        "patch validation for for function %s could not be "
                        + " completed",
                        faddr)
                    continue
                result = fnpeparticulars.to_json_result()
                if result.is_ok:
                    content["patchevents"].append(result.content)
                else:
                    chklogger.logger.warning(
                        "error in patch validation for function %s: %s",
                        faddr, result.reason)

    jsonresult = JU.jsonok("patchvalidation", content)
    if xoutput is not None:
        UC.print_status_update(
            "Relational function compare results saved in " + xoutput)
        with open(xoutput, "w") as fp:
            json.dump(jsonresult, fp)
    else:
        print(json.dumps(jsonresult))

    chklogger.logger.info("relational compare function completed")
    exit(0)


def relational_compare_cfgs_cmd(args: argparse.Namespace) -> NoReturn:

    # arguments
    xname1: str = args.xname1
    xname2: str = args.xname2
    xpatchresults: Optional[str] = args.patch_results_file
    usermappingfile: Optional[str] = args.usermapping
    showcalls: bool = args.show_calls
    showpredicates: bool = args.show_predicates
    outputfilename: str = args.outputfilename
    fileformat: str = args.format
    loglevel: str = args.loglevel
    logfilename: Optional[str] = args.logfilename
    logfilemode: str = args.logfilemode

    print("Visual comparison of the cfgs for " + xname1 + " and " + xname2)

    try:
        (path1, xfile1) = UC.get_path_filename(xname1)
        UF.check_analysis_results(path1, xfile1)
        (path2, xfile2) = UC.get_path_filename(xname2)
        UF.check_analysis_results(path2, xfile2)
    except UF.CHBError as e:
        print(str(e.wrap()))
        exit(1)

    UC.set_logging(
        loglevel,
        path1,
        logfilename=logfilename,
        mode=logfilemode,
        msg="relational compare cfgs invoked")

    patchevents: Dict[str, PatchEvent] = {} # start of wrapper -> patch event

    patchresultsdata: Optional[Dict[str, Any]] = None
    if xpatchresults is not None:
        with open(xpatchresults, "r") as fp:
            patchresultsdata = json.load(fp)

    if patchresultsdata is not None:
        patchresults = PatchResults(patchresultsdata)
        for event in patchresults.events:
            if (
                    event.is_trampoline
                    or event.is_trampoline_pair_minimal_2_and_3):
                if event.has_wrapper():
                    startaddr = event.wrapper.vahex
                    patchevents[startaddr] = event

    usermapping: Dict[str, str] = {}
    if usermappingfile is not None:
        if os.path.isfile(usermappingfile):
            with open(usermappingfile, "r") as fp:
                userdata = json.load(fp)
                usermapping = userdata["function-mapping"]
        else:
            UC.print_error(
                "Usermapping file " + usermappingfile + " not found")
            exit(1)

    xinfo1 = XI.XInfo()
    xinfo2 = XI.XInfo()
    xinfo1.load(path1, xfile1)
    xinfo2.load(path2, xfile2)
    app1 = UC.get_app(path1, xfile1, xinfo1)
    app2 = UC.get_app(path2, xfile2, xinfo2)

    relanalysis = RelationalAnalysis(app1, app2, usermapping=usermapping, patchevents=patchevents)

    functionschanged = relanalysis.functions_changed()
    if len(functionschanged) == 0:
        UC.print_error("No functions changed")
        exit(0)

    dotgraphs: List[DotCfg] = []

    for faddr in functionschanged:
        if faddr in relanalysis.function_mapping:
            fnanalysis = relanalysis.function_analysis(faddr)
            blockschanged = fnanalysis.blocks_changed()
            cfgmatcher = fnanalysis.cfgmatcher
            (dotcfg1, dotcfg2) = cfgmatcher.dot_cfgs(
                blockschanged=blockschanged,
                showcalls=showcalls, showpredicates=showpredicates)
            dotgraphs.extend([dotcfg1, dotcfg2])
        else:
            dotcfgremoved = DotCfg(
                "removed",
                app1.function(faddr),
                showcalls=showcalls,
                showpredicates=showpredicates,
                subgraph=True)
            dotgraphs.append(dotcfgremoved)

    newfunctions = relanalysis.functions_added()
    for faddr in newfunctions:
        dotcfgnew = DotCfg(
            "new",
            app2.function(faddr),
            defaultcolor="orange",
            showcalls=showcalls,
            showpredicates=showpredicates,
            subgraph=True)
        dotgraphs.append(dotcfgnew)

    pdffilename = UD.print_dot_subgraphs(
        app1.path,
        "cfg_comparison",
        outputfilename,
        fileformat,
        [dotcfg.build() for dotcfg in dotgraphs])

    print(relational_header(
        xname1, xname2, xinfo2.md5, "control-flow-graph comparison"))
    if os.path.isfile(pdffilename):
        UC.print_info(
            "Control flow graph comparison for "
            + "vulnerable/patched"
            + " has been saved in "
            + pdffilename
            + "\n  - Basic blocks changed or new are shown in orange"
            + "\n  - Basic blocks unchanged (md5-equal) are shown in blue")
    else:
        UC.print_error(
            "Error in converting dot file to pdf")
        exit(1)

    print("=" * 80)
    print("||" + (str(datetime.datetime.now()) + "  ").rjust(76) + "||")
    print("=" * 80)

    chklogger.logger.info("relational compare cfgs completed")

    exit(0)


def relational_compare_md5s_cmd(args: argparse.Namespace) -> NoReturn:

    # arguments
    xname1: str = args.xname1
    xname2: str = args.xname2

    print("Comparison of the function md5s of " + xname1 + " and " + xname2)

    try:
        (path1, xfile1) = UC.get_path_filename(xname1)
        UF.check_analysis_results(path1, xfile1)
        (path2, xfile2) = UC.get_path_filename(xname2)
        UF.check_analysis_results(path2, xfile2)
    except UF.CHBError as e:
        print(str(e.wrap()))
        exit(1)

    xinfo1 = XI.XInfo()
    xinfo2 = XI.XInfo()
    xinfo1.load(path1, xfile1)
    xinfo2.load(path2, xfile2)
    app1 = UC.get_app(path1, xfile1, xinfo1)
    app2 = UC.get_app(path2, xfile2, xinfo2)

    md5s1 = app1.function_md5s
    md5s2 = app2.function_md5s

    comparison: Dict[str, Optional[str]] = {}

    for (f1, md51) in md5s1.items():
        if f1 in md5s2:
            md52 = md5s2[f1]
            if md52 == md51:
                comparison[f1] = "equal"
            else:
                comparison[f1] = "different"
        else:
            comparison[f1] = "missing"

    for (f2, md52) in md5s2.items():
        if f2 in comparison:
            continue
        else:
            comparison[f2] = "new"

    eqcount: int = 0

    neq: List[str] = []
    missing: List[str] = []
    newfns: List[str] = []

    for (f, md5) in comparison.items():
        if comparison[f] == "equal":
            eqcount += 1
        elif comparison[f] == "different":
            neq.append(f)
        elif comparison[f] == "missing":
            missing.append(f)
        elif comparison[f] == "new":
            newfns.append(f)

    md5sdict: Dict[str, Tuple[List[str], List[str]]] = {}

    for (f, md5) in md5s1.items():
        md5sdict.setdefault(md5, ([], []))
        md5sdict[md5][0].append(f)

    for (f, md5) in md5s2.items():
        md5sdict.setdefault(md5, ([], []))
        md5sdict[md5][1].append(f)

    print("Md5 comparison")
    print("=" * 80)
    print("Equal: " + str(eqcount))
    print("")
    print("Different: " + str(len(neq)) + "\n" + ", ".join(neq))
    print("")
    print("Missing: " + str(len(missing)) + "\n" + ", ".join(missing))
    print("")
    print("New functions: " + str(len(newfns)) + "\n" + ", ".join(newfns))
    print("")

    print("\nmd5 mapping")
    for (md5, t) in sorted(md5sdict.items()):
        print(md5 + "   " + str(t))

    count = 0
    countall = 0
    print("\nmd5s that appear in both")
    for (md5, t) in sorted(md5sdict.items()):
        if len(t[0]) > 0 and len(t[1]) > 0:
            count += 1
            if len(t[0]) == len(t[1]):
                countall += len(t[0])
            else:
                print(" *** lengths are different")
            print(str(t[0]) + " ===> " + str(t[1]))

    print("\nPartial matches: " + str(count))
    print("All matches: " + str(countall))

    exit(0)


def relational_compare_invs_cmd(args: argparse.Namespace) -> NoReturn:

    # arguments
    xname1: str = args.xname1
    xname2: str = args.xname2
    usermappingfile: Optional[str] = args.usermapping
    loglevel: str = args.loglevel
    logfilename: Optional[str] = args.logfilename
    logfilemode: str = args.logfilemode

    print("Comparison of the invariants for " + xname1 + " and " + xname2)

    try:
        (path1, xfile1) = UC.get_path_filename(xname1)
        UF.check_analysis_results(path1, xfile1)
        (path2, xfile2) = UC.get_path_filename(xname2)
        UF.check_analysis_results(path2, xfile2)
    except UF.CHBError as e:
        print(str(e.wrap()))
        exit(1)

    UC.set_logging(
        loglevel,
        path1,
        logfilename=logfilename,
        mode=logfilemode,
        msg="relational compare invariants invoked")

    usermapping: Dict[str, str] = {}
    if usermappingfile is not None:
        if os.path.isfile(usermappingfile):
            with open(usermappingfile, "r") as fp:
                userdata = json.load(fp)
                usermapping = userdata["function-mapping"]
        else:
            UC.print_error(
                "Usermapping file " + usermappingfile + " not found")
            exit(1)

    xinfo1 = XI.XInfo()
    xinfo2 = XI.XInfo()
    xinfo1.load(path1, xfile1)
    xinfo2.load(path2, xfile2)
    app1 = UC.get_app(path1, xfile1, xinfo1)
    app2 = UC.get_app(path2, xfile2, xinfo2)

    relanalysis = RelationalAnalysis(app1, app2, usermapping=usermapping)

    functionschanged = relanalysis.functions_changed()
    if len(functionschanged) == 0:
        UC.print_error("No functions changed")
        exit(0)

    invlost: int  = 0

    if True:
        functionschanged = relanalysis.functions_changed()
        f1fn = app1.function(functionschanged[0])
        f2fn = app2.function(functionschanged[0])

        f1invariants = f1fn.invariants
        f2invariants = f2fn.invariants

        f1table: Dict[str, Dict[str, NonRelationalValue]] = {}
        f2table: Dict[str, Dict[str, NonRelationalValue]] = {}
        for loc in f1invariants:
            for fact in f1invariants[loc]:
                if fact.is_nonrelational and not "@" in str(fact.variable):
                    fact = cast(NRVFact, fact)
                    f1table.setdefault(loc, {})
                    if str(fact.variable) != "PC":
                        f1table[loc][str(fact.variable)] = fact.value
        for loc in f2invariants:
            for fact in f2invariants[loc]:
                if fact.is_nonrelational and not "@" in str(fact.variable):
                    fact = cast(NRVFact, fact)
                    f2table.setdefault(loc, {})
                    if str(fact.variable) != "PC":
                        f2table[loc][str(fact.variable)] = fact.value
        comparison: Dict[str, Dict[
            str,
            Tuple[Optional[NonRelationalValue],
                  Optional[NonRelationalValue]]]] = {}
        for loc in f1table:
            comparison.setdefault(loc, {})
            f1values = f1table[loc]
            if loc in f2table:
                f2values = f2table[loc]
                for v1 in f1values:
                    if v1 in f2values:
                        f1value = f1table[loc][v1]
                        f2value = f2table[loc][v1]
                        comparison[loc][v1] = (f1value, f2value)
                    else:
                        invlost += 1
                        f1value = f1table[loc][v1]
                        comparison[loc][v1] = (f1value, None)
            else:
                for v1 in f1values:
                    comparison[loc][v1] = (f1values[v1], None)

        newblocks: Dict[str, Dict[str, NonRelationalValue]] = {}
        for loc in f2table:
            if loc not in f1table:
                newblocks.setdefault(loc, {})
                f2values = f2table[loc]
                for v2 in f2values:
                    newblocks[loc][v2] = f2values[v2]

        print(relational_header(
            xname1, xname2, xinfo2.md5, "invariant comparison"))
        counter: int = 0
        dcounter: int = 0
        print("\nInvariants modified or missing:")
        print("~" * 80)
        for loc in sorted(comparison):
            for v in sorted(comparison[loc]):
                values = comparison[loc][v]
                if str(values[0]) == str(values[1]):
                    counter += 1
                else:
                    dcounter += 1
                    print(
                        loc.ljust(12)
                        + v.ljust(32)
                        + str(values[0]).ljust(20)
                        + "  "
                        + str(values[1]))

        print("\n\n")
        print("~" * 80)
        print("Invariants lost: " + str(invlost))
        print("Invariants lost/modified: " + str(dcounter))
        print(
            "Invariants not modified: "
            + str(counter)
            + " (in "
            + str(len(f1table))
            + " locations)")
        print("~" * 80)

        if len(newblocks) > 0:
            print("\nInvariants of newly added blocks:")
            print("~" * 80)
            for loc in sorted(newblocks):
                print("\n" + loc)
                for v in sorted(newblocks[loc]):
                    newvalue = newblocks[loc][v]
                    print("  " + v.ljust(32) + str(newvalue))

    print("=" * 80)
    print("||" + (str(datetime.datetime.now()) + "  ").rjust(76) + "||")
    print("=" * 80)

    chklogger.logger.info("relational compare invariants completed")

    exit(0)


def relational_compare_elfdata(args: argparse.Namespace) -> NoReturn:

    # arguments
    xname1: str = args.xname1
    xname2: str = args.xname2

    try:
        (path1, xfile1) = UC.get_path_filename(xname1)
        (path2, xfile2) = UC.get_path_filename(xname2)
    except UF.CHBError as e:
        print(str(e.wrap()))
        exit(1)

    xinfo1 = XI.XInfo()
    xinfo1.load(path1, xfile1)

    xinfo2 = XI.XInfo()
    xinfo2.load(path2, xfile2)

    app1 = UC.get_app(path1, xfile1, xinfo1)
    app2 = UC.get_app(path2, xfile2, xinfo2)

    sectionheaders1 = app1.header.sectionheaders
    sectionheaders2 = app2.header.sectionheaders

    xcomparison = XComparison(
        False,
        path1,
        xfile1,
        path2,
        xfile2,
        app1,
        app2)

    xcomparison.compare_sections()
    xcomparison.compare_segments()

    print(xcomparison.diffs_as_table())

    exit(0)


def relational_compare_cfg_info(args: argparse.Namespace) -> NoReturn:
    """This command helps to establish a function mapping between two
    binaries. The assumption is that the two binaries are roughly
    similar, in particular that the order in which the functions appear
    is stable, but some functions may have changed in size, or some new
    functions may have been inserted.

    It only requires both binaries to have been disassembled with the
    option --save_asm_cfg_info; it does not require the binaries to have
    been analyzed.
    """

    # arguments
    xname1: str = args.xname1
    xname2: str = args.xname2
    newfunctions: List[str] = args.newfunctions

    try:
        (path1, xfile1) = UC.get_path_filename(xname1)
        (path2, xfile2) = UC.get_path_filename(xname2)
    except UF.CHBError as e:
        print(str(e.wrap()))
        exit(1)

    xinfo1 = XI.XInfo()
    xinfo1.load(path1, xfile1)

    xinfo2 = XI.XInfo()
    xinfo2.load(path2, xfile2)

    app1 = UC.get_app(path1, xfile1, xinfo1)
    app2 = UC.get_app(path2, xfile2, xinfo2)

    cfginfo1 = app1.appcfginfo
    cfginfo2 = app2.appcfginfo

    if len(cfginfo1.function_cfg_infos) == 0:
        UC.print_error(
            "No function data found for " + xname1 + " in " + path1
            + "\n Please disassemble with option -save_cfg_info")
        exit(1)

    if len(cfginfo2.function_cfg_infos) == 0:
        UC.print_error(
            "No function data found for " + xname2 + " in " + path2
            + "\n Please disassemble with option -save_cfg_info")
        exit(1)

    cfginfos1 = cfginfo1.cfg_infos
    cfginfos2 = cfginfo2.cfg_infos

    print("app1: " + str(len(cfginfos1)))
    print("app2: " + str(len(cfginfos2)))

    cfginfos2 = [x for x in cfginfos2 if x.faddr not in newfunctions]

    cfginfos2 = cfginfos2[:len(cfginfos1)]

    diffcount = 0

    for (ci1, ci2) in zip(cfginfos1, cfginfos2):
        if (
                ci1.basic_blocks == ci2.basic_blocks
                and ci1.instructions == ci2.instructions):
            cfgdiff = ""
        elif ci1.basic_blocks == ci2.basic_blocks:
            cfgdiff = (
                "diff: " +
                str(ci1.basic_blocks).rjust(8) + "  "
                + str(ci1.instructions) + " => " + str(ci2.instructions))
            diffcount += 1
        else:
            cfgdiff = (
                "diff: " +
                str(ci1.basic_blocks) + " => " + str(ci2.basic_blocks)
                + "  "
                + str(ci1.instructions) + " => " + str(ci2.instructions))
            diffcount += 1
        if ci1.name is not None and ci2.name is not None and ci1.name == ci2.name:
            name = ci1.name
        elif ci1.name is not None:
            name = ci1.name + " (original)"
        elif ci2.name is not None:
            name = ci2.name + " (patched)"
        else:
            name = ""

        print(ci1.faddr + "   " + ci2.faddr + "   " +
              str(ci2.faddr_i - ci1.faddr_i).rjust(4) + "  " + cfgdiff.ljust(24)
              + name)

    print("\nNumber of functions different: " + str(diffcount))

    exit(0)


def relational_compare_globalvars(args: argparse.Namespace) -> NoReturn:

    # arguments
    xname1: str = args.xname1
    xname2: str = args.xname2

    try:
        (path1, xfile1) = UC.get_path_filename(xname1)
        (path2, xfile2) = UC.get_path_filename(xname2)
    except UF.CHBError as e:
        print(str(e.wrap()))
        exit(1)

    xinfo1 = XI.XInfo()
    xinfo1.load(path1, xfile1)

    xinfo2 = XI.XInfo()
    xinfo2.load(path2, xfile2)

    app1 = UC.get_app(path1, xfile1, xinfo1)
    app2 = UC.get_app(path2, xfile2, xinfo2)

    memmap1 = app1.globalmemorymap
    memmap2 = app2.globalmemorymap

    if len(memmap1.locations) == 0:
        UC.print_error(
            "No memory map found for " + xname1 + " in " + path1)
        exit(1)

    if len(memmap2.locations) == 0:
        UC.print_error(
            "No memory map found for " + xname2 + " in " + path2)
        exit(1)

    glocs1 = memmap1.locations
    glocs2 = memmap2.locations

    result: Dict[str, Tuple[str, str]] = {}

    for (addr, gloc1) in sorted(glocs1.items()):
        gloc2 = memmap2.get_location_by_name(gloc1.name)
        if gloc2 is not None:
            result[addr] = (gloc1.name, gloc2.addr)

    for (addr1, (name, addr2)) in sorted(result.items()):
        diff = int(addr2, 16) - int(addr1, 16)
        print("  " + addr1.rjust(8) + "  " + addr2.rjust(8) + "  " + str(diff).rjust(8) + "  " + name)

    (loc1count, loc1coverage) = memmap1.coverage()
    (loc2count, loc2coverage) = memmap2.coverage()

    print("\nCoverage")
    print("App1: " + str(loc1count) + ", " + str(loc1coverage))
    print("App2: " + str(loc2count) + ", " + str(loc2coverage))

    exit(0)
