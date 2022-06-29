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
"""Abstract superclass of control flow graph.

Subclasses:
  - ARMCfg
  - MIPSCfg
"""

import xml.etree.ElementTree as ET

from typing import (
    Any,
    cast,
    Dict,
    List,
    Mapping,
    NewType,
    Optional,
    Sequence,
    Set,
    Tuple,
    TYPE_CHECKING, Union)

from chb.app.CfgBlock import CfgBlock
from chb.app.DerivedGraphSequence import DerivedGraphSequence

import chb.ast.ASTNode as AST
from chb.astinterface.ASTInterface import ASTInterface

import chb.util.tingly as tingly

import chb.invariants.XXprUtil as XU

import chb.util.fileutil as UF

if TYPE_CHECKING:
    from chb.app.Function import Function

class Cfg:

    def __init__(
            self,
            faddr: str,
            xnode: ET.Element) -> None:
        self._faddr = faddr
        self.xnode = xnode
        self._edges: Dict[str, List[str]] = {}
        self._graphseq: Optional[DerivedGraphSequence] = None

    @property
    def faddr(self) -> str:
        return self._faddr

    @property
    def blocks(self) -> Mapping[str, CfgBlock]:
        raise UF.CHBError("Property blocks not implemented for Cfg")

    @property
    def edges(self) -> Mapping[str, Sequence[str]]:
        if len(self._edges) == 0:
            xedges = self.xnode.find("edges")
            if xedges is None:
                raise UF.CHBError("Edges are missing from cfg xml")
            for e in xedges.findall("e"):
                src = e.get("src")
                if src is None:
                    raise UF.CHBError("Src address is missing from cfg")
                tgt = e.get("tgt")
                if tgt is None:
                    raise UF.CHBError("Tgt address is missing from cfg")
                self._edges.setdefault(src, [])
                self._edges[src].append(tgt)
        return self._edges

    def modify_edges(
            self,
            remove: List[Tuple[str, str]],
            add: List[Tuple[str, str]]) -> None:
        for (src, tgt) in remove:
            for (s, tl) in self.edges.items():
                if s == src:
                    if tgt in tl:
                        tgtlist: List[str] = [x for x in tl]
                        tgtlist.remove(tgt)
                        self._edges[src] = tgtlist
        for (src, tgt) in add:
            for (s, tl) in self.edges.items():
                if s == src:
                    if tgt not in tl:
                        tgtlist = [x for x in tl]
                        tgtlist.append(tgt)
                        self._edges[src] = tgtlist

    @property
    def edges_as_set(self) -> Set[Tuple[str, str]]:
        result: Set[Tuple[str, str]] = set([])
        for src in self.edges:
            for dst in self.edges[src]:
                result.add((src, dst))
        return result

    @property
    def derived_graph_sequence(self) -> DerivedGraphSequence:
        if self._graphseq is None:
            nodes = list(self.blocks.keys())
            self._graphseq = DerivedGraphSequence(self.faddr, nodes, self.edges)
        return self._graphseq

    @property
    def is_reducible(self) -> bool:
        return self.derived_graph_sequence.is_reducible

    @property
    def rpo_sorted_nodes(self) -> List[str]:
        """Return a list of block addresses in reverse postorder."""

        if self.is_reducible:
            return self.derived_graph_sequence.rpo_sorted_nodes
        else:
            return []

    def analyze_loops(self):
        rg = tingly.RootedDiGraph(self.derived_graph_sequence.nodes,
                                    self.derived_graph_sequence.edges,
                                    self.derived_graph_sequence.graphs[0].nodes[0])
        ipostdoms = rg.ipostdoms()

        def initial_loop_header_identification() -> Tuple[Dict[str, int], Set[Tuple[str, str]]]:
            loopdepths : Dict[str, int] = {}
            loopcandidates : Set[Tuple[str, str]] = set()

            for n, gn in enumerate(self.derived_graph_sequence.graphs):
                for header, gin in gn.intervals.items():
                    print(f'header for interval at graph level {n=} is {header=}')
                    for src in gin.edges:
                        for tgt in gin.edges[src]:
                            print(' ' * n + f"considering edge {src=} -> {tgt=} at loop level {n=}")
                            if tgt == header:
                                assert (header not in loopdepths or loopdepths[header] == n)
                                loopdepths[header] = n
                                # The src node is in an interval at level n, but we're ultimately
                                # interested in the node(s) within the equivalent interval(s) at
                                # level 0.
                                loopcandidates.add( (header, src) )
            return loopdepths, loopcandidates

        def expand_interval_nodes(node, level) -> List[str]:
            return self.derived_graph_sequence.graphs[level - 1].intervals[node].nodes

        def find_level_0_backedges(loopcandidates : List[Tuple[str, str]],
                                   loopdepths : Dict[str, int]
                                  ) -> List[Tuple[int, Tuple[str, str]]]:
            backedge_levels : List[Tuple[int, str, str]] = []
            for hdr, src_n in loopcandidates:
                # The worklist contains interval nodes targeting hdr with a backedge.
                # For interval depths > 0, we need to (recursively) peek inside the
                # interval to find the node within it which contains the backedge.
                worklist = [ (src_n, loopdepths[hdr], loopdepths[hdr]) ]
                while len(worklist) > 0:
                    (src, n, norig) = worklist.pop()
                    if n == 0:
                        print(f"found level-0 backedge from {src} to {hdr}")
                        backedge_levels.append( (norig, (src, hdr)) )
                    else:
                        for node in expand_interval_nodes(src, n):
                            for tgt in self.successors(node):
                                if tgt == hdr:
                                    print(f"found backedge at level {n-1=} from {node} to {hdr}")
                                    worklist.append( (node, n - 1, norig) )
            return backedge_levels

        def determine_loop_circuit(
                    backedge_levels: List[Tuple[int, str, str]]
                ) -> Dict[str, List[str]]:
            incircuit : Dict[str, List[str]] = {}
            preds = self.derived_graph_sequence.graphs[0].revedges

            # We iterate by level to ensure that each node
            # is associated with the innermost nested loop which contains it.
            backedge_levels.sort(key=lambda tup: tup[0])

            # The nodes in a loop's circuit are found by iterating backwards from
            # the latch until we find the header.
            for _level, (src_n, header) in backedge_levels:
                print(f'         collecting circuit body of {_level, (src_n, header)=}')
                worklist = [src_n]
                seen = set(worklist)
                while worklist:
                    node = worklist.pop()
                    if not node in incircuit:
                        incircuit[node] = []
                    incircuit[node].append(header)
                    if node != header:
                        for prev in preds[node]:
                            if not prev in seen:
                                seen.add(prev)
                                worklist.append(prev)

            return incircuit

        def determine_loop_scope(
                    backedge_levels: List[Tuple[int, str, str]],
                    afterloop: Dict[str, Optional[str]]
                ) -> Dict[str, List[str]]:
            inscope : Dict[str, List[str]] = {}
            succs = self.derived_graph_sequence.graphs[0].edges

            header_levels = list(set((level, header) for level, (_, header) in backedge_levels))
            headers = set(header for _, header in header_levels)

            # We iterate by level to ensure that each node
            # is associated with the innermost nested loop which contains it.
            # Largest first, because that's the nature of syntax.
            header_levels.sort(key=lambda tup: tup[0], reverse=True)

            # The nodes in a loop's scope are found by iterating forwards from
            # the header until we find the the follow.
            for _level, header in header_levels:
                other_headers = headers - {header}
                worklist = [header]
                seen = set(worklist)
                print(f'         collecting scope body of {(_level, header)=}; {other_headers=}')

                def known_different_scope(node):
                    return node == afterloop[header] or node in other_headers

                while worklist:
                    node = worklist.pop()
                    if not node in inscope:
                        inscope[node] = []
                    if known_different_scope(node):
                        continue
                    print(f'             marking {node=} as part of scope of {header=}')
                    inscope[node].append(header)
                    for next in succs[node]:
                        if not next in seen:
                            seen.add(next)
                            worklist.append(next)

            return inscope

        def classify_loop(src, header, n: int, ipostdoms) -> str:
            print(f"loop candidate {header=} found at graph level {n=} with backedge from {src=}")

            hdrlen = len(self.successors(header))
            latchlen = len(self.successors(src))
            if ipostdoms[header] == None:
                return 'endless'
            elif hdrlen == 2 and latchlen == 1:
                return 'while'
            elif hdrlen == 1 and latchlen == 2:
                return 'do-while'
            elif hdrlen == 1 and latchlen == 1:
                # Probably a while-like loop, albeit with an internal goto somewhere;
                # the fact that the postdominator exists implies that it's possible to
                # exit the loop.
                return 'internal-control'
            else:
                if hdrlen == 2 and latchlen == 2 and header == src:
                    # Some while loops get optimized to a single self-looping node.
                    return 'while'

                return 'undetermined'

        def determine_loopfollow(src, hdr, inloop, looptype) -> Optional[str]:
            """The follow node is the one which executes on the way out of the loop.
               The follow may be printed within the sytactic block of the loop,
               or it may be the statement after the loop (targeted by a break).
               The loopfollow is not owned by the loop, even when printed within it."""
            if looptype == 'while':
                succs = self.successors(hdr)
                assert len(succs) == 2
                if succs[0] in inloop and inloop[succs[0]][0] == hdr:
                    return succs[1]
                else:
                    return succs[0]
            elif looptype == 'do-while':
                succs = self.successors(src)
                assert len(succs) == 2
                if succs[0] in inloop and inloop[succs[0]][0] == hdr:
                    return succs[1]
                else:
                    return succs[0]
            elif looptype == 'endless':
                return None
            elif looptype == 'internal-control':
                return ipostdoms[hdr]
            else:
                return None

        loopdepths, loopcandidates = initial_loop_header_identification()
        backedge_levels = find_level_0_backedges(loopcandidates, loopdepths)
        incircuit = determine_loop_circuit(backedge_levels)
        
        import pprint
        print(f"incircuit:")
        pprint.pprint(incircuit, indent=4)
        print(f"{loopcandidates=}")
        print(f"{backedge_levels=}")

        loopsignatures = []
        for norig, (src, hdr) in backedge_levels:
            looptype = classify_loop(src, hdr, norig, ipostdoms)

            if hdr in incircuit and incircuit[hdr][0] != hdr:
                print(f"           discarding loop candidate {(hdr,src,looptype,norig)=} since the header belongs to another loop ({incircuit[hdr]})")
            elif src in incircuit and incircuit[src][0] != hdr:
                print(f"           discarding loop candidate {(hdr,src,looptype,norig)=} since the latch belongs to another loop ({incircuit[src]})")
            else:
                loopfollow = determine_loopfollow(src, hdr, incircuit, looptype)
                loopsignatures.append( (hdr, src, looptype, loopfollow, norig) )

        
        loopfollows = {}
        for hdr, src, looptype, loopfollow, norig in loopsignatures:
            loopfollows[hdr] = loopfollow

        afterloop = {}
        for hdr in loopfollows.keys():
            pdom = ipostdoms[hdr]
            while pdom != None and pdom in incircuit and hdr in incircuit[pdom]:
                pdom = ipostdoms[pdom]
            afterloop[hdr] = pdom
        afterloop.setdefault(None)

        inscope = determine_loop_scope(backedge_levels, afterloop)
        print(f"inscope:")
        pprint.pprint(inscope, indent=4)


        print(f"loopsignatures:")
        pprint.pprint(loopsignatures, indent=4)
        
        backedges = set(edge for _, edge in backedge_levels)
        return (incircuit, inscope, backedges, loopsignatures, loopfollows, afterloop, rg)

    def is_returning(self, stmt: AST.ASTStmt) -> bool:
        if isinstance(stmt, AST.ASTReturn):
            return True
        if isinstance(stmt, AST.ASTBlock):
            return self.is_returning(stmt.stmts[-1])
        return False

    def stmt_ast(
            self,
            fn: "Function",
            astree: ASTInterface,
            blockstmts: Dict[str, AST.ASTStmt]) -> AST.ASTNode:
        
        self.derived_graph_sequence.to_dot("/home/ben/", "nustmtast")
        for id in blockstmts.keys():
            from chb.ast.ASTCPrettyPrinter import ASTCPrettyPrinter
            pp = ASTCPrettyPrinter(astree.astree.symboltable)
            pp.stmt_to_c(blockstmts[id])
            sep = "\n     "
            c = sep.join(str(pp.ccode).split("\n"))
            print(f'{id} ==>{sep}{c}')

        incircuit, inscope, all_backedges, loopsignatures, loopfollows, afterloop, rg = self.analyze_loops()
        
        def loop_scope_for_node_is(n: str, tgt: str) -> bool:
            return n in inscope and len(inscope[n]) > 0 and inscope[n][0] == tgt

        idoms = rg.idoms
        ipostdoms = rg.ipostdoms()

        print(f"{idoms=}")
        print(f'{ipostdoms=}')
        import pprint
        pprint.pprint(rg._edge_flavors, indent=4)

        print(f'loopfollows:')
        pprint.pprint(loopfollows, indent=4)
        print(f'afterloop:')
        pprint.pprint(afterloop, indent=4)

        loopheaders = set(sig[0] for sig in loopsignatures)
        latchingnodes = set(src for src, tgt in all_backedges)
        twowayconds = rg.two_way_conditionals(loopheaders, latchingnodes)

        print(f'twowayconds:')
        pprint.pprint(twowayconds, indent=4)

        gotoedges = set()
        # Some edges into multi-predecessor nodes must become gotos.
        # Backedges within a loop don't count; they are implicitly represented
        # (and, if not, would be represented with `continue`s). But we might need
        # a goto for a backedge that crosses between loops.
        # Similarly, the join points for two-way conditionals are exempt.
        # For the remainder, one arbitrarily chosen edge is exempt, and the others
        # must use gotos.
        ifjoinpoints = set(twowayconds.values())
        print(f'{ifjoinpoints=}')
        for tgt in rg.rpo_sorted: # outer
            print(f'considering goto target {tgt}')
            preds = rg.pre(tgt)
            if len(preds) <= 1 or tgt in ifjoinpoints:
                continue # to outer
            print(f'{len(preds)=} for {tgt=}')

            # If any predecessor is a tree edge, the others need gotos.
            # If none are tree edges, one will be chosen arbitrarily
            # to not need a goto.
            exempted_one_pred = any(rg.edge_flavor(p, tgt) == 'tree' for p in preds)

            for p in preds: # inner
                edge = (p, tgt)
                if rg.edge_flavor(p, tgt) == 'tree':
                    print(f'tree {edge=} cannot be a goto')
                    continue
                if edge in all_backedges:
                    if loop_scope_for_node_is(p, tgt):
                        print(f"      skipping edge {edge=} because the pred is in the scope of the target")
                        continue # to inner
                    else:
                        print(f"  not skipping edge {edge=} because the pred is not in the scope of the target")
                if not exempted_one_pred:
                    exempted_one_pred = True
                    print(f"     exempting edge {edge=} from gotos because it was the first leading to the target")
                else:
                    print(f"     adding goto edge {edge=}")
                    gotoedges.add(edge)
        print(f"######## eventually got {gotoedges=}")

        non_goto_backedges = all_backedges - gotoedges

        # Cifuentes used mutable state to toggle labels as needed when used
        # by gotos. We generate label AST nodes before the gotos are emitted, so we
        # need a conservative approximation of the labels that might be used.
        cross_edges = set(e for e, flavor in rg._edge_flavors.items() if flavor == 'cross')
        labeled_stmts = set(tgt for _, tgt in gotoedges | cross_edges)

        breakedges = set()
        # For each loop header, the break target is the first *out of the loop*
        # postdominating node, and the break edges are those *from in the loop*
        # targeting it.
        for hdr in loopheaders:
            pdom = afterloop[hdr]
            print(f"::break target for {hdr=} is {pdom=} {inscope[pdom] if pdom in inscope else None}")
            for src in rg.edges:
                for tgt in rg.edges[src]:
                    if tgt == pdom:
                        # The src node need not be "owned" by the loop, since non-owned
                        # nodes can appear within the syntactic scope of the loop.
                        if rg.dominates(hdr, src) and not rg.dominates(pdom, src):
                            print(f"::::adding break edge owned by {hdr=} : {(src,tgt)=}")
                            breakedges.add( (src, tgt) )

        def emit(n: str) -> List[AST.ASTStmt]:
            if n in labeled_stmts:
                return [astree.mk_label_stmt(n), blockstmts[n]]
            return [blockstmts[n]]

        constructed_stmts = set()
        def construct(
                n: str,
                follow: Optional[str],
                loopheader: Optional[str],
                result: List[AST.ASTStmt]) -> AST.ASTStmt:
            # `follow` is a marker indicating the join point of an `if` branch.

            def possible_loop_latch_branch(succ, follownode) -> AST.ASTStmt:
                if (n, succ) in non_goto_backedges:
                    # don't infinitely recurse!
                    return astree.mk_block([])

                if (n, succ) in breakedges:
                        print(f"emitting break at edge {n=}->{succ=}  {loopheader=}")
                        print(f"    {inscope[n] if n in inscope else None=}")
                        print(f"    {inscope[succ] if succ in inscope else None=}")
                        return astree.mk_break_stmt()

                return construct(succ, follownode, loopheader, [])

            print(f"construct({n=}, {follow=}, {loopheader=})")
            if follow and n == follow:
                return astree.mk_block(result)

            if n in constructed_stmts:
                print(f"###########################  already constructed {n=}; emitting an unexpected goto")
                return astree.mk_block(result + [astree.mk_goto_stmt(n)])
            else:
                constructed_stmts.add(n)

            if len(self.successors(n)) == 0:
                return astree.mk_block(result + emit(n))

            if loop_scope_for_node_is(n, n) and loopheader != n:
                # Loop headers are those for which `inloop[n][0] == n`.
                # When we encounter it the first time, we recur with
                # a new `loopheader` flag so that we don't infinitely recurse.
                print(f"encountered loop header node {n=}, {len(result)=}")
                follownode = afterloop[n]
                print(f'{follownode=} for {n=} ; {loopheader=}')
                constructed_stmts.remove(n)
                body = construct(n, follow, n, [])
                loop = astree.mk_loop(body)
                if follownode:
                    # In rare cases, the follow node may have multiple predecessors.
                    # In order to avoid emitting the same nodes multiple times, we
                    # need to instead emit a goto for all but one of the predecessor
                    # loops.


                    # Continue slurping up nodes past the loop we just constructed
                    return construct(
                        follownode, follow, loopheader, result + [loop])
                else:
                    # No more nodes to slurp up; return what we have so far, plus our loop
                    if result == []:
                        return loop
                    return astree.mk_block(result + [loop])
                assert False # make sure we don't accidentally fall through!

            if len(self.successors(n)) == 1:
                next = self.successors(n)[0]
                if (n, next) in non_goto_backedges:
                    if loopheader == next:
                        print(f"ending construct early at {n=} {next=} due to backedge...")
                        return astree.mk_block(result + emit(n))
                    else:
                        print(f"ending construct early (different loopheader) at {n=} {next=} due to backedge...")
                        return astree.mk_block(result + emit(n))

                if (n, next) in breakedges:
                        print(f"emitting break at edge {n=}->{next=}  {loopheader=}")
                        print(f"    {inscope[n] if n in inscope else None=}")
                        print(f"    {inscope[next] if next in inscope else None=}")
                        return astree.mk_block(result + emit(n) + [astree.mk_break_stmt()])

                if (n, next) in gotoedges:
                    print(f"ending construct early at {n=} due to goto...")
                    return astree.mk_block(result + emit(n) + [astree.mk_goto_stmt(next)])    

                print((n,next), 'was not in gotoedges')
                return construct(next, follow, loopheader, result + emit(n))

            elif len(self.successors(n)) == 2:
                if n in twowayconds:
                    follownode: Optional[str] = twowayconds[n]
                else:
                    follownode = None
                truside = self.successors(n)[1]
                falside = self.successors(n)[0]
                ifbranch = possible_loop_latch_branch(truside, follownode)
                elsebranch = possible_loop_latch_branch(falside, follownode)

                pcoffset = ( (int(truside, 16) - int(falside, 16)) - 2)
                if ifbranch.is_empty():
                    condition = fn.blocks[n].assembly_ast_condition(
                        astree, reverse=True)
                    bstmt = astree.mk_branch(
                        condition, elsebranch, ifbranch, pcoffset)
                else:
                    condition = fn.blocks[n].assembly_ast_condition(astree)
                    if (
                            (not elsebranch.is_empty())
                            and condition
                            and condition.is_ast_binary_op):
                        cond = cast(AST.ASTBinaryOp, condition)
                        if cond.op in ["neq", "ne"]:
                            condition = astree.mk_binary_expression(
                                "eq", cond.exp1, cond.exp2)
                            bstmt = astree.mk_branch(
                                condition, elsebranch, ifbranch, pcoffset)
                        else:
                            bstmt = astree.mk_branch(
                                condition, ifbranch, elsebranch, pcoffset)
                    else:
                        bstmt = astree.mk_branch(
                            condition, ifbranch, elsebranch, pcoffset)
                branchinstr = fn.blocks[n].last_instruction
                astree.add_instruction_span(
                    bstmt.assembly_xref, branchinstr.iaddr, branchinstr.bytestring)

                print(f',,,,,, handling continuation of 2-succ node {n=} {loopheader=} {follownode=} {follow=}')
                if follownode:
                    return construct(
                        follownode, follow, loopheader, result + emit(n) + [bstmt])
                else:
                    return astree.mk_block(result + emit(n) + [bstmt])
            else:
                raise UF.CHBError("Multi branch for " + n)

        return construct(self.faddr, None, None, [])

    def assembly_ast(
            self,
            fn: "Function",
            astree: ASTInterface) -> AST.ASTNode:
        blockstmts: Dict[str, AST.ASTStmt] = {}
        for n in self.rpo_sorted_nodes:
            blocknode = fn.blocks[n].assembly_ast(astree)
            blockstmts[n] = blocknode

        return self.stmt_ast(fn, astree, blockstmts)

    def ast(self,
            fn: "Function",
            astree: ASTInterface) -> AST.ASTNode:
        blockstmts: Dict[str, AST.ASTStmt] = {}
        for n in self.rpo_sorted_nodes:
            blocknode = fn.blocks[n].ast(astree)
            if fn.blocks[n].has_return:
                instr = fn.blocks[n].last_instruction
                rv = instr.return_value()
                if rv is not None:
                    astexprs: List[AST.ASTExpr] = XU.xxpr_to_ast_exprs(rv, astree)
                else:
                    astexprs = []
                astexpr = astexprs[0] if len(astexprs) == 1 else None
                rtnstmt = astree.mk_return_stmt(astexpr)
                blocknode = astree.mk_block([blocknode, rtnstmt])
            blockstmts[n] = blocknode

        return self.stmt_ast(fn, astree, blockstmts)

    def max_loop_level(self) -> int:
        return max([len(self.blocks[b].looplevels) for b in self.blocks])

    def has_loop_level(self, baddr: str) -> bool:
        if baddr in self.blocks:
            return len(self.blocks[baddr].looplevels) > 0
        else:
            return False

    def has_loops(self) -> bool:
        return self.max_loop_level() > 0

    def loop_levels(self, baddr: str) -> Sequence[str]:
        if baddr in self.blocks:
            return self.blocks[baddr].looplevels
        else:
            raise UF.CHBError("Blockaddress " + baddr + " not found in cfg")

    def successors(self, src: str) -> Sequence[str]:
        """Addresses of the successor basic blocks.

        For an if-then-else branch the else branch is the first successor.
        """
        if src in self._edges:
            return self._edges[src]
        else:
            return []

    def __str__(self) -> str:
        lines: List[str] = []
        lines.append("Basic blocks: ")
        for b in self.blocks:
            lines.append(str(b))
        lines.append("\nEdges: ")
        for e in self.edges:
            lines.append(e.ljust(6) + "  [" + ", ".join(self.edges[e]) + "]")
        return "\n".join(lines)
