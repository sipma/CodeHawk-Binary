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
    TYPE_CHECKING)

from chb.app.CfgBlock import CfgBlock
from chb.app.DerivedGraphSequence import DerivedGraphSequence

import chb.ast.ASTNode as AST
from chb.astinterface.ASTInterface import ASTInterface

import chb.util.tingly as tingly

import chb.invariants.XXprUtil as XU

import chb.util.fileutil as UF

if TYPE_CHECKING:
    from chb.app.Function import Function

def loop_scope_for_node_is(n: str, tgt: str, inscope) -> bool:
    return n in inscope and len(inscope[n]) > 0 and inscope[n][0] == tgt

class LoopAnalysis:
    def __init__(self, dgs: DerivedGraphSequence):
        self.derived_graph_sequence = dgs
    
    def _initial_loop_header_identification(self) \
            -> Tuple[Dict[str, int], Set[Tuple[str, str]]]:
        loopdepths : Dict[str, int] = {}
        loopcandidates : Set[Tuple[str, str]] = set()

        for n, gn in enumerate(self.derived_graph_sequence.graphs):
            for header in sorted(gn.intervals.keys()):
                gin = gn.intervals[header]
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

    def _find_level_0_backedges(self, fg,
                               loopdepths : Dict[str, int],
                               loopcandidates : List[Tuple[str, str]],
                                ) -> List[Tuple[int, Tuple[str, str]]]:
        
        def expand_interval_nodes(node, level) -> List[str]:
            return self.derived_graph_sequence.graphs[level - 1].intervals[node].nodes

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
                        if hdr in fg.post(node):
                            print(f"found backedge at level {n-1=} from {node} to {hdr}")
                            worklist.append( (node, n - 1, norig) )
        return backedge_levels


    def _determine_loop_circuit(self, fg,
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
                assert fg.dominates(header, node)

                if not node in incircuit:
                    incircuit[node] = []
                incircuit[node].append(header)
                if node != header:
                    print("         adding unseen predecessors of", node, "to worklist:", [p for p in preds[node] if not p in seen])
                    for prev in preds[node]:
                        if not prev in seen:
                            seen.add(prev)
                            worklist.append(prev)

        return incircuit

    def _determine_loop_scope(self,
                rg: tingly.RootedDiGraph,
                backedge_levels: List[Tuple[int, str, str]],
                afterloop: Dict[str, Optional[str]],
                incircuit: Dict[str, List[str]],
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

            def process(n):
                if not n in seen:
                    seen.add(n)
                    worklist.append(n)

            while worklist:
                node = worklist.pop()
                if not node in inscope:
                    inscope[node] = []
                if node == afterloop[header]:
                    continue
                if node in other_headers:
                    # Ignore the body of the loop, but the follow node can be ours,
                    # assuming it has only a single predecessor.
                    for next in succs[node]:
                        if next in incircuit and node in incircuit[next]:
                            continue
                        if len(rg.pre(next)) == 1:
                            #assert next not in owners
                            print(f"while determining loop scope, updating afterloop[{node}] to {next}")
                            afterloop[node] = next
                            process(next)
                    continue

                print(f'             marking {node=} as part of scope of {header=}')
                inscope[node].append(header)
                for next in succs[node]:
                    process(next)

        return inscope

    def _classify_loop(src, header, n: int, ipostdoms, fg) -> str:
        print(f"loop candidate {header=} found at graph level {n=} with backedge from {src=}")

        hdrlen = len(fg.post(header))
        latchlen = len(fg.post(src))
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

    def _determine_loopfollow(src, hdr, ipostdoms, fg, inloop, looptype) -> Optional[str]:
        """The follow node is the one which executes on the way out of the loop.
            The follow may be printed within the sytactic block of the loop,
            or it may be the statement after the loop (targeted by a break).
            The loopfollow is not owned by the loop, even when printed within it."""
        if looptype == 'while':
            succs = list(fg.post(hdr))
            assert len(succs) == 2
            if succs[0] in inloop and inloop[succs[0]][0] == hdr:
                return succs[1]
            else:
                return succs[0]
        elif looptype == 'do-while':
            succs = list(fg.post(src))
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

    def analyze_loops(self, fg: tingly.RootedDiGraph):
        rfg = fg.inverse_with_phantom_exit_node()
        ipostdoms = tingly.RootedDiGraph.ipostdoms(rfg)

        loopdepths, loopcandidates = self._initial_loop_header_identification()
        backedge_levels = self._find_level_0_backedges(fg, loopdepths, loopcandidates)
        incircuit = self._determine_loop_circuit(fg, backedge_levels)
        
        loopsignatures = []
        for norig, (src, hdr) in backedge_levels:
            looptype = LoopAnalysis._classify_loop(src, hdr, norig, ipostdoms, fg)
            loopfollow = LoopAnalysis._determine_loopfollow(src, hdr, ipostdoms, fg, incircuit, looptype)
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

        # The afterloop node is a candidate for the sequential successor statement
        # for the loop, but if one loop contains another, and the inner loop is the
        # only way to reach an exit node, and there are no `break`s from the outer loop,
        # there need be no sequential successor for the outer loop. The afterloop node
        # should not be used, since it would be better placed within the inner loop.
        # This heuristic is not yet implemented.

        # More generally, there is often some leeway in the placement of blocks, especially
        # exit blocks accessible via inner loops. The exit sequence can occur purely within
        # the inner loop, or it may be placed after the outer loop.
        # (An example test case is cram-tests/codehawk-lifting/loops-gotos-c).
        # The afterloop node for a loop header does not always match the join point
        # of the header's conditional node.
        
        inscope = self._determine_loop_scope(fg, backedge_levels, afterloop, incircuit)
        backedges = set(edge for _, edge in backedge_levels)

        import pprint
        print(f"incircuit:")
        pprint.pprint(incircuit, indent=4)

        return (inscope, backedges, loopsignatures, loopfollows, afterloop, ipostdoms)

    def compute_gotoedges(rg: tingly.RootedDiGraph, twowayconds: Dict[str, str], inscope):
        gotoedges = set()
        # Some edges into multi-predecessor nodes must become gotos, or breaks.
        # We might need a goto for a backedge that crosses between loops.
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

            for p in sorted(preds): # inner
                edge = (p, tgt)
                if rg.edge_flavor(p, tgt) == 'tree':
                    print(f'tree {edge=} cannot be a goto')
                    continue
                if rg.edge_flavor(p, tgt) == 'back':
                    if loop_scope_for_node_is(p, tgt, inscope):
                        print(f"      skipping {edge=} because the pred is in the scope of the target")
                        continue # to inner
                    else:
                        print(f"  not skipping {edge=} because the pred is not in the scope of the target")
                if not exempted_one_pred:
                    exempted_one_pred = True
                    print(f"     exempting {edge=} from gotos because it was the first leading to the target")
                else:
                    print(f"     adding goto {edge=}")
                    gotoedges.add(edge)
        print(f"######## eventually got {gotoedges=}")
        return gotoedges

    def compute_breakedges(gotoedges: Set[Tuple[str, str]],
                           rg: tingly.RootedDiGraph,
                           loopheaders, afterloop, inscope, owners):
        breakedges = set()
        # For each loop header, the break target is the first *out of the loop*
        # postdominating node, if it is owned by the loop header. Loops can have
        # an afterloop node that can only be reached via gotos!
        # Given a break target, the break edges are those *from in the loop*
        # targeting it.
        for hdr in loopheaders:
            pdom = afterloop[hdr]
            print(f"::break target for {hdr=} is {pdom=} {inscope[pdom] if pdom in inscope else None}")
            for src in rg.edges:
                if pdom not in rg.edges[src]:
                    continue
                if rg.dominates(hdr, src) and not rg.dominates(pdom, src):
                    src_outside_hdr = src in inscope and inscope[src][0] != hdr
                    owned_elsewhere = pdom in owners and owners[pdom][0] != hdr
                    if (not owned_elsewhere) and not src_outside_hdr:
                        print(f"::::adding break edge owned by {hdr=} : {(src,pdom)=}")
                        breakedges.add( (src, pdom) )
                    else:
                        print(f"::::adding goto edge owned by {hdr=} : {(src,pdom)=} ;; {owned_elsewhere=} {src_outside_hdr=}")
                        gotoedges.add( (src, pdom) )
        return breakedges

    def scope_nesting_depth(rg: tingly.RootedDiGraph, all_backedges, gotoedges, afterloop, loopheaders, twowayconds):
        worklist = []
        worklist.append( (rg.start_node, 0) )

        depths = {node: len(rg.nodes) for node in rg.nodes}
        owners = {}
        seen = set()
        while len(worklist) > 0:
            (node, depth) = worklist.pop()
            if node in seen:
                continue

            seen.add(node)
            depths[node] = min(depth, depths[node])

            def process(succ, depth, followdict, tag):
                newdepth = depth
                roots = [hdr for hdr in followdict if followdict[hdr] == succ]
                for hdr in roots:
                    if depths[hdr] < newdepth:
                        newdepth = depths[hdr]
                        owners[succ] = (hdr, tag)
                #print(f"exploring break edge {succ=} via {node=} with newdepth {newdepth}")
                worklist.append((succ, newdepth))

            for succ in rg.post(node):
                if (node, succ) in all_backedges:
                    continue

                if (node, succ) in gotoedges:
                    continue

                if succ in afterloop.values():
                    process(succ, depth, afterloop, 'loop')
                    #process(succ, depth, afterloop, 'cond')
                    continue

                newdepth = depth
                if node in loopheaders:
                    newdepth += 1
                if node in twowayconds:
                    newdepth += 1

                if succ in twowayconds.values():
                    process(succ, newdepth, twowayconds, 'cond')
                    continue

                #print(f"exploring {succ=} via {node=} with depth {newdepth}")
                worklist.append((succ, newdepth))

        import pprint
        print("scope nesting depths:")
        pprint.pprint(depths, indent=4)

        print("owners:")
        pprint.pprint(owners, indent=4)
        return owners

class Cfg:

    def __init__(
            self,
            faddr: str,
            xnode: ET.Element) -> None:
        self._faddr = faddr
        self.xnode = xnode
        self._edges: Dict[str, List[str]] = {}
        self._graphseq: Optional[DerivedGraphSequence] = None
        self._flowgraph: Optional[tingly.RootedDiGraph] = None

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
    def flowgraph(self) -> tingly.RootedDiGraph:
        if self._flowgraph is None:
            self._flowgraph = tingly.RootedDiGraph(self.derived_graph_sequence.nodes,
                                    self.derived_graph_sequence.edges,
                                    self.derived_graph_sequence.graphs[0].nodes[0])
        return self._flowgraph

    @property
    def rpo_sorted_nodes(self) -> List[str]:
        """Return a list of block addresses in reverse postorder."""

        return self.flowgraph.rpo_sorted

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

        la = LoopAnalysis(self.derived_graph_sequence)
        inscope, all_backedges, loopsignatures, loopfollows, afterloop, ipostdoms = la.analyze_loops(self.flowgraph)
        
        idoms = self.flowgraph.idoms


        import pprint
        print(f"inscope:")
        pprint.pprint(inscope, indent=4)

        print(f"loopsignatures:")
        pprint.pprint(loopsignatures, indent=4)


        print("idoms:")
        pprint.pprint(idoms, indent=4)

        print("ipostdoms:")
        pprint.pprint(ipostdoms, indent=4)

        pprint.pprint(self.flowgraph._edge_flavors, indent=4)

        print(f'loopfollows:')
        pprint.pprint(loopfollows, indent=4)
        print(f'afterloop:')
        pprint.pprint(afterloop, indent=4)

        loopheaders = set(sig[0] for sig in loopsignatures)
        latchingnodes = set(src for src, tgt in all_backedges)
        print(f'{loopheaders=} ; {latchingnodes=} (ndet ok)')
        twowayconds = self.flowgraph.two_way_conditionals(latchingnodes)

        print(f'twowayconds:')
        pprint.pprint(twowayconds, indent=4)

        gotoedges = LoopAnalysis.compute_gotoedges(self.flowgraph, twowayconds, inscope)
        non_goto_backedges = all_backedges - gotoedges

        # Pre-generate a conservative approximation of the labels that might be used;
        # when a goto is emitted, make sure the label it targets actually gets printed.
        labeled_stmts = { tgt: astree.mk_label_stmt(tgt) for tgt in self.flowgraph.rpo_sorted }

        owners = LoopAnalysis.scope_nesting_depth(self.flowgraph, all_backedges, gotoedges, afterloop, loopheaders, twowayconds)
        
        # mutates gotoedges
        breakedges = LoopAnalysis.compute_breakedges(gotoedges, self.flowgraph, loopheaders, afterloop, inscope, owners)

        def emit(n: str) -> List[AST.ASTStmt]:
            """Produces the AST for a block, preceded by a label (which may not get printed)."""
            if n not in blockstmts:
                return [labeled_stmts[n]]

            return [labeled_stmts[n], blockstmts[n]]

        constructed_stmts = set()
        def construct(
                n: str,
                follow: Optional[str],
                loopheader: Optional[str],
                result: List[AST.ASTStmt]) -> AST.ASTStmt:
            # When processing the two arms of a conditional branch,
            # `follow` indicates the join point, i.e. where the arms end.

            def possible_loop_latch_branch(succ, newfollownode) -> AST.ASTStmt:
                if (n, succ) in non_goto_backedges:
                    # don't infinitely recurse!
                    return astree.mk_block([])

                if (n, succ) in breakedges:
                        print(f"emitting break in loop at edge {n=}->{succ=}  {loopheader=}")
                        print(f"    {inscope[n] if n in inscope else None=}")
                        print(f"    {inscope[succ] if succ in inscope else None=}")
                        return astree.mk_break_stmt()

                if (n, succ) in gotoedges:
                    print(f"emitting goto in loop at edge {n=} {succ=} {loopheader=}")
                    labeled_stmts[succ]._printed = True
                    return astree.mk_goto_stmt(succ)

                return construct(succ, newfollownode, loopheader, [])

            print(f"construct({n=}, {follow=}, {loopheader=})")

            if follow and n == follow:
                print(f"stopping at {follow=} and returning what's been collected so far")
                return astree.mk_block(result)

            if n in constructed_stmts:
                print(f"###########################  already constructed {n=}; emitting an unexpected goto")
                labeled_stmts[n]._printed = True
                return astree.mk_block(result + [astree.mk_goto_stmt(n)])
            else:
                constructed_stmts.add(n)

            if len(self.successors(n)) == 0:
                return astree.mk_block(result + emit(n))

            if loop_scope_for_node_is(n, n, inscope) and loopheader != n:
                # When we encounter a loop header for the first time, we recur with
                # a new `loopheader` flag so that we don't infinitely recurse.
                follownode = afterloop[n]
                print(f"LOOP LOOP LOOP LOOP LOOP encountered loop header node {n=}, {len(result)=}")
                print(f'                {follownode=} ; {loopheader=} ; {follow=} ; {owners=}')
                constructed_stmts.remove(n)
                body = construct(n, follow, n, [])
                loop = astree.mk_loop(body)
                follownode_owned_by_loop_if_any = follownode not in owners or (n, 'loop') == owners[follownode]
                if follownode and follownode_owned_by_loop_if_any:
                    # A testcase which requires the follownode_owned_by_loop check is
                    #       cram-tests/codehawk-lifting/loops-gotos-b
                    return construct(
                        follownode, follow, loopheader, result + [loop])

                # No more nodes to slurp up; return what we have so far, plus our loop
                if result == []:
                    return loop
                return astree.mk_block(result + [loop])

            if len(self.successors(n)) == 1:
                next = self.successors(n)[0]
                if (n, next) in non_goto_backedges:
                    if loopheader == next:
                        print(f"ending construct early at {n=} {next=} due to backedge...")
                    else:
                        print(f"ending construct early (different loopheader) at {n=} {next=} due to backedge...")
                    return astree.mk_block(result + emit(n) + [astree.mk_continue_stmt()])
                    #return astree.mk_block(result + emit(n))

                if (n, next) in breakedges:
                        print(f"emitting break at edge {n=}->{next=}  {loopheader=}")
                        print(f"    {inscope[n] if n in inscope else None=}")
                        print(f"    {inscope[next] if next in inscope else None=}")
                        return astree.mk_block(result + emit(n) + [astree.mk_break_stmt()])

                if (n, next) in gotoedges:
                    print(f"ending construct early at {n=} due to goto {next=}...")
                    labeled_stmts[next]._printed = True
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

                # If the afterloop node is the same as the join point for the loop header,
                # the afterloop node should be processed by the code that emits the loop construct,
                # so we should only process follownodes that aren't also afterloop nodes.
                # We should also skip emitting follow nodes that we don't own.
                if (not follownode \
                        or (n == loopheader and afterloop[loopheader] == follownode) \
                        or (follownode in owners and owners[follownode] != (n, 'cond'))):
                    print(f',,,,,, skipping continuation of 2-succ node {n=} {loopheader=} {follownode=} {follow=}')
                    return astree.mk_block(result + emit(n) + [bstmt])

                print(f',,,,,, constructing continuation of 2-succ node {n=} {loopheader=} {follownode=} {follow=}')
                return construct(
                    follownode, follow, loopheader, result + emit(n) + [bstmt])
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
