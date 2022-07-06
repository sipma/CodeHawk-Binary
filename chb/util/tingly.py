# tingly, the TINy Graph LibrarY

from typing import Dict, List, Mapping, Optional, Sequence, Set, Tuple

UserNodeID = str # or int, whatever

class RootedDiGraph:

    def __init__(self, nodes: Sequence[UserNodeID], edges: Mapping[UserNodeID, Sequence[UserNodeID]], start_node: UserNodeID):
        self.nodes = nodes
        self.edges = edges
        self.start_node = start_node
        self._rpo: Dict[UserNodeID, int] = {}
        self._rpo_sorted: List[UserNodeID] = []
        self._edge_flavors: Dict[Tuple[UserNodeID, UserNodeID], str] = {}
        self._revedges: Dict[str, List[str]] = {}
        self._twowayconditionals: Dict[str, str] = {} # follow nodes
        self._idoms: Dict[UserNodeID, Optional[UserNodeID]] = {n:None for n in nodes} # immediate dominator

        self._compute_dfs() # First DFS computes the reverse postorder list.
        self._compute_dfs() # DFS in RPO order can produce fewer cross edges.
        self._compute_doms()

    def _compute_dfs(self) -> None:
        """Initializes the reverse postorder list."""
        visited = set()
        starttime = {v:0 for v in self.nodes}
        endtime = {v:0 for v in self.nodes}
        vtime = 0

        prev_rpo = self._rpo_sorted
        self._rpo_sorted = []
        self._rpo = {}

        def visit(node: str) -> None:
            nonlocal vtime
            visited.add(node)
            starttime[node] = vtime
            vtime += 1

            # Set iteration order is nondeterministic, so we must sort to ensure determinism.
            successors = sorted(self.post(node))
            if len(prev_rpo) > 0:
                succ_idxs = sorted(prev_rpo.index(x) for x in successors)
                successors = [prev_rpo[i] for i in succ_idxs]

            # Doing DFS a second time, visiting the successors in reverse postorder,
            # helps to avoid unnecessary cross edges.
            for t in successors:
                if t not in visited:
                    self._edge_flavors[(node, t)] = "tree"
                    visit(t)
                else:
                    if endtime[t] == 0: # starttime[t] < starttime[node] and endtime[t] > endtime[node]:
                        self._edge_flavors[(node, t)] = "back"
                    elif starttime[t] > starttime[node]: # and endtime[t] < endtime[node]:
                        self._edge_flavors[(node, t)] = "forward"
                    else: # starttime[t] < starttime[node] and endtime[t] < endtime[node]:
                        self._edge_flavors[(node, t)] = "cross"
            
            endtime[node] = vtime
            vtime += 1

            self._rpo_sorted.append(node)

        visit(self.start_node)
        self._rpo_sorted.reverse()

    def edge_flavor(self, src: UserNodeID, tgt: UserNodeID) -> str:
        """
        Returns the flavor of the edge ('back', 'forward', 'cross', 'tree') from src to tgt.
        """
        return self._edge_flavors[(src, tgt)]

    @property
    def revedges(self) -> Dict[str, List[str]]:
        if len(self._revedges) == 0:
            for src in self.edges:
                for tgt in self.edges[src]:
                    self._revedges.setdefault(tgt, [])
                    self._revedges[tgt].append(src)
        return self._revedges

    @property
    def rpo_sorted(self) -> List[UserNodeID]:
        """
        Returns a list of the graph's nodes in a reverse postorder.
        """
        return self._rpo_sorted

    @property
    def rpo(self) -> Dict[UserNodeID, int]:
        """
        Returns a mapping from address to index in the reverse postorder.
        """
        if len(self._rpo) == 0:
            self._rpo = {k:i+1 for i, k in enumerate(self.rpo_sorted)}
        return self._rpo

    def post(self, n) -> Set[str]:
        if n in self.edges:
            return set(self.edges[n])
        else:
            return set([])

    def pre(self, n) -> Set[str]:
        if n in self.revedges:
            return set(self.revedges[n])
        else:
            return set([])

    def inverse_with_phantom_exit_node(self) -> 'RootedDiGraph':
        """
        Returns the inverse of the graph, .
        """
        phantomend = '__' + str(len(self.nodes))
        augedges = self.revedges.copy()
        terminators = [node for node in self.nodes if len(self.post(node)) == 0]
        augedges[phantomend] = terminators
        return RootedDiGraph(self.nodes + [phantomend], augedges, phantomend)

    def ipostdoms(rrg: 'RootedDiGraph') -> Dict[UserNodeID, Set[UserNodeID]]:
        idoms = dict(rrg.idoms)
        # The start node of the reverse graph is a phantom node that doesn't
        # exist in the original graph.
        del idoms[rrg.start_node]
        return idoms
            
    def _compute_doms(self) -> None:
        """
        Computes the dominators of each node.

        Implements the algorithm in:
            "A Simple, Fast Dominance Algorithm"
            Keith D. Cooper, Timothy J. Harvey, and Ken Kennedy
            https://www.cs.rice.edu/~keith/EMBED/dom.pdf
        """

        def intersect(b1: UserNodeID, b2: UserNodeID) -> UserNodeID:
            finger1 = b1
            finger2 = b2
            while finger1 != finger2:
                # The paper describes comparisons on postorder numbers; we're using
                # the reverse postorder numbers, so we need to flip the comparison.
                while self.rpo[finger1] > self.rpo[finger2]:
                    finger1 = self._idoms[finger1]
                while self.rpo[finger2] > self.rpo[finger1]:
                    finger2 = self._idoms[finger2]
            return finger1

        # Initialize the dominators of the start node to be the start node itself.
        self._idoms[self.start_node] = self.start_node
        changed = True
        while changed:
            changed = False
            for node in self.rpo_sorted:
                if node == self.start_node:
                    continue
                allpreds = list(self.pre(node))
                new_idom = None
                for pred in allpreds:
                    if self._idoms[pred] is not None:
                        new_idom = pred
                        allpreds.remove(pred) # now it's almost-allpreds...
                        break
                assert new_idom is not None
                for pred in allpreds:
                    if self._idoms[pred] is not None:
                        new_idom = intersect(pred, new_idom)
                if self._idoms[node] != new_idom:
                    self._idoms[node] = new_idom
                    changed = True

    def idom(self, node: UserNodeID) -> Optional[UserNodeID]:
        """
        Returns the immediate dominator of the given node.
        """
        return self._idoms[node]

    @property
    def idoms(self) -> Dict[UserNodeID, UserNodeID]:
        """
        Returns a mapping from node to its immediate dominator.
        """
        return self._idoms.copy()

    # Linearly bounded by the depth of the dominator tree
    def dominates(self, node_a: UserNodeID, node_b: UserNodeID) -> bool:
        """
        Returns True if node_a dominates node_b.
        """
        # Self-domination is implicit.
        if node_a == node_b:
            return True

        finger = node_b
        while finger != self.start_node:
            if finger == node_a:
                return True
            finger = self._idoms[finger]
        return False

    def two_way_conditionals(self, loopheaders: Set[str], latchingnodes: Set[str]) -> Dict[str, str]:
        """Identify 2-way conditionals and their follow nodes.

        Based on algorithm in:
            Cristina Cifuentes, Structuring Decompiled Graphs, Compiler Construction,
            CC'96, LNCS 1060, pg 91-105, Springer, 1996.
            https://link.springer.com/content/pdf/10.1007/3-540-61053-7_55.pdf
        """

        def find_follow(m: str) -> Optional[str]:
            followcandidates: List[str] = [
                i for i in self.nodes
                if self.idom(i) == m and len(self.pre(i)) >= 2]
            if len(followcandidates) > 0:
                return max(followcandidates, key=lambda k: self.rpo[k])
            else:
                return None

        def is_descendant(child: str, parent: str) -> bool:
            # Consider a graph arising from 
            #     while (x() && y()) { d() } return;
            # which looks like:
            #     H -> A -> B -> C -> D -> H...
            #      \->--------->/  \> E
            # The algorithm below processes C first, leaving it
            # unresolved. Then it processes H, which identifies
            # C as the follow node. The unresolved check then calls
            # is_descendant(C, C) which must return False, or else
            # node C will be considered to be its own follow node!
            if child == parent:
                return False
            worklist = [child]
            seen = set()
            while worklist:
                node = worklist.pop()
                if node == parent:
                    return True
                if node in seen:
                    continue
                seen.add(node)
                for pred in self.pre(node):
                    # Don't consider backedges!
                    if self.edge_flavor(pred, node) == 'back':
                        continue
                    worklist.append(pred)   
            return False

        unresolved: Set[str] = set([])

        if len(self._twowayconditionals) == 0:
            for m in reversed(self._rpo_sorted):
                # Cifuentes skips nodes marked as loop headers, since she integrates
                # the conditional directly into the loop construct, but we keep them
                # separate, and so do not skip loop headers.
                if (    len(self.post(m)) == 2   # 2-way conditional
                        and not m in latchingnodes):  # not a latching node
                    follow = find_follow(m)
                    print(f"   _twowayconditionals:     {m=} {follow=}")
                    if follow is not None:
                        self._twowayconditionals[m] = follow
                        toberemoved: List[str] = []
                        for k in sorted(unresolved):
                            if is_descendant(follow, k):
                                print(f"   _twowayconditionals updating {k=} as descendent to have {follow=} from {m=}")
                                self._twowayconditionals[k] = follow
                                toberemoved.append(k)
                        for k in toberemoved:
                            unresolved.remove(k)
                    else:
                        unresolved.add(m)

        if len(unresolved) > 0:
            print("Unresolved two-way conditional: " + ", ".join(unresolved))
        return self._twowayconditionals