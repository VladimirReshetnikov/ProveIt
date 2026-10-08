"""Small independent reduced F2 Khovanov cube for closed braid validation.

This is an EXPONENTIAL reference implementation, not a production scanner.
Positive crossing: 0=vertical, 1=cap/cup; negative crossing swaps these.
The circle through the first closure strand is labelled x. The reduced
quantum shift is +1, so the crossingless unknot lies in bidegree (0,0).
"""
from __future__ import annotations
from dataclasses import dataclass
from collections import defaultdict
from .core import DAG, binary_basis, dense_transfer, factor_at_cut, minimum_vertex_cut, F2
from .budgets import sharp_rank_budget

@dataclass(frozen=True)
class ChainComplex:
    degrees: tuple[int, ...]
    quantum: tuple[int, ...]
    edges: tuple[tuple[int,int], ...]

    def validate(self) -> bool:
        n = len(self.degrees)
        if len(self.quantum) != n or len(self.edges) != len(set(self.edges)): return False
        out = [set() for _ in range(n)]
        for u,v in self.edges:
            if not (0 <= u < n and 0 <= v < n): return False
            if self.degrees[v] != self.degrees[u]+1 or self.quantum[v] != self.quantum[u]: return False
            out[u].add(v)
        for u in range(n):
            twice = set()
            for v in out[u]: twice.symmetric_difference_update(out[v])
            if twice: return False
        return True

    def homology(self) -> dict[tuple[int,int], int]:
        groups = defaultdict(list)
        for v, key in enumerate(zip(self.degrees,self.quantum)): groups[key].append(v)
        edge_out = defaultdict(list)
        for u,v in self.edges: edge_out[u].append(v)
        ranks = {}
        for key, sources in groups.items():
            h,j = key; targets = groups.get((h+1,j),[]); where = {v:i for i,v in enumerate(targets)}
            columns = [sum(1 << where[v] for v in edge_out[u]) for u in sources]
            ranks[key] = len(binary_basis(columns))
        return {key: value for key,vertices in groups.items()
                if (value := len(vertices)-ranks.get(key,0)-ranks.get((key[0]-1,key[1]),0))}


def closure_components(strands: int, word: list[int] | tuple[int,...]) -> int:
    if type(strands) is not int or strands < 1: raise ValueError("positive braid index required")
    permutation = list(range(strands))
    for x in word:
        if type(x) is not int or not 1 <= abs(x) < strands: raise ValueError("invalid braid generator")
        i = abs(x)-1; permutation[i],permutation[i+1] = permutation[i+1],permutation[i]
    seen = set(); count = 0
    for i in range(strands):
        if i not in seen:
            count += 1; u = i
            while u not in seen: seen.add(u); u = permutation[u]
    return count


def _resolution(strands, word, state):
    n = len(word); size = (n+1)*strands; parent = list(range(size))
    def find(a):
        while parent[a] != a:
            parent[a] = parent[parent[a]]; a = parent[a]
        return a
    def join(a,b):
        a,b = find(a),find(b)
        if a != b: parent[b] = a
    for t,x in enumerate(word):
        i = abs(x)-1
        horizontal = bool((state >> t) & 1) ^ (x < 0)
        for j in range(strands):
            if j not in (i,i+1): join(t*strands+j,(t+1)*strands+j)
        if horizontal:
            join(t*strands+i,t*strands+i+1)
            join((t+1)*strands+i,(t+1)*strands+i+1)
        else:
            join(t*strands+i,(t+1)*strands+i)
            join(t*strands+i+1,(t+1)*strands+i+1)
    for j in range(strands): join(j,n*strands+j)
    groups = defaultdict(set)
    for v in range(size): groups[find(v)].add(v)
    circles = tuple(sorted((frozenset(x) for x in groups.values()), key=lambda x:min(x)))
    mark = next(i for i,c in enumerate(circles) if 0 in c)
    return circles, mark


def reduced_cube(strands: int, word: list[int] | tuple[int,...], max_crossings: int = 11) -> ChainComplex:
    closure_components(strands,word)
    n = len(word)
    if n > max_crossings: raise ValueError("reference cube crossing limit exceeded")
    negative = sum(x < 0 for x in word); positive = n-negative
    resolutions = [_resolution(strands,word,s) for s in range(1 << n)]
    ids = {}; degrees = []; quantum = []
    state_labels = []
    for s,(circles,mark) in enumerate(resolutions):
        other = [i for i in range(len(circles)) if i != mark]
        labels = []
        for bits in range(1 << len(other)):
            label = 1 << mark
            for j,i in enumerate(other): label |= ((bits >> j)&1) << i
            ids[s,label] = len(degrees); labels.append(label)
            degrees.append(s.bit_count()-negative)
            quantum.append(s.bit_count()+positive-2*negative+len(circles)-2*label.bit_count()+1)
        state_labels.append(labels)
    edges = set()
    for s,(old,mark) in enumerate(resolutions):
        old_map = {c:i for i,c in enumerate(old)}
        for crossing in range(n):
            if (s >> crossing)&1: continue
            t = s | (1 << crossing); new,newmark = resolutions[t]
            new_map = {c:i for i,c in enumerate(new)}
            unchanged = [(old_map[c],new_map[c]) for c in old_map.keys() & new_map.keys()]
            lost = [i for i,c in enumerate(old) if c not in new_map]
            gained = [i for i,c in enumerate(new) if c not in old_map]
            if (len(lost),len(gained)) not in ((2,1),(1,2)):
                raise ArithmeticError("resolution edge is not a merge/split saddle")
            for label in state_labels[s]:
                base = sum(((label >> a)&1) << b for a,b in unchanged)
                outputs = []
                if len(lost) == 2:
                    x,y = ((label >> a)&1 for a in lost)
                    if not (x and y): outputs = [base | ((x|y) << gained[0])]
                elif (label >> lost[0])&1:
                    outputs = [base | (1 << gained[0]) | (1 << gained[1])]
                else:
                    outputs = [base | (1 << gained[0]),base | (1 << gained[1])]
                for result in outputs:
                    if not (result >> newmark)&1:
                        raise ArithmeticError("marked subcomplex not preserved")
                    edge = (ids[s,label],ids[t,result])
                    if edge in edges: edges.remove(edge)
                    else: edges.add(edge)
    result = ChainComplex(tuple(degrees),tuple(quantum),tuple(sorted(edges)))
    if not result.validate(): raise ArithmeticError("cube grading or d^2 check failed")
    return result


def acyclic_matching(complex_: ChainComplex, edge_limit: int | None = None):
    """Greedy partial Morse matching, with an exact cycle test per reversal.

    The procedure is deliberately simple, bounded, and deterministic. It need
    not find a maximum/minimum-critical matching, and may be expensive.
    """
    if not complex_.validate(): raise ValueError("not a valid F2 chain complex")
    n = len(complex_.degrees); adj = [set() for _ in range(n)]
    for u,v in complex_.edges: adj[u].add(v)
    matched = set(); pairs = []
    candidates = sorted(complex_.edges, key=lambda e:(len(adj[e[0]]),e))
    for index,(u,v) in enumerate(candidates):
        if edge_limit is not None and index >= edge_limit: break
        if u in matched or v in matched: continue
        adj[u].remove(v)
        seen = {u}; todo = [u]
        while todo and v not in seen:
            for w in adj[todo.pop()]:
                if w not in seen: seen.add(w); todo.append(w)
        if v in seen:
            adj[u].add(v)
        else:
            adj[v].add(u); matched.update((u,v)); pairs.append((u,v))
    return tuple(pairs)


def verify_matching(complex_: ChainComplex, pairs) -> bool:
    try:
        edge_set = set(complex_.edges); used = set(); reversed_edges = []
        for u,v in pairs:
            if (u,v) not in edge_set or u in used or v in used: return False
            used.update((u,v))
        pair_set = set(map(tuple,pairs))
        for u,v in complex_.edges:
            reversed_edges.append((v,u,1) if (u,v) in pair_set else (u,v,1))
        DAG(len(complex_.degrees),tuple(reversed_edges),(),())
        return complex_.validate()
    except (ValueError,TypeError,IndexError): return False


def morse_graphs(complex_: ChainComplex, pairs):
    """Return critical dimensions and one transfer DAG per (h,j).

    Vertex IDs are local to a graph. All input generators (including irrelevant
    ones in the two degrees) are retained; no zero coefficient is guessed.
    """
    if not verify_matching(complex_,pairs): raise ValueError("invalid/cyclic Morse matching")
    used = {v for pair in pairs for v in pair}; matched = set(map(tuple,pairs))
    groups = defaultdict(list); critical = defaultdict(list)
    for v,key in enumerate(zip(complex_.degrees,complex_.quantum)):
        groups[key].append(v)
        if v not in used: critical[key].append(v)
    graphs = {}
    edges_by_key = defaultdict(list)
    for u,v in complex_.edges:
        edges_by_key[complex_.degrees[u],complex_.quantum[u]].append((u,v))
    for key,sources in critical.items():
        h,j = key; targets = critical.get((h+1,j),[])
        if not sources or not targets: continue
        vertices = groups[key]+groups[h+1,j]; where = {v:i for i,v in enumerate(vertices)}
        edges = []
        for u,v in edges_by_key[key]:
            edges.append((where[v],where[u],1) if (u,v) in matched else (where[u],where[v],1))
        # Critical sources have no reversed incoming edge; critical targets no
        # reversed outgoing edge, as required by DAG's terminal convention.
        graphs[key] = DAG(len(vertices),tuple(sorted(edges)),tuple(where[v] for v in sources),
                          tuple(where[v] for v in targets))
    return {key:len(value) for key,value in critical.items()}, graphs


def analyze_complex(complex_: ChainComplex, pairs=None, compare_dense=True):
    if pairs is None: pairs = acyclic_matching(complex_)
    counts,graphs = morse_graphs(complex_,pairs)
    ranks = {}; capacities = {}; details = []
    for key,graph in sorted(graphs.items()):
        cut = minimum_vertex_cut(graph)
        factors = factor_at_cut(graph,cut.cut,F2())
        rank = factors.binary_rank()
        if compare_dense:
            dense,work = dense_transfer(graph,F2())
            if factors.expand(F2()) != dense: raise ArithmeticError("first-hit transfer mismatch")
            dense_rank = len(binary_basis([sum(row[j] << i for i,row in enumerate(dense))
                                            for j in range(len(graph.sources))]))
            if rank != dense_rank: raise ArithmeticError("factor rank mismatch")
        else: work = None
        ranks[key] = rank; capacities[key] = cut.capacity
        details.append(dict(h=key[0],j=key[1],vertices=graph.n,edges=len(graph.edges),
            sources=len(graph.sources),targets=len(graph.targets),cut_capacity=cut.capacity,
            cut_vertices=len(cut.cut),rank=rank,forward_compositions=None if work is None else work.compositions,
            factor_compositions=factors.work.compositions))
    homology = {}; lower = {}
    for key,c in counts.items():
        prev = (key[0]-1,key[1])
        b = c-ranks.get(key,0)-ranks.get(prev,0)
        if b < 0: raise ArithmeticError("negative Morse Betti number")
        if b: homology[key] = b
        lo = max(0,c-capacities.get(key,0)-capacities.get(prev,0))
        if lo: lower[key] = lo
    S = sum(counts.values()); K = sum(capacities.values())
    budget = sharp_rank_budget(counts, capacities)
    return dict(generators=len(complex_.degrees),edges=len(complex_.edges),pairs=len(pairs),
        critical=S,capacity_sum=K,sharp_lower=budget['homology_lower'],global_lower=max(0,S-2*K),graded_lower=sum(lower.values()),
        exact_rank=sum(homology.values()),homology=homology,details=details)
