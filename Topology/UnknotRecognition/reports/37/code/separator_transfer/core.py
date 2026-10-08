"""Exact first-hit factorization of typed, finite, acyclic path sums.

No ring division, commutativity, generic-rank assumption, or randomized identity
checks are used. Input coefficient encodings are integers; addition is XOR.
The category/ring adapter is responsible for validating its encoding and types.
"""
from __future__ import annotations
from dataclasses import dataclass
from collections import deque
from heapq import heappush, heappop
from typing import Protocol, Sequence

class Operations(Protocol):
    def one(self, v: int) -> int: ...
    def mul(self, u: int, v: int, w: int, after: int, before: int) -> int: ...

class F2:
    def one(self, v: int) -> int:
        return 1
    def mul(self, u: int, v: int, w: int, after: int, before: int) -> int:
        if after not in (0, 1) or before not in (0, 1):
            raise ValueError("not an F2 coefficient")
        return after & before

class DotAlgebra:
    """F2[x_0,...,x_(k-1)]/(x_i^2). Bit m is monomial with support m."""
    def __init__(self, k: int):
        if not isinstance(k, int) or k < 0:
            raise ValueError("k must be nonnegative")
        self.k = k
    def one(self, v: int) -> int:
        return 1
    def mul(self, u: int, v: int, w: int, after: int, before: int) -> int:
        if min(after, before) < 0 or max(after, before).bit_length() > (1 << self.k):
            raise ValueError("invalid dot-polynomial encoding")
        out = 0
        a = after
        while a:
            bit = a & -a; i = bit.bit_length() - 1; a ^= bit
            b = before
            while b:
                bit = b & -b; j = bit.bit_length() - 1; b ^= bit
                if not (i & j):
                    out ^= 1 << (i | j)
        return out

class MatrixCategory:
    """Typed rectangular F2 matrices, packed row-major; no commutativity."""
    def __init__(self, dims: Sequence[int]):
        self.dims = tuple(dims)
        if any(type(d) is not int or d < 0 for d in self.dims):
            raise ValueError("dimensions must be nonnegative integers")
    def one(self, v: int) -> int:
        d = self.dims[v]
        return sum(1 << (i*d+i) for i in range(d))
    def mul(self, u: int, v: int, w: int, after: int, before: int) -> int:
        a, b, c = self.dims[u], self.dims[v], self.dims[w]
        if min(after, before) < 0 or after.bit_length() > b*c or before.bit_length() > a*b:
            raise ValueError("matrix dimensions do not match its packed encoding")
        out = 0; mask_a = (1 << a)-1; mask_b = (1 << b)-1
        for i in range(c):
            support = (after >> (i*b)) & mask_b
            row = 0
            while support:
                bit = support & -support; j = bit.bit_length()-1; support ^= bit
                row ^= (before >> (j*a)) & mask_a
            out |= row << (i*a)
        return out

@dataclass(frozen=True)
class DAG:
    n: int
    edges: tuple[tuple[int, int, int], ...]
    sources: tuple[int, ...]
    targets: tuple[int, ...]

    def __post_init__(self):
        if type(self.n) is not int or self.n < 0:
            raise ValueError("invalid vertex count")
        for seq in (self.sources, self.targets):
            if len(seq) != len(set(seq)) or any(type(v) is not int or not 0 <= v < self.n for v in seq):
                raise ValueError("invalid terminal list")
        if set(self.sources) & set(self.targets):
            raise ValueError("sources and targets must be disjoint")
        seen = set()
        for u, v, f in self.edges:
            if not (type(u) is int and type(v) is int and 0 <= u < self.n and 0 <= v < self.n):
                raise ValueError("invalid edge endpoint")
            if type(f) is not int or f <= 0 or (u, v) in seen:
                raise ValueError("edges must have nonzero integer labels and be unique")
            seen.add((u, v))
            if v in self.sources or u in self.targets:
                raise ValueError("sources must have indegree zero; targets outdegree zero")
        self.order()  # Reject directed cycles before any algebra is evaluated.

    def adjacency(self):
        out = [[] for _ in range(self.n)]; inc = [[] for _ in range(self.n)]
        for u, v, f in self.edges:
            out[u].append((v, f)); inc[v].append((u, f))
        return out, inc

    def order(self) -> tuple[int, ...]:
        out = [[] for _ in range(self.n)]; deg = [0]*self.n
        for u, v, _ in self.edges:
            out[u].append(v); deg[v] += 1
        heap = []
        for v in range(self.n):
            if not deg[v]: heappush(heap, v)
        order = []
        while heap:
            u = heappop(heap); order.append(u)
            for v in out[u]:
                deg[v] -= 1
                if not deg[v]: heappush(heap, v)
        if len(order) != self.n:
            raise ValueError("the transfer graph contains a directed cycle")
        return tuple(order)

    def separates(self, cut: Sequence[int]) -> bool:
        forbidden = set(cut)
        if len(forbidden) != len(cut) or any(type(v) is not int or not 0 <= v < self.n for v in forbidden):
            return False
        out, _ = self.adjacency()
        seen = set(self.sources) - forbidden; todo = list(seen)
        while todo:
            for v, _ in out[todo.pop()]:
                if v not in forbidden and v not in seen:
                    seen.add(v); todo.append(v)
        return not (seen & set(self.targets))

@dataclass
class Work:
    compositions: int = 0
    vertex_visits: int = 0


def dense_transfer(graph: DAG, ops: Operations, reverse: bool = False):
    """Independent endpoint-propagation reference; returns target-by-source rows."""
    order = graph.order(); out, inc = graph.adjacency(); work = Work()
    rows = [[0]*len(graph.sources) for _ in graph.targets]
    roots = graph.targets if reverse else graph.sources
    for index, root in enumerate(roots):
        values = [0]*graph.n; values[root] = ops.one(root)
        for u in (reversed(order) if reverse else order):
            work.vertex_visits += 1
            if not values[u]: continue
            for v, f in (inc[u] if reverse else out[u]):
                if reverse:
                    term = ops.mul(v, u, root, values[u], f)
                else:
                    term = ops.mul(root, u, v, f, values[u])
                values[v] ^= term; work.compositions += 1
        if reverse:
            rows[index] = [values[s] for s in graph.sources]
        else:
            for j, t in enumerate(graph.targets): rows[j][index] = values[t]
    return rows, work

@dataclass
class Factors:
    sources: tuple[int, ...]
    targets: tuple[int, ...]
    cut: tuple[int, ...]
    A: list[list[int]]  # cut x sources: first-hit prefixes
    B: list[list[int]]  # targets x cut: unrestricted suffixes
    work: Work

    def entry(self, target_index: int, source_index: int, ops: Operations) -> int:
        s = self.sources[source_index]; t = self.targets[target_index]; result = 0
        for j, c in enumerate(self.cut):
            a, b = self.A[j][source_index], self.B[target_index][j]
            if a and b: result ^= ops.mul(s, c, t, b, a)
        return result

    def expand(self, ops: Operations):
        return [[self.entry(i,j,ops) for j in range(len(self.sources))]
                for i in range(len(self.targets))]

    def binary_rank(self, dims: Sequence[int] | None = None) -> int:
        """Rank(BA), never form BA. dims=None means scalar F2 coefficients.

        With dims supplied, A and B entries are packed rectangular F2 matrices.
        There is intentionally no ring-valued 'rank' method.
        """
        if dims is None:
            n = max(self.sources+self.targets+self.cut, default=-1)+1
            dims = [1]*n
        a_offsets = []; b_offsets = []; c_offsets = []
        a_total = b_total = c_total = 0
        for v in self.sources: a_offsets.append(a_total); a_total += dims[v]
        for v in self.targets: b_offsets.append(b_total); b_total += dims[v]
        for v in self.cut: c_offsets.append(c_total); c_total += dims[v]
        Acols = [0]*a_total; Bcols = [0]*c_total
        for ci, c in enumerate(self.cut):
            dc = dims[c]
            for si, s in enumerate(self.sources):
                ds = dims[s]; block = self.A[ci][si]
                if block < 0 or block.bit_length() > ds*dc:
                    raise ValueError("invalid A block")
                for row in range(dc):
                    bits = (block >> (row*ds)) & ((1 << ds)-1)
                    while bits:
                        bit = bits & -bits; col = bit.bit_length()-1; bits ^= bit
                        Acols[a_offsets[si]+col] |= 1 << (c_offsets[ci]+row)
            for ti, t in enumerate(self.targets):
                dt = dims[t]; block = self.B[ti][ci]
                if block < 0 or block.bit_length() > dc*dt:
                    raise ValueError("invalid B block")
                for row in range(dt):
                    bits = (block >> (row*dc)) & ((1 << dc)-1)
                    while bits:
                        bit = bits & -bits; col = bit.bit_length()-1; bits ^= bit
                        Bcols[c_offsets[ci]+col] |= 1 << (b_offsets[ti]+row)
        images = []
        for vector in binary_basis(Acols):
            image = 0
            while vector:
                bit = vector & -vector; vector ^= bit
                image ^= Bcols[bit.bit_length()-1]
            images.append(image)
        return len(binary_basis(images))


def binary_basis(columns: Sequence[int]) -> list[int]:
    pivots = {}
    for value in columns:
        if type(value) is not int or value < 0:
            raise ValueError("binary columns must be nonnegative integers")
        while value:
            p = value.bit_length()-1
            if p not in pivots:
                pivots[p] = value; break
            value ^= pivots[p]
    return [pivots[p] for p in sorted(pivots)]


def factor_at_cut(graph: DAG, cut: Sequence[int], ops: Operations) -> Factors:
    if not graph.separates(cut):
        raise ValueError("the supplied vertices do not separate all source-target paths")
    order = graph.order(); pos = {v:i for i,v in enumerate(order)}
    cut = tuple(sorted(cut, key=pos.__getitem__)); forbidden = set(cut)
    out, inc = graph.adjacency(); A = []; B = [[0]*len(cut) for _ in graph.targets]
    work = Work()
    for ci, c in enumerate(cut):
        # Prefixes are FIRST-HIT paths. Other cut vertices are not traversed.
        values = [0]*graph.n; values[c] = ops.one(c)
        for u in reversed(order):
            work.vertex_visits += 1
            if not values[u] or (u in forbidden and u != c): continue
            for v, f in inc[u]:
                values[v] ^= ops.mul(v, u, c, values[u], f)
                work.compositions += 1
        A.append([values[s] if s not in forbidden or s == c else 0 for s in graph.sources])
        # Suffixes are unrestricted: later cut vertices may occur.
        values = [0]*graph.n; values[c] = ops.one(c)
        for u in order:
            work.vertex_visits += 1
            if not values[u]: continue
            for v, f in out[u]:
                values[v] ^= ops.mul(c, u, v, f, values[u])
                work.compositions += 1
        for ti, t in enumerate(graph.targets): B[ti][ci] = values[t]
    return Factors(graph.sources, graph.targets, cut, A, B, work)

@dataclass(frozen=True)
class CutCertificate:
    cut: tuple[int, ...]
    capacity: int
    flows: tuple[int, ...]


def split_network(graph: DAG, capacities: Sequence[int]):
    if len(capacities) != graph.n or any(type(x) is not int or x < 0 for x in capacities):
        raise ValueError("one nonnegative integer capacity per vertex is required")
    inf = sum(capacities)+1; s = 2*graph.n; t = s+1
    arcs = [(2*v, 2*v+1, cap) for v,cap in enumerate(capacities)]
    arcs += [(2*u+1, 2*v, inf) for u,v,_ in graph.edges]
    arcs += [(s, 2*v, inf) for v in graph.sources]
    arcs += [(2*v+1, t, inf) for v in graph.targets]
    return arcs, s, t


def minimum_vertex_cut(graph: DAG, capacities: Sequence[int] | None = None) -> CutCertificate:
    """Exact weighted cut via Edmonds-Karp; integral capacities stay binary encoded."""
    if capacities is None: capacities = [1]*graph.n
    arcs, s, t = split_network(graph, capacities); n = t+1
    adj = [[] for _ in range(n)]; to = []; residual = []
    for u,v,cap in arcs:
        i = len(to); to.extend((v,u)); residual.extend((cap,0))
        adj[u].append(i); adj[v].append(i+1)
    flow = 0
    while True:
        parent = [-1]*n; parent[s] = -2; todo = deque([s])
        while todo and parent[t] == -1:
            u = todo.popleft()
            for e in adj[u]:
                v = to[e]
                if residual[e] > 0 and parent[v] == -1:
                    parent[v] = e; todo.append(v)
                    if v == t: break
        if parent[t] == -1: break
        amount = sum(capacities)+1; v = t
        while v != s:
            e = parent[v]; amount = min(amount,residual[e]); v = to[e^1]
        v = t
        while v != s:
            e = parent[v]; residual[e] -= amount; residual[e^1] += amount; v = to[e^1]
        flow += amount
    reachable = set([s]); todo = [s]
    while todo:
        u = todo.pop()
        for e in adj[u]:
            v = to[e]
            if residual[e] > 0 and v not in reachable:
                reachable.add(v); todo.append(v)
    cut = tuple(v for v in range(graph.n) if 2*v in reachable and 2*v+1 not in reachable)
    certificate = CutCertificate(cut, sum(capacities[v] for v in cut),
                                 tuple(cap-residual[2*i] for i,(_,_,cap) in enumerate(arcs)))
    if certificate.capacity != flow or not verify_cut_certificate(graph, capacities, certificate):
        raise ArithmeticError("internal flow/cut inconsistency")
    return certificate


def verify_cut_certificate(graph: DAG, capacities: Sequence[int], cert: CutCertificate) -> bool:
    """Independent feasibility + cut check; no optimizer is called."""
    try:
        arcs,s,t = split_network(graph,capacities)
        if not graph.separates(cert.cut) or type(cert.capacity) is not int: return False
        if len(arcs) != len(cert.flows) or cert.capacity != sum(capacities[v] for v in cert.cut): return False
        balance = [0]*(t+1)
        for (u,v,cap),f in zip(arcs,cert.flows):
            if type(f) is not int or not 0 <= f <= cap: return False
            balance[u] -= f; balance[v] += f
        return (balance[s] == -cert.capacity and balance[t] == cert.capacity
                and all(balance[v] == 0 for v in range(s)))
    except (ValueError, IndexError, TypeError):
        return False
