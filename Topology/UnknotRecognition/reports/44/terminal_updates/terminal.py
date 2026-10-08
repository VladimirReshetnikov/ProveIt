"""Signed graph cofactors under terminal identifications.

The graph layer deliberately does not assert that a graph is a knot diagram.
The maintained BoundaryTait geometry must validate a completion before using
this observer to make a statement about that completion.
"""
from __future__ import annotations
from dataclasses import dataclass
from math import prod
from typing import Iterable, Sequence
from .linear import (Matrix, Budget, DynamicRank, bareiss, det_mod, eye,
                     is_prime, matmul, square, tick, transpose,
                     verify_normal_form)

@dataclass(frozen=True)
class SignedGraph:
    vertices: int
    edges: tuple[tuple[int, int, int], ...]

    def __post_init__(self) -> None:
        if type(self.vertices) is not int or self.vertices < 1:
            raise ValueError('at least one graph vertex is required')
        try:
            immutable_edges = tuple(tuple(edge) for edge in self.edges)
        except TypeError as exc:
            raise ValueError('edges must be a sequence of integer triples') from exc
        object.__setattr__(self, 'edges', immutable_edges)
        for edge in self.edges:
            if len(edge) != 3 or any(type(x) is not int for x in edge):
                raise ValueError('edges must be integer triples')
            u, v, _ = edge
            if not (0 <= u < self.vertices and 0 <= v < self.vertices):
                raise ValueError('edge endpoint out of range')

    def laplacian(self) -> Matrix:
        out = [[0]*self.vertices for _ in range(self.vertices)]
        for u, v, w in self.edges:
            if u == v:
                continue
            out[u][u] += w
            out[v][v] += w
            out[u][v] -= w
            out[v][u] -= w
        return out

    @property
    def uniform_bound(self) -> int:
        # Every quotient spanning tree is a subset of original non-loop edges.
        return prod(1+abs(w) for u, v, w in self.edges if u != v)

    @classmethod
    def from_laplacian(cls, laplacian: Sequence[Sequence[int]]) -> 'SignedGraph':
        n = len(laplacian)
        if n < 1 or any(len(row) != n for row in laplacian):
            raise ValueError('a nonempty square Laplacian is required')
        if any(type(z) is not int for row in laplacian for z in row):
            raise ValueError('integral Laplacian required')
        if any(sum(row) for row in laplacian):
            raise ValueError('Laplacian rows must sum to zero')
        if any(laplacian[i][j] != laplacian[j][i] for i in range(n) for j in range(n)):
            raise ValueError('symmetric Laplacian required')
        edges = tuple((i, j, -laplacian[i][j]) for i in range(n)
                      for j in range(i+1, n) if laplacian[i][j])
        return cls(n, edges)


def check_terminals(vertices: int, terminals: Sequence[int]) -> tuple[int, ...]:
    t = tuple(terminals)
    if not t or any(type(v) is not int or not 0 <= v < vertices for v in t):
        raise ValueError('a nonempty list of valid terminals is required')
    if len(set(t)) != len(t):
        raise ValueError('terminals must be distinct')
    return t


def blocks_from_labels(labels: Sequence[int], b: int) -> dict[int, frozenset[int]]:
    if len(labels) != b or any(type(x) is not int for x in labels):
        raise ValueError('partition must contain one integer label per terminal')
    blocks: dict[int, list[int]] = {}
    for i, label in enumerate(labels):
        blocks.setdefault(label, []).append(i)
    return {min(v): frozenset(v) for v in blocks.values()}


def anchored_blocks_from_labels(labels: Sequence[int], b: int) -> dict[int, frozenset[int]]:
    """Decode labels that name the actual retained anchors, not just a partition."""
    if len(labels) != b or any(type(a) is not int or not 0 <= a < b for a in labels):
        raise ValueError('invalid anchored labels')
    groups: dict[int, set[int]] = {}
    for i, a in enumerate(labels):
        groups.setdefault(a, set()).add(i)
    blocks = {a: frozenset(group) for a, group in groups.items()}
    labels_from_blocks(blocks, b)
    return blocks


def labels_from_blocks(blocks: dict[int, frozenset[int]], b: int) -> tuple[int, ...]:
    result = [-1]*b
    for anchor, block in blocks.items():
        if anchor not in block:
            raise ValueError('block anchor is not in its block')
        for i in block:
            if not 0 <= i < b or result[i] != -1:
                raise ValueError('invalid partition blocks')
            result[i] = anchor
    if any(x < 0 for x in result) or result[0] != 0:
        raise ValueError('partition must cover all terminals and root at zero')
    return tuple(result)


def quotient_cofactor(graph: SignedGraph, terminals: Sequence[int],
                       labels: Sequence[int]) -> Matrix:
    """Independent quotient construction over the integers, before elimination."""
    t = check_terminals(graph.vertices, terminals)
    blocks = blocks_from_labels(labels, len(t))
    owner = {i: a for a, group in blocks.items() for i in group}
    term_index = {v: i for i, v in enumerate(t)}
    keys = [('t', owner[term_index[v]]) if v in term_index else ('i', v)
            for v in range(graph.vertices)]
    root = keys[t[0]]
    active = sorted(set(keys)-{root})
    ids = {key: i for i, key in enumerate(active)}
    d = [[0]*len(ids) for _ in ids]
    for u, v, w in graph.edges:
        ku, kv = keys[u], keys[v]
        if ku == kv:
            continue
        if ku != root:
            d[ids[ku]][ids[ku]] += w
        if kv != root:
            d[ids[kv]][ids[kv]] += w
        if ku != root and kv != root:
            d[ids[ku]][ids[kv]] -= w
            d[ids[kv]][ids[ku]] -= w
    return d


class TerminalKernel:
    """Prime-specific, singular-safe elimination of a fixed graph interior."""
    def __init__(self, graph: SignedGraph, terminals: Sequence[int], p: int,
                 budget: Budget | None = None):
        if not is_prime(p):
            raise ValueError('modulus must be prime')
        self.graph, self.terminals, self.p = graph, check_terminals(graph.vertices, terminals), p
        self.b = len(self.terminals)
        self.t = self.b-1
        termset = set(self.terminals)
        self.interior = tuple(v for v in range(graph.vertices) if v not in termset)
        order = self.interior+self.terminals[1:]
        lap = graph.laplacian()
        tick(budget, max(1, len(lap)**2))
        self.grounded = [[lap[i][j] % p for j in order] for i in order]
        h, t = len(self.interior), self.t
        a = [row[:h] for row in self.grounded[:h]]
        normal = DynamicRank(a, p, budget, _prime_checked=True)
        self.interior_certificate = normal.certificate()
        self.nullity = h-normal.rank
        self.factor = normal.scale
        self.all_zero = self.nullity > t
        self.dimension = 0 if self.all_zero else self.nullity+t
        self.base: Matrix = []
        if self.all_zero:
            return
        rho, r = normal.rank, self.nullity
        # Keep rectangular empty matrices explicit where needed.
        b0 = [row[h:] for row in self.grounded[:h]]
        e0 = [row[:h] for row in self.grounded[h:]]
        left_b = matmul(normal.left, b0, p) if h else []
        e_right = matmul(e0, normal.right, p) if h else [[] for _ in range(t)]
        s = [row[h:] for row in self.grounded[h:]]
        for i in range(t):
            tick(budget, max(1, t*rho))
            for j in range(t):
                s[i][j] = (s[i][j]-sum(e_right[i][k]*left_b[k][j]
                                      for k in range(rho))) % p
        self.base = [[0]*r+left_b[rho+i] for i in range(r)]
        self.base += [e_right[i][rho:]+s[i] for i in range(t)]
        tick(budget, 1)

    def matrix_for(self, blocks: dict[int, frozenset[int]]) -> Matrix:
        """Fixed-size row-constraint matrix; its determinant is the quotient cofactor/factor."""
        labels_from_blocks(blocks, self.b)
        if self.all_zero:
            return []
        n, r, p = self.dimension, self.nullity, self.p
        m = [row[:] for row in self.base]
        for a, group in blocks.items():
            if a:
                m[r+a-1] = [sum(self.base[r+i-1][j] for i in group) % p for j in range(n)]
            for i in group:
                if i == a:
                    continue
                row = [0]*n
                row[r+i-1] = 1
                if a:
                    row[r+a-1] = -1 % p
                m[r+i-1] = row
        return m

    def small_matrix(self, blocks: dict[int, frozenset[int]]) -> Matrix | None:
        """Smallest straightforward singular-safe border for a static query."""
        labels_from_blocks(blocks, self.b)
        active = [(a, blocks[a]) for a in sorted(blocks) if a]
        q, r, p = len(active), self.nullity, self.p
        if self.all_zero or r > q:
            return None  # determinant is necessarily zero
        m = [[0]*(r+q) for _ in range(r+q)]
        for i in range(r):
            for j, (_, group) in enumerate(active):
                m[i][r+j] = sum(self.base[i][r+v-1] for v in group) % p
        for i, (_, group) in enumerate(active):
            for j in range(r):
                m[r+i][j] = sum(self.base[r+v-1][j] for v in group) % p
            for j, (_, other) in enumerate(active):
                m[r+i][r+j] = sum(self.base[r+v-1][r+w-1]
                                  for v in group for w in other) % p
        return m

    def query(self, labels: Sequence[int]) -> int:
        small = self.small_matrix(blocks_from_labels(labels, self.b))
        return 0 if small is None else self.factor*det_mod(small, self.p) % self.p

    def cursor(self, budget: Budget | None = None) -> 'PartitionCursor':
        return PartitionCursor(self, budget)

    def certificate(self) -> dict:
        return dict(p=self.p, terminals=list(self.terminals),
                    interior=self.interior_certificate)


class PartitionCursor:
    """Persistent-by-copy terminal merges; unsuccessful merges publish nothing."""
    def __init__(self, kernel: TerminalKernel, budget: Budget | None = None):
        self.kernel = kernel
        self.blocks = {i: frozenset((i,)) for i in range(kernel.b)}
        self.normal = (None if kernel.all_zero else
                       DynamicRank(kernel.base, kernel.p, budget, _prime_checked=True))
        self.edits = 0

    @property
    def labels(self) -> tuple[int, ...]:
        return labels_from_blocks(self.blocks, self.kernel.b)

    @property
    def residue(self) -> int:
        return (0 if self.normal is None else
                self.kernel.factor*self.normal.determinant % self.kernel.p)

    def merged(self, target: int, source: int, budget: Budget | None = None) -> 'PartitionCursor':
        """Return a child, joining source into target, retaining target's anchor.

        The root block can only be the target. The parent remains unchanged
        on success, exhaustion, or allocation failure. Each child costs O(b^2).
        """
        tick(budget, 1)
        if target not in self.blocks or source not in self.blocks or target == source or source == 0:
            raise ValueError('two distinct live anchors are required; source must not be root')
        kernel = self.kernel
        child = object.__new__(PartitionCursor)
        child.kernel, child.edits = kernel, self.edits+1
        child.blocks = self.blocks.copy()
        group = self.blocks[source]
        child.blocks[target] = child.blocks[target] | group
        del child.blocks[source]
        child.normal = None if self.normal is None else self.normal.clone(budget)
        if child.normal is not None:
            n, r, p = kernel.dimension, kernel.nullity, kernel.p
            e = [0]*n
            e[r+source-1] = 1
            if target:
                e[r+target-1] = -1 % p
            chi = [0]*n
            for i in group:
                chi[r+i-1] = 1
            w = []
            for j in range(n):
                tick(budget, len(group))
                w.append(sum(kernel.base[r+i-1][j] for i in group) % p)
            # Delta = -e*w^T + chi*e^T. Intermediate matrices may be singular.
            child.normal.update([(-z) % p for z in e], w, budget)
            child.normal.update(chi, e, budget)
        tick(budget, 1)
        return child

    def certificate(self) -> dict:
        return dict(labels=list(self.labels),
                    normal=None if self.normal is None else self.normal.certificate())


def enough_primes(bound: int) -> tuple[int, ...]:
    """Small deterministic primes whose product exceeds 2*bound."""
    if type(bound) is not int or bound < 1:
        raise ValueError('a positive integer bound is required')
    primes, modulus, candidate = [], 1, 2
    while modulus <= 2*bound:
        if is_prime(candidate):
            primes.append(candidate)
            modulus *= candidate
        candidate += 1 if candidate == 2 else 2
    return tuple(primes)


def reconstruct(residues: Sequence[int], primes: Sequence[int], bound: int) -> int:
    if len(residues) != len(primes) or len(set(primes)) != len(primes):
        raise ValueError('residues need distinct corresponding primes')
    if type(bound) is not int or bound < 0:
        raise ValueError('invalid absolute-value bound')
    x, modulus = 0, 1
    for residue, p in zip(residues, primes):
        if not is_prime(p) or type(residue) is not int:
            raise ValueError('invalid prime or residue')
        z = ((residue-x)*pow(modulus, -1, p)) % p
        x += modulus*z
        modulus *= p
    if modulus <= 2*bound:
        raise ValueError('insufficient modulus for a unique signed reconstruction')
    value = x if 2*x <= modulus else x-modulus
    if abs(value) > bound:
        raise ArithmeticError('residues violate the certified bound')
    return value


class ExactObserver:
    def __init__(self, graph: SignedGraph, terminals: Sequence[int],
                 budget: Budget | None = None):
        self.graph, self.terminals = graph, check_terminals(graph.vertices, terminals)
        self.bound = graph.uniform_bound
        self.primes = enough_primes(self.bound)
        self.kernels = tuple(TerminalKernel(graph, self.terminals, p, budget) for p in self.primes)

    def query(self, labels: Sequence[int]) -> int:
        return reconstruct([k.query(labels) for k in self.kernels], self.primes, self.bound)

    def cursor(self, budget: Budget | None = None) -> 'ExactCursor':
        obj = object.__new__(ExactCursor)
        obj.observer = self
        obj.cursors = tuple(k.cursor(budget) for k in self.kernels)
        return obj


class ExactCursor:
    @property
    def labels(self) -> tuple[int, ...]:
        return self.cursors[0].labels

    @property
    def value(self) -> int:
        o = self.observer
        return reconstruct([c.residue for c in self.cursors], o.primes, o.bound)

    def merged(self, target: int, source: int, budget: Budget | None = None) -> 'ExactCursor':
        child = object.__new__(ExactCursor)
        child.observer = self.observer
        child.cursors = tuple(c.merged(target, source, budget) for c in self.cursors)
        tick(budget, 1)
        return child

    def certificate(self) -> dict:
        o = self.observer
        return dict(schema='terminal-cofactor-v1',
                    graph=dict(vertices=o.graph.vertices, edges=[list(e) for e in o.graph.edges]),
                    terminals=list(o.terminals), labels=list(self.labels),
                    value=self.value, bound=o.bound,
                    fields=[dict(kernel=k.certificate(), endpoint=c.certificate())
                            for k, c in zip(o.kernels, self.cursors)])


def verify_exact_certificate(certificate: dict) -> bool:
    """Verify graph binding, field normal forms, endpoint determinants, and CRT.

    This is a deterministic polynomial-time verifier, not a quadratic verifier.
    It derives the border again but never calls DynamicRank.update.
    """
    try:
        if certificate['schema'] != 'terminal-cofactor-v1':
            return False
        if type(certificate['value']) is not int or type(certificate['bound']) is not int:
            return False
        g = certificate['graph']
        graph = SignedGraph(g['vertices'], tuple(tuple(e) for e in g['edges']))
        terminals = check_terminals(graph.vertices, certificate['terminals'])
        labels = certificate['labels']
        blocks = anchored_blocks_from_labels(labels, len(terminals))
        bound = graph.uniform_bound
        if certificate['bound'] != bound:
            return False
        lap = graph.laplacian()
        interior = tuple(i for i in range(graph.vertices) if i not in set(terminals))
        order = interior+terminals[1:]
        h, t = len(interior), len(terminals)-1
        full = [[lap[i][j] for j in order] for i in order]
        a = [row[:h] for row in full[:h]]
        primes, residues = [], []
        for field in certificate['fields']:
            kc, ec = field['kernel'], field['endpoint']
            p, ic = kc['p'], kc['interior']
            if kc['terminals'] != list(terminals) or ic['p'] != p:
                return False
            if not verify_normal_form(a, ic) or ec['labels'] != labels:
                return False
            rho, r = ic['rank'], h-ic['rank']
            if r > t:
                if ec['normal'] is not None:
                    return False
                residue = 0
            else:
                b0 = [row[h:] for row in full[:h]]
                e0 = [row[:h] for row in full[h:]]
                lb = matmul(ic['left'], b0, p) if h else []
                er = matmul(e0, ic['right'], p) if h else [[] for _ in range(t)]
                s = [row[h:] for row in full[h:]]
                for i in range(t):
                    for j in range(t):
                        s[i][j] = (s[i][j]-sum(er[i][k]*lb[k][j] for k in range(rho))) % p
                base = [[0]*r+lb[rho+i] for i in range(r)]
                base += [er[i][rho:]+s[i] for i in range(t)]
                # Build the row-constraint matrix without the kernel object.
                m = [row[:] for row in base]
                for anchor, group in blocks.items():
                    if anchor:
                        m[r+anchor-1] = [sum(base[r+i-1][j] for i in group) % p
                                        for j in range(r+t)]
                    for i in group:
                        if i == anchor:
                            continue
                        row = [0]*(r+t)
                        row[r+i-1] = 1
                        if anchor:
                            row[r+anchor-1] = -1 % p
                        m[r+i-1] = row
                nc = ec['normal']
                if nc is None or nc['p'] != p or not verify_normal_form(m, nc):
                    return False
                residue = ic['scale']*nc['scale'] % p if nc['rank'] == r+t else 0
            primes.append(p)
            residues.append(residue)
        return reconstruct(residues, primes, bound) == certificate['value']
    except (ValueError, TypeError, KeyError, ArithmeticError, IndexError):
        return False
