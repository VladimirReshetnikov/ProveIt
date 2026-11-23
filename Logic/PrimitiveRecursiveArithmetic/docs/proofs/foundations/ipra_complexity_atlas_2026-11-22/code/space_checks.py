#!/usr/bin/env python3
"""Finite implementation checks for space.tex, not general formal proofs.

Independent checks compare an ordinary breadth-first reachability computation
with (i) actual evaluation of a single-copy quantified Boolean formula,
(ii) local forced-enumeration certificate validation, and (iii) the layered
acyclic reduction.  The testing implementation stores graphs/certificates;
it is not itself claimed to have logarithmic work space.
"""
from __future__ import annotations

import itertools
import json
from dataclasses import dataclass
from functools import lru_cache
from pathlib import Path


@dataclass(frozen=True)
class Graph:
    n: int
    bits: int

    def edge(self, u: int, v: int) -> bool:
        return 0 <= u < self.n and 0 <= v < self.n and bool(self.bits >> (u*self.n+v) & 1)


def bfs_paths(g: Graph, s: int, bound: int) -> dict[int, tuple[int, ...]]:
    paths = {s: (s,)}
    for _ in range(bound):
        new = dict(paths)
        for u, p in paths.items():
            for v in range(g.n):
                if g.edge(u, v) and v not in new:
                    new[v] = p + (v,)
        paths = new
    return paths


def path_ok(g: Graph, s: int, t: int, bound: int, p: tuple[int, ...]) -> bool:
    return bool(p) and p[0] == s and p[-1] == t and len(p)-1 <= bound and \
        all(0 <= u < g.n for u in p) and all(g.edge(u,v) for u,v in zip(p,p[1:]))


def negative_certificate_ok(g: Graph, s: int, v: int, i: int, count: int,
                            selections: tuple[tuple[int, ...] | None, ...]) -> bool:
    if len(selections) != g.n:
        return False
    accepted = 0
    for u, p in enumerate(selections):
        if p is not None:
            if not path_ok(g, s, u, i, p) or u == v or g.edge(u,v):
                return False
            accepted += 1
    return accepted == count


def layered(g: Graph) -> Graph:
    n = g.n*g.n
    bits = 0
    for i in range(g.n-1):
        for u in range(g.n):
            for v in range(g.n):
                if u == v or g.edge(u,v):
                    source, target = i*g.n+u, (i+1)*g.n+v
                    bits |= 1 << (source*n+target)
    return Graph(n, bits)


# QBF AST contains the actual quantifiers; the evaluator does not call graph
# reachability and does not special-case the selector construction.
def con(b): return ('c', bool(b))
def var(i): return ('v', i)
def neg(f): return ('not', f)
def conj(f,g): return ('and', f,g)
def disj(f,g): return ('or', f,g)
def implies(f,g): return disj(neg(f),g)
def iff(f,g): return conj(implies(f,g), implies(g,f))


def fold_and(fs):
    ans = con(True)
    for f in fs:
        ans = conj(ans, f)
    return ans


def fold_or(fs):
    ans = con(False)
    for f in fs:
        ans = disj(ans, f)
    return ans


def vector_equal(a,b):
    assert len(a) == len(b)
    return fold_and(iff(x,y) for x,y in zip(a,b))


def bits_vector(n,width):
    return tuple(con(n >> i & 1) for i in range(width))


def quantify(tag, ids, body):
    for i in reversed(ids):
        body = (tag, i, body)
    return body


def compact_reach_qbf(g: Graph, s: int, t: int, level: int):
    width = max(1, (g.n-1).bit_length())
    fresh = itertools.count()
    def build(k, u, v):
        if k == 0:
            edges = fold_or(conj(vector_equal(u,bits_vector(a,width)),
                                 vector_equal(v,bits_vector(b,width)))
                            for a in range(g.n) for b in range(g.n) if g.edge(a,b))
            return disj(vector_equal(u,v), edges)
        m = tuple(next(fresh) for _ in range(width))
        z = next(fresh)
        a = tuple(next(fresh) for _ in range(width))
        b = tuple(next(fresh) for _ in range(width))
        mv, av, bv = tuple(map(var,m)), tuple(map(var,a)), tuple(map(var,b))
        guard = conj(implies(neg(var(z)),conj(vector_equal(av,u),vector_equal(bv,mv))),
                     implies(var(z),conj(vector_equal(av,mv),vector_equal(bv,v))))
        child = build(k-1,av,bv)  # exactly ONE recursively constructed copy
        return quantify('ex',m,('all',z,quantify('ex',a,quantify('ex',b,conj(guard,child)))))
    return build(level,bits_vector(s,width),bits_vector(t,width))


def evaluate(formula):
    @lru_cache(maxsize=None)
    def go(f, assignment):
        kind = f[0]
        if kind == 'c': return f[1]
        if kind == 'v': return bool(assignment >> f[1] & 1)
        if kind == 'not': return not go(f[1],assignment)
        if kind == 'and': return go(f[1],assignment) and go(f[2],assignment)
        if kind == 'or': return go(f[1],assignment) or go(f[2],assignment)
        bit = 1 << f[1]
        lo, hi = assignment & ~bit, assignment | bit
        if kind == 'ex': return go(f[2],lo) or go(f[2],hi)
        if kind == 'all': return go(f[2],lo) and go(f[2],hi)
        raise ValueError(kind)
    result = go(formula,0)
    go.cache_clear()
    return result


def nodes(f):
    if f[0] in ('c','v'): return 1
    if f[0] in ('not',): return 1+nodes(f[1])
    if f[0] in ('ex','all'): return 1+nodes(f[2])
    return 1+nodes(f[1])+nodes(f[2])


def main():
    graphs = forced_tests = layer_tests = qbf_tests = 0
    for n in range(1,4):
        for bits in range(1 << (n*n)):
            graphs += 1
            g = Graph(n,bits)
            h = layered(g)
            for s in range(n):
                reach = bfs_paths(g,s,n)
                hreach = bfs_paths(h,s,n-1)
                for t in range(n):
                    assert (t in reach) == ((n-1)*n+t in hreach)
                    layer_tests += 1
                for i in range(n):
                    paths = bfs_paths(g,s,i)
                    nextpaths = bfs_paths(g,s,i+1)
                    for v in range(n):
                        # Enumerate ALL subsets, using independently obtained
                        # valid paths.  Exact counts must force the whole row.
                        for subset in range(1 << n):
                            selection = tuple(paths.get(u) if subset >> u & 1 else None for u in range(n))
                            result = negative_certificate_ok(g,s,v,i,len(paths),selection)
                            all_selected = all(selection[u] is not None for u in paths)
                            assert result == (all_selected and v not in nextpaths)
                            forced_tests += 1
            if n <= 2:
                for s in range(n):
                    for t in range(n):
                        sizes = []
                        for k in range(4):
                            f = compact_reach_qbf(g,s,t,k)
                            assert evaluate(f) == (t in bfs_paths(g,s,2**k))
                            sizes.append(nodes(f))
                            qbf_tests += 1
                        increments = [b-a for a,b in zip(sizes,sizes[1:])]
                        assert len(set(increments)) == 1, sizes
    # Larger width checks ensure selector vector constraints are bitwise.
    for g in (Graph(3,0),Graph(3, (1 << 1) | (1 << 5)), Graph(4, (1 << 1) | (1 << 6) | (1 << 11))):
        for k in range(3):
            f = compact_reach_qbf(g,0,g.n-1,k)
            assert evaluate(f) == (g.n-1 in bfs_paths(g,0,2**k))
            qbf_tests += 1
    report = dict(status='passed', directed_graphs=graphs,
                  forced_enumeration_subset_checks=forced_tests,
                  layered_reduction_endpoint_checks=layer_tests,
                  actual_qbf_evaluation_checks=qbf_tests,
                  qbf_size_growth='linear in recursion depth, checked',
                  limits='Finite tests; no general proof or small-space claim for this Python implementation.')
    print(json.dumps(report,indent=2))


if __name__ == '__main__':
    main()
