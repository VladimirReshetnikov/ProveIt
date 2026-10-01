#!/usr/bin/env python3
"""Exact analysis of binary, one-marker semilinear ray seeds.

A ray (b_i,b_j)+N*(u,v) allows the single 1 in 0**i + '1' + 0**j.
The seed also contains every all-zero word. Integers have arbitrary precision.
The structural class test is polynomial; maximum clique is exponential.
This implements ray inputs, NOT a general CFG-to-Presburger compiler.
"""
from __future__ import annotations
from dataclasses import dataclass
from fractions import Fraction
from math import gcd, isqrt
import argparse
import json
from pathlib import Path
from typing import Iterable

@dataclass(frozen=True)
class Ray:
    base: tuple[int, int]
    step: tuple[int, int]

    def __post_init__(self) -> None:
        if len(self.base) != 2 or len(self.step) != 2:
            raise ValueError('base and step must each have two entries')
        if any(type(x) is not int or x < 0 for x in (*self.base, *self.step)):
            raise ValueError('all coordinates must be nonnegative integers')

    @property
    def n0(self) -> int:
        return sum(self.base) + 1

    @property
    def q(self) -> int:
        return sum(self.step)

    def position(self, n: int) -> int | None:
        if self.q == 0:
            return self.base[0] if n == self.n0 else None
        if n < self.n0 or (n - self.n0) % self.q:
            return None
        return self.base[0] + self.step[0] * ((n - self.n0) // self.q)

    def affine(self) -> tuple[Fraction, Fraction]:
        if self.q == 0:
            raise ValueError('a finite point has no cofinal affine function')
        slope = Fraction(self.step[0], self.q)
        return slope, self.base[0] - slope * self.n0

    def as_dict(self) -> dict:
        return {'base': list(self.base), 'step': list(self.step)}


def support(rays: Iterable[Ray], n: int) -> set[int]:
    if n < 0:
        raise ValueError('length must be nonnegative')
    return {i for r in rays if (i := r.position(n)) is not None}


def crt_pair(a: int, m: int, b: int, n: int) -> tuple[int, int] | None:
    """Generalized CRT: return least residue and positive modulus."""
    if m <= 0 or n <= 0:
        raise ValueError('moduli must be positive')
    g = gcd(m, n)
    if (b - a) % g:
        return None
    reduced = n // g
    k = 0 if reduced == 1 else ((b-a)//g * pow(m//g, -1, reduced)) % reduced
    modulus = m * reduced
    return (a + m*k) % modulus, modulus


def compatibility_graph(rays: list[Ray]) -> tuple[list[Ray], list[set[int]]]:
    infinite = [r for r in rays if r.q]
    graph = [set() for _ in infinite]
    for i, r in enumerate(infinite):
        for j in range(i):
            s = infinite[j]
            if (r.n0-s.n0) % gcd(r.q, s.q) == 0 and r.affine() != s.affine():
                graph[i].add(j)
                graph[j].add(i)
    return infinite, graph


def maximum_clique(graph: list[set[int]]) -> list[int]:
    """Exact branch-and-bound; worst-case exponential, as required by hardness."""
    best: list[int] = []
    def visit(chosen: list[int], candidates: set[int]) -> None:
        nonlocal best
        if len(chosen) + len(candidates) <= len(best):
            return
        if not candidates:
            if len(chosen) > len(best):
                best = chosen[:]
            return
        while candidates:
            if len(chosen) + len(candidates) <= len(best):
                return
            v = max(candidates, key=lambda x: (len(graph[x] & candidates), -x))
            candidates.remove(v)
            new = chosen + [v]
            if len(new) > len(best):
                best = new[:]
            visit(new, candidates & graph[v])
    visit([], set(range(len(graph))))
    return sorted(best)


def structural_class(rays: list[Ray]) -> dict:
    infinite = [r for r in rays if r.q]
    interior = [(i,r) for i,r in enumerate(infinite) if all(r.step)]
    if not interior:
        return {'class': 'regular', 'obstruction_pair': None}
    for k,(i,r) in enumerate(interior):
        for j,s in interior[:k]:
            if r.affine()[0] != s.affine()[0]:
                common = crt_pair(r.n0,r.q,s.n0,s.q)
                if common is not None:
                    return {'class': 'not context-free',
                            'obstruction_pair': [j,i],
                            'interior_speeds': [str(s.affine()[0]),str(r.affine()[0])],
                            'common_length_congruence': list(common)}
    return {'class': 'linear context-free, nonregular', 'obstruction_pair': None}


def analyze(rays: list[Ray]) -> dict:
    infinite, graph = compatibility_graph(rays)
    clique = maximum_clique(graph)
    exceptional = {r.n0 for r in rays if r.q == 0}
    finite_max = max((len(support(rays,n)) for n in exceptional), default=0)
    k = max(len(clique),finite_max)
    depth = (max(1,k)-1).bit_length()
    return {**structural_class(rays), 'maximum_sites': k,
            'parallel_stabilization_depth': depth,
            'frozen_source_stabilization_depth': max(0,k-1),
            'cofinal_maximum_clique': clique,
            'infinite_ray_count': len(infinite),
            'finite_point_lengths': sorted(exceptional)}


def primes() -> Iterable[int]:
    p = 2
    while True:
        if all(p % d for d in range(2,isqrt(p)+1)):
            yield p
        p += 1


def graph_to_endpoint_rays(graph: list[set[int]]) -> list[Ray]:
    """Polynomial-bit CLIQUE reduction. Every resulting marker has speed 0."""
    size = len(graph)
    if any(v in graph[v] for v in range(size)):
        raise ValueError('graph must be loop-free')
    if any(not (0 <= w < size) or v not in graph[w]
           for v in range(size) for w in graph[v]):
        raise ValueError('graph must be undirected')
    congruences: list[list[tuple[int,int]]] = [[] for _ in graph]
    ps = iter(primes())
    for v in range(size):
        for w in range(v+1,size):
            if w not in graph[v]:
                p = next(ps)
                congruences[v].append((0,p))
                congruences[w].append((1,p))
    rays: list[Ray] = []
    for v, cs in enumerate(congruences):
        residue, modulus = 0,1
        for a,m in cs:
            merged = crt_pair(residue,modulus,a,m)
            if merged is None:
                raise AssertionError('distinct prime constraints must be compatible')
            residue,modulus = merged
        n0 = residue
        if n0 < v+1:
            n0 += ((v+1-n0+modulus-1)//modulus)*modulus
        rays.append(Ray((v,n0-v-1),(0,modulus)))
    return rays


def marker_family(k: int) -> list[Ray]:
    if k < 1:
        raise ValueError('k must be positive')
    return [Ray((j-1,k-j),(j,k+1-j)) for j in range(1,k+1)]


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('input', type=Path, help='JSON object containing a rays list')
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    try:
        data = json.loads(args.input.read_text(encoding='utf-8'))
        rays = [Ray(tuple(r['base']),tuple(r['step'])) for r in data['rays']]
        result = json.dumps(analyze(rays),indent=2) + '\n'
    except (OSError,ValueError,KeyError,TypeError) as exc:
        parser.exit(2,f'error: {exc}\n')
    if args.output:
        try:
            args.output.write_text(result,encoding='utf-8')
        except OSError as exc:
            parser.exit(2,f'error: {exc}\n')
    else:
        print(result,end='')

if __name__ == '__main__':
    main()
