#!/usr/bin/env python3
"""Exact finite and algebraic checks for the accompanying manuscript.

Tests supplement, rather than replace, the general mathematical proofs.
The standard-library tests are mandatory. SymPy checks are optional and
are explicitly reported when the dependency is absent.
"""
from __future__ import annotations

import itertools
import json
import math
import random
import sys
import time
import traceback
from collections import Counter
from fractions import Fraction
from pathlib import Path
from typing import Callable, Iterable

ROOT = Path(__file__).resolve().parent
STATS: Counter[str] = Counter()
DETAILS: list[dict] = []


def require(condition: bool, message: str) -> None:
    if not condition:
        raise AssertionError(message)


def submasks(mask: int) -> Iterable[int]:
    s = mask
    while True:
        yield s
        if s == 0:
            return
        s = (s - 1) & mask


def bits(mask: int) -> list[int]:
    result = []
    while mask:
        low = mask & -mask
        result.append(low.bit_length() - 1)
        mask ^= low
    return result


class FiniteAbelianGroup:
    def __init__(self, factors: tuple[int, ...]):
        self.factors = factors
        self.elements = list(itertools.product(*(range(q) for q in factors)))
        self.index = {v: i for i, v in enumerate(self.elements)}
        self.N = len(self.elements)
        self.full = (1 << self.N) - 1
        self.add = [[self.index[tuple((a+b) % q for a,b,q in zip(x,y,factors))]
                     for y in self.elements] for x in self.elements]
        self.neg = [self.index[tuple((-a) % q for a,q in zip(x,factors))]
                    for x in self.elements]
        self.shifts = []
        for t in range(self.N):
            row = [0] * (1 << self.N)
            for mask in range(1, 1 << self.N):
                low = mask & -mask
                i = low.bit_length() - 1
                row[mask] = row[mask ^ low] | (1 << self.add[i][t])
            self.shifts.append(row)
        self.sizes = [mask.bit_count() for mask in range(1 << self.N)]
        self.energy = [sum((mask & self.shifts[t][mask]).bit_count() ** 2
                           for t in range(self.N)) for mask in range(1 << self.N)]
        self.cubes = {1: [s*s for s in self.sizes], 2: self.energy}
        for k in (3, 4):
            prev = self.cubes[k-1]
            self.cubes[k] = [sum(prev[mask & self.shifts[t][mask]]
                                for t in range(self.N))
                             for mask in range(1 << self.N)]
        self.subgroups = [mask for mask in range(1, 1 << self.N)
                          if self.is_subgroup(mask)]
        self.cosets = sorted({self.shifts[t][H] for H in self.subgroups for t in range(self.N)})

    def is_subgroup(self, mask: int) -> bool:
        if not (mask & 1):
            return False
        support = bits(mask)
        return all(mask & (1 << self.add[a][b]) for a in support for b in support)

    def classify_boundary(self, H: int, D: int, k: int) -> bool:
        if D == 0:
            return True
        b = bits(D)[0]
        K = self.shifts[self.neg[b]][D]
        if not self.is_subgroup(K) or K & ~H:
            return False
        twice_b = self.add[b][b]
        if k == 2:
            return bool(H & (1 << twice_b))
        return bool(K & (1 << twice_b)) and all(K & (1 << self.add[t][t]) for t in bits(H))


def test_group(factors: tuple[int, ...]) -> None:
    g = FiniteAbelianGroup(factors)
    N = g.N
    for H in g.subgroups:
        hs = bits(H)
        h = len(hs)
        for R in submasks(H):
            r = R.bit_count()
            A = H ^ R
            ER = g.energy[R]
            expected2 = h**3 - 4*r*h*h + 6*r*r*h - 4*r**3 + ER
            require(g.energy[A] == expected2, f'energy complement: {factors}, H={H},R={R}')
            STATS['energy_complement_identities'] += 1
            U = [(R & g.shifts[t][R]).bit_count() for t in hs]
            Q = sum((R | g.shifts[t][R]).bit_count()**3 - g.energy[R | g.shifts[t][R]] for t in hs)
            P = h**4 - 8*r*h**3 + 28*r*r*h*h - 42*r**3*h + 21*r**4
            rhs = (6*h-15*r)*(r**3-ER) + 3*(r*ER-sum(u**3 for u in U)) + Q
            require(P-g.cubes[3][A] == rhs, f'cube complement identity: {factors},H={H},R={R}')
            STATS['cube_complement_identities'] += 1
            if 5*r <= 2*h:
                require(g.cubes[3][A] <= P, 'sharp complement bound')
                STATS['sharp_complement_bounds'] += 1
            if h % 2:
                odd_upper = h**4 - 8*r*h**3 + 28*r*r*h*h - 56*r**3*h + 12*h*ER + 58*r**4
                require(g.cubes[3][A] <= odd_upper, 'odd Bonferroni bound')
                STATS['odd_complement_bounds'] += 1
        outside = g.full ^ H
        for D in submasks(outside):
            s = D.bit_count()
            A = H | D
            for k in (2, 3, 4):
                ck = 2**(k+1)-2
                bound = h**(k+1) + ck*h*s**k + s**(k+1)
                actual = g.cubes[k][A]
                require(actual <= bound, f'boundary inequality: {factors},H={H},D={D},k={k}')
                require((actual == bound) == g.classify_boundary(H,D,k),
                        f'boundary equality classification: {factors},H={H},D={D},k={k}')
                STATS['boundary_inequalities_and_equalities'] += 1
    for A in range(1, 1 << N):
        n = A.bit_count()
        e2_num = n**3-g.energy[A]
        for k in (2,3,4):
            require(g.cubes[k][A] <= n**(k-2)*g.energy[A], 'cube-energy comparison')
            STATS['cube_energy_comparisons'] += 1
        if 60*e2_num < n**3:
            distances = [(A ^ C).bit_count() for C in g.cosets]
            d = min(distances)
            require(distances.count(d) == 1, 'nearest-coset uniqueness')
            require(e2_num >= d*n*(n-d), 'exact local energy bound')
            STATS['small_deficit_rounding_checks'] += 1
    DETAILS.append({'group': list(factors), 'order': N, 'subsets': 1 << N,
                    'subgroups': len(g.subgroups), 'cosets': len(g.cosets)})


def determinant(matrix: list[list[int]]) -> int:
    n = len(matrix)
    if n == 0:
        return 1
    if n == 1:
        return matrix[0][0]
    return sum((-1)**j * matrix[0][j] * determinant([row[:j]+row[j+1:] for row in matrix[1:]])
               for j in range(n))


def test_cube_census() -> None:
    vertices = list(itertools.product((0,1), repeat=3))
    counts = Counter()
    for inds in itertools.combinations(range(8),4):
        rows = [[1,*vertices[i]] for i in inds]
        d = abs(determinant(rows))
        counts[d] += 1
        if d == 0:
            pts = [vertices[i] for i in inds]
            rectangle = any(tuple(a+b for a,b in zip(pts[0],pts[j])) ==
                            tuple(a+b for a,b in zip(pts[u],pts[v]))
                            for j,u,v in ((1,2,3),(2,1,3),(3,1,2)))
            require(rectangle, 'rank-three quadruple must be a rectangle')
        if d == 2:
            require(len({sum(vertices[i]) % 2 for i in inds}) == 1, 'parity tetrahedron classification')
    require(counts == Counter({0:12,1:56,2:2}), f'cube determinant census: {counts}')
    for inds in itertools.combinations(range(8),3):
        rows = [[1,*vertices[i]] for i in inds]
        require(any(abs(determinant([[row[j] for j in cols] for row in rows])) == 1
                    for cols in itertools.combinations(range(4),3)), 'primitive triple')
    STATS['cube_vertex_configurations'] += 70+56
    DETAILS.append({'cube_determinants': dict(counts)})


def energy_small(S: set[int], subtract: Callable[[int,int],int]) -> int:
    counts = Counter(subtract(a,b) for a in S for b in S)
    return sum(v*v for v in counts.values())


def complement_counts(N: int, R: set[int], add: Callable[[int,int],int],
                      subtract: Callable[[int,int],int]) -> tuple[int,int]:
    r = len(R)
    E = N**3-4*r*N*N+6*r*r*N-4*r**3+energy_small(R,subtract)
    C3 = 0
    for t in range(N):
        B = R | {add(a,t) for a in R}
        b = len(B)
        C3 += N**3-4*b*N*N+6*b*b*N-4*b**3+energy_small(B,subtract)
    return E,C3


def test_large_near_extremizers() -> None:
    rng = random.Random(20261007)
    records = []
    specifications = [('cyclic',257),('cyclic',509),('binary',256),('binary',512)]
    for kind,N in specifications:
        if kind == 'cyclic':
            add = lambda a,b,N=N: (a+b) % N
            sub = lambda a,b,N=N: (a-b) % N
        else:
            add = lambda a,b: a ^ b
            sub = add
        samples = [{0}]
        if kind == 'binary':
            samples += [set(range(2)),set(range(4))]
        samples += [set(rng.sample(range(N),r)) for r in (2,3,4,5) for _ in range(2)]
        for R in samples:
            r = len(R); n=N-r
            E,C3 = complement_counts(N,R,add,sub)
            require(n**3-E >= r*n*(n-r), 'large local U2')
            require(n**4-C3 >= 4*r*n**3-10*r*r*n*n+6*r**3*n, 'large exact local U3')
            if kind == 'cyclic':
                require(n**4-C3 >= 4*r*n**3-10*r*r*n*n+8*r**3*n-35*r**4, 'large odd cubic bound')
            if r == 1:
                tau = 1 if kind=='cyclic' else N
                expected = N**4-8*N**3+28*N*N-44*N+21+2*tau
                require(C3 == expected, 'singleton-deletion torsion formula')
            STATS['large_near_extremizer_checks'] += 1
            records.append({'kind':kind,'order':N,'holes':r,
                            'energy_defect_numerator':n**3-E,
                            'cube_defect_numerator':n**4-C3})
    DETAILS.append({'large_example_samples': records})


def test_symbolic() -> dict:
    try:
        import sympy as sp
    except ImportError:
        return {'status':'skipped','reason':'SymPy is not installed; all finite checks still ran.'}
    x,y,d,e = sp.symbols('x y d e')
    F = (1-y)**4-4*x*(1-y)**3+10*x*x*(1-y)**2-6*x**3*(1-y)+14*(1+x-y)*y**3+y**4
    bracket = -8*d+4*y-2*d*d+10*d*y+8*y*y+6*d**3-8*d*d*y+16*d*y*y-26*y**3
    require(sp.expand(F.subs(x,d-y)-F.subs({x:d,y:0})-y*bracket)==0, 'mixed cubic polynomial')
    Fodd = F-2*x**3*(1-y)+35*x**4
    bracket_odd = -8*d+4*y+4*d*d+4*d*y+10*y*y-132*d**3+196*d*d*y-118*d*y*y+7*y**3
    require(sp.expand(Fodd.subs(x,d-y)-Fodd.subs({x:d,y:0})-y*bracket_odd)==0, 'odd mixed polynomial')
    inverse3 = e/4+sp.Rational(5,32)*e**2+sp.Rational(11,64)*e**3+sp.Rational(475,2048)*e**4
    require(sp.series(4*inverse3-10*inverse3**2+6*inverse3**3-e,e,0,5).removeO()==0, 'inverse U3 series')
    inverse_odd = e/4+sp.Rational(5,32)*e**2+sp.Rational(21,128)*e**3
    require(sp.series(4*inverse_odd-10*inverse_odd**2+8*inverse_odd**3-e,e,0,4).removeO()==0, 'inverse odd series')
    for k in range(4,9):
        q=k+1;c=2**(k+1)-2
        P=1-(1-d)**q-c*(1-d)*d**k-d**q
        if k==4:
            require(sp.expand(P-(5*d-10*d*d+10*d**3-35*d**4+30*d**5))==0, 'P4 expression')
        inv=e/q+sp.Rational(k,2*q*q)*e**2+sp.Rational(k*(2*k+1),6*q**3)*e**3
        require(sp.series(P.subs(d,inv)-e,e,0,4).removeO()==0, f'inverse higher series k={k}')
    STATS['symbolic_identity_checks'] += 10
    return {'status':'passed','sympy_version':sp.__version__}


def main() -> int:
    start=time.monotonic()
    result={'status':'running','note':'Finite and symbolic checks are not a proof-assistant verification.'}
    try:
        test_cube_census()
        for factors in [(2,),(3,),(4,),(5,),(6,),(7,),(8,),(9,),(10,),
                        (2,2),(2,2,2),(2,3),(3,3),(4,2)]:
            test_group(factors)
        test_large_near_extremizers()
        result['symbolic']=test_symbolic()
        result['status']='passed'
    except Exception as exc:
        result['status']='failed'
        result['error']=str(exc)
        result['traceback']=traceback.format_exc()
    result['counts']=dict(STATS)
    result['details']=DETAILS
    result['elapsed_seconds']=round(time.monotonic()-start,3)
    (ROOT/'verification_results.json').write_text(json.dumps(result,indent=2),encoding='utf-8')
    print(json.dumps({k:v for k,v in result.items() if k!='details'},indent=2))
    return 0 if result['status']=='passed' else 1


if __name__=='__main__':
    raise SystemExit(main())
