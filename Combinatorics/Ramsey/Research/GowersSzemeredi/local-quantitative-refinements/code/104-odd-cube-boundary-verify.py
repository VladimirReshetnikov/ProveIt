#!/usr/bin/env python3
"""Exact finite checks for Odd-order cube stability and sharp subgroup boundaries.

Dependencies: numpy and sympy. All comparisons use integers or exact rational
arithmetic. Tests are supplementary to, not replacements for, the general proofs.
Run `python verify.py` in this directory. A deterministic JSON receipt is written.
"""
from __future__ import annotations
import argparse
import itertools as it
import json
from collections import Counter
from fractions import Fraction as Q
from pathlib import Path
from typing import Sequence

import numpy as np
import sympy as sp


def require(condition: bool, message: str) -> None:
    """Do not use assert: checks must remain active under python -O."""
    if not bool(condition):
        raise RuntimeError(message)


class Group:
    def __init__(self, moduli: Sequence[int]):
        self.moduli = tuple(moduli)
        self.elts = list(it.product(*(range(m) for m in moduli)))
        self.n = len(self.elts)
        index = {a: i for i, a in enumerate(self.elts)}
        self.add = np.array([[index[tuple((x+y) % m for x,y,m in
                          zip(a,b,self.moduli))] for b in self.elts]
                          for a in self.elts], dtype=np.int64)
        self.neg = np.array([index[tuple((-x) % m for x,m in
                              zip(a,self.moduli))] for a in self.elts])
        self.full = (1 << self.n)-1
        self.masks = np.arange(1 << self.n, dtype=np.int64)
        self.sizes = np.array([int(a).bit_count() for a in self.masks],
                              dtype=np.int64)
        self.shifts = np.zeros((self.n, 1 << self.n), dtype=np.int64)
        for t in range(self.n):
            for i in range(self.n):
                bit = 1 << i
                self.shifts[t, bit:2*bit] = (self.shifts[t, :bit] |
                                                    (1 << int(self.add[i,t])))
        self.intersections = self.masks[None, :] & self.shifts
        self.cubes = {1: self.sizes**2}
        for k in range(2, 7):
            self.cubes[k] = self.cubes[k-1][self.intersections].sum(axis=0)

    @property
    def name(self) -> str:
        return ' x '.join(f'C{m}' for m in self.moduli)

    def elements(self, mask: int) -> list[int]:
        return [i for i in range(self.n) if mask >> i & 1]

    def is_subgroup(self, mask: int) -> bool:
        return bool(mask & 1) and all(int(self.shifts[t, mask]) == mask
                                     for t in self.elements(mask))

    def is_coset(self, mask: int) -> bool:
        if not mask:
            return False
        b = (mask & -mask).bit_length()-1
        return self.is_subgroup(int(self.shifts[int(self.neg[b]), mask]))

    def subgroups(self) -> list[int]:
        return [int(a) for a in self.masks if self.is_subgroup(int(a))]


def check_group(g: Group) -> dict:
    n = g.sizes
    energy_def = n**3-g.cubes[2]
    comparison_count = 0
    for k in range(2, 7):
        cube_def = n**(k+1)-g.cubes[k]
        lower = n**(k-2)*energy_def
        require(np.all(cube_def >= lower), f'lower comparison {g.name} k={k}')
        require(np.all(cube_def <= (2**k-k-1)*lower),
                f'upper comparison {g.name} k={k}')
        comparison_count += len(n)-1

    boundary_count = universal_count = equality_count = one_fiber_count = 0
    diversity_count = energy_count = 0
    subgroups = g.subgroups()
    for H in subgroups:
        h = H.bit_count()
        outside = g.full ^ H
        ds = g.masks[(g.masks & H) == 0]
        ds = ds[ds != 0]
        if not len(ds):
            continue
        sizes = g.sizes[ds]
        union = ds | H
        no_two = all((H >> int(g.add[i,i]) & 1) == 0
                     for i in g.elements(outside))
        # Quotient-fiber diversity, calculated directly from intersections.
        RH = g.sizes[g.intersections[np.array(g.elements(H))[:, None],
                                    ds[None, :]]].sum(axis=0)
        P = sizes**2-RH
        for k in range(2, 7):
            universal = h**(k+1)+(2**(k+1)-2)*h*sizes**k+sizes**(k+1)
            require(np.all(g.cubes[k][union] <= universal),
                    f'universal boundary {g.name}, H={H}, k={k}')
            universal_count += len(ds)
            if not no_two:
                continue
            # beta_k - 1 = (3^k - 3*2^(k-1))/2^(k-1).
            denom = 2**(k-1)
            coeff = 3**k-3*denom
            a_scaled = 2*(k-1)*h*denom-coeff*sizes
            active = a_scaled >= 0
            if not np.any(active):
                continue
            dd, ss, aa, pp = ds[active], sizes[active], a_scaled[active], P[active]
            B = h**(k+1)+2*k*h*ss**k+ss**(k+1)-g.cubes[k][dd | H]
            require(np.all(B >= 0), f'odd boundary {g.name}, H={H}, k={k}')
            require(np.all(denom*B >= aa*ss**(k-2)*pp),
                    f'diversity remainder {g.name}, H={H}, k={k}')
            boundary_count += len(dd)
            diversity_count += len(dd)
            if k >= 3:
                ed = ss**3-g.cubes[2][dd]
                require(np.all(denom*B >= aa*ss**(k-3)*ed),
                        f'energy remainder {g.name}, H={H}, k={k}')
                energy_count += len(dd)
            for d, bdef, av, pv in zip(dd, B, aa, pp):
                if av > 0:
                    expected = int(pv) == 0 and g.is_coset(int(d))
                    require((int(bdef) == 0) == expected,
                            f'equality classification {g.name}, H={H}, D={d}, k={k}')
                    equality_count += 1
            # No size condition for the one-fiber identity.
            fiber = ds[P == 0]
            if len(fiber):
                rhs = h**(k+1)+2*k*h*g.cubes[k-1][fiber]+g.cubes[k][fiber]
                require(np.all(g.cubes[k][fiber | H] == rhs),
                        f'one-fiber identity {g.name}, H={H}, k={k}')
                one_fiber_count += len(fiber)
    return dict(group=g.name, order=g.n, subsets=2**g.n,
                nonempty_set_dimension_comparisons=comparison_count,
                subgroups=len(subgroups), universal_boundary_checks=universal_count,
                odd_quotient_boundary_checks=boundary_count,
                diversity_remainder_checks=diversity_count,
                energy_remainder_checks=energy_count,
                strict_equality_checks=equality_count,
                one_fiber_identity_checks=one_fiber_count)


def check_occupancy(g: Group) -> dict:
    require(g.n % 2 == 1, 'occupancy check requires odd group')
    vertices = []
    for x,a,b,c in it.product(range(g.n), repeat=4):
        vertices.append([x, g.add[x,a], g.add[x,b], g.add[g.add[x,a],b],
                         g.add[x,c], g.add[g.add[x,a],c], g.add[g.add[x,b],c],
                         g.add[g.add[g.add[x,a],b],c]])
    vertices = np.array(vertices, dtype=np.int64)
    checks = equality_checks = 0
    for R in range(1 << g.n):
        r,h = R.bit_count(),g.n
        occupancy = ((R >> vertices) & 1).sum(axis=1)
        counts = np.bincount(occupancy, minlength=9)
        ed = r**3-int(g.cubes[2][R])
        cd = r**4-int(g.cubes[3][R])
        T = h**4-8*r*h**3+28*r*r*h*h-44*r**3*h+23*r**4
        lhs = T-int(g.cubes[3][g.full ^ R])
        rhs = 12*h*ed-35*cd+int(counts[5]+5*counts[6]+15*counts[7])
        require(lhs == rhs, f'occupancy identity {g.name} R={R}')
        require(int(counts[8]) == int(g.cubes[3][R]), 'full occupancy count')
        require(lhs >= (12*h-140*r)*ed, f'complement bound {g.name} R={R}')
        if 0 < 35*r < 3*h:
            require((lhs == 0) == g.is_coset(R), 'complement equality')
            equality_checks += 1
        checks += 1
    return dict(group=g.name, parameter_cubes=len(vertices),
                subsets=checks, strict_complement_equality_checks=equality_checks)


def determinant_census() -> dict:
    V = [sp.Matrix([[1, *w]]) for w in it.product((0,1), repeat=3)]
    counts = Counter()
    four_dets = {}
    for S in it.combinations(range(8),4):
        matrix = sp.Matrix.vstack(*(V[i] for i in S))
        det = abs(int(matrix.det()))
        counts[str(det)] += 1
        four_dets[S] = det
        if det == 0:
            require(matrix.rank() == 3, 'singular quadruple rank')
            # Verify it is genuinely an affine parallelogram.
            require(any(V[S[0]]+V[S[j]] == V[S[a]]+V[S[b]]
                        for j,a,b in [(1,2,3),(2,1,3),(3,1,2)]),
                    'rank-three quadruple parallelogram')
    require(dict(counts) == {'0':12,'1':56,'2':2}, 'four-vertex census')
    for size in (1,2,3):
        for S in it.combinations(range(8),size):
            require(any(set(S).issubset(U) and det == 1
                        for U,det in four_dets.items()), 'unimodular extension')
    for S in it.combinations(range(8),5):
        require(any(set(U).issubset(S) and det == 1
                    for U,det in four_dets.items()), 'five-set unimodular basis')
    return dict(four_vertex_determinants=dict(sorted(counts.items())),
                small_subset_unimodular_extensions=8+28+56,
                five_vertex_unimodular_extensions=56)


def symbolic_checks() -> dict:
    h,r,d,y,t = sp.symbols('h r d y t')
    m = h-r
    T = h**4-8*r*h**3+28*r**2*h**2-44*r**3*h+23*r**4
    require(sp.expand(T-(m**4-4*r*m**3+10*r*r*m*m-8*r**3*m)) == 0,
            'cubic normalization')
    def F(x,y):
        return ((1-y)**4-4*x*(1-y)**3+10*x*x*(1-y)**2-8*x**3*(1-y)
                +14*(1+x-y)*y**3+y**4)
    quotient = sp.expand((F(d-y,y)-F(d,0))/y)
    expected = (-8*d+4*y+4*d*d+4*d*y+10*y*y+8*d**3
                -14*d*d*y+22*d*y*y-28*y**3)
    require(sp.expand(quotient-expected) == 0, 'mixed cubic polynomial')
    require(4-18*Q(1,50)-30*Q(1,50)**2 >= Q(7,2), 'mixed margin')
    k4 = sp.expand((1+t)**5-16*t*(1+t)**4+120*t*t*(1+t)**3-(1-t)**5)
    require(sp.expand(k4 - t*(-6+56*t+284*t*t+296*t**3+106*t**4)) == 0, 'four-cube hole polynomial')
    endpoint = 56*Q(1,49)+284*Q(1,49)**2+296*Q(1,49)**3+106*Q(1,49)**4
    require(endpoint < 3, 'four-cube hole margin')
    alpha = {str(k):str(Q(2*(k-1),1)/(2*Q(3,2)**k-3)) for k in range(2,9)}
    eps = sp.symbols('e')
    coeff = [sp.Rational(1,4)]
    for order in range(2,6):
        a = sp.symbols('a')
        series = sum(coeff[i-1]*eps**i for i in range(1,order))+a*eps**order
        term = sp.expand(4*series-10*series**2+8*series**3-eps).coeff(eps,order)
        coeff.append(sp.solve(term,a)[0])
    return dict(cubic_mixed_quotient=str(quotient),
                boundary_radius_alpha=alpha,
                inverse_cubic_coefficients=[str(v) for v in coeff],
                k4_hole_endpoint_positive_sum=str(endpoint))


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, default=Path(__file__).with_name('verification_results.json'))
    args = parser.parse_args()
    report = {'status':'PASS', 'arithmetic':'integer counts and exact rationals; no floating-point comparisons',
              'scope':'finite supplementary tests, not a proof-assistant certificate',
              'determinant_census':determinant_census(), 'symbolic':symbolic_checks(),
              'groups':[], 'occupancy':[]}
    groups = [(3,),(5,),(7,),(9,),(11,),(13,),(15,),
              (6,),(10,),(12,),(14,),(3,3),(2,2),(2,2,2),(2,2,2,2)]
    for moduli in groups:
        g = Group(moduli)
        row = check_group(g)
        report['groups'].append(row)
        if g.n % 2 and g.n <= 9:
            report['occupancy'].append(check_occupancy(g))
        print(json.dumps(row), flush=True)
    totals = {key:sum(row[key] for row in report['groups'])
              for key in report['groups'][0] if key not in ('group','order')}
    report['totals'] = totals
    args.output.write_text(json.dumps(report, indent=2, sort_keys=True)+'\n', encoding='utf-8')
    print('PASS: '+str(args.output), flush=True)

if __name__ == '__main__':
    main()
