#!/usr/bin/env python3
"""Exact finite checks for Sharp Affine Localization for Quadratic Phases.

Python 3.10+, standard library only. Handles prime fields and GF(9).
These tests corroborate the article; they are not proof-assistant certificates.
Run: python code/verify.py --output data/exact_checks.json
"""
from __future__ import annotations
import argparse
import itertools
import json
from math import comb, isqrt
from collections import Counter
from dataclasses import dataclass
from pathlib import Path
from typing import Iterable

Point = tuple[int, ...]
Cell = frozenset[Point]

@dataclass(frozen=True)
class Field:
    p: int
    degree: int = 1

    def __post_init__(self) -> None:
        if self.p < 3 or any(self.p % d == 0 for d in range(2, isqrt(self.p)+1)):
            raise ValueError('p must be an odd prime')
        if self.degree != 1 and (self.p, self.degree) != (3, 2):
            raise ValueError('Only prime fields and GF(9)=GF(3)[T]/(T^2+1) are implemented')

    @property
    def q(self) -> int:
        return self.p**self.degree

    def add(self, a: int, b: int) -> int:
        if self.degree == 1:
            return (a+b) % self.p
        return (a % 3+b % 3) % 3 + 3*((a//3+b//3) % 3)

    def neg(self, a: int) -> int:
        if self.degree == 1:
            return (-a) % self.p
        return (-a % 3) % 3 + 3*((-(a//3)) % 3)

    def sub(self, a: int, b: int) -> int:
        return self.add(a, self.neg(b))

    def mul(self, a: int, b: int) -> int:
        if self.degree == 1:
            return a*b % self.p
        a0,a1=a%3,a//3; b0,b1=b%3,b//3
        return (a0*b0-a1*b1) % 3 + 3*((a0*b1+a1*b0) % 3)

    def inv(self, a: int) -> int:
        if not a:
            raise ZeroDivisionError('zero has no multiplicative inverse')
        for b in range(1, self.q):
            if self.mul(a,b)==1:
                return b
        raise AssertionError('field implementation has a nonunit')


def axis(s: int, t: int) -> Point:
    return (t,0) if s==0 else (0,t)


def cross(F: Field) -> frozenset[Point]:
    return frozenset(axis(s,t) for s in (0,1) for t in range(F.q))


def affine_line(F: Field, base: Point, direction: Point) -> Cell:
    assert any(direction)
    return frozenset(tuple(F.add(a,F.mul(t,b)) for a,b in zip(base,direction)) for t in range(F.q))


def check_partition(cells: Iterable[Cell], domain: Iterable[Point]) -> list[Cell]:
    cells=list(cells); domain=set(domain)
    assert cells and all(cells)
    count=Counter(p for c in cells for p in c)
    assert set(count)==domain, 'partition has a missing or extraneous point'
    assert all(v==1 for v in count.values()), 'partition cells overlap'
    return cells


def zero_cycle(F: Field, reverse: bool=False) -> list[Cell]:
    out=[frozenset([(0,0,0,0)])]
    for s,t in itertools.product((0,1),repeat=2):
        fixed_first=(s==t) != reverse
        for a in range(1,F.q):
            if fixed_first:
                out.append(frozenset(axis(s,a)+axis(t,b) for b in range(F.q)))
            else:
                out.append(frozenset(axis(s,b)+axis(t,a) for b in range(F.q)))
    return out


def scalar_cross(F: Field, choose_axis: int=0) -> list[Cell]:
    return [frozenset(axis(choose_axis,t) for t in range(F.q))]+[
        frozenset([axis(1-choose_axis,t)]) for t in range(1,F.q)]


def global_two(F: Field) -> list[Cell]:
    q=F.q
    nonzero=[(x,y) for x in range(1,q) for y in range(1,q)]
    out=zero_cycle(F)
    for p in nonzero:
        out.extend(frozenset(x+p for x in c) for c in scalar_cross(F))
        out.extend(frozenset(p+x for x in c) for c in scalar_cross(F))
    out.extend(frozenset([a+b]) for a in nonzero for b in nonzero)
    return out


def all_zero_cells(F: Field) -> list[Cell]:
    """All nonempty affine subspaces in C x C, by the orthant lemma."""
    q=F.q; out=set()
    for s,t in itertools.product((0,1),repeat=2):
        embed=lambda p: axis(s,p[0])+axis(t,p[1])
        out.add(frozenset(embed(p) for p in itertools.product(range(q),repeat=2)))
        for a in itertools.product(range(q),repeat=2):
            for d in [(1,b) for b in range(q)]+[(0,1)]:
                out.add(frozenset(embed(p) for p in affine_line(F,a,d)))
    out.update(frozenset([a+b]) for a in cross(F) for b in cross(F))
    return sorted(out,key=lambda c:(len(c),sorted(c)))


def field_checks(F: Field) -> None:
    q=F.q
    for a,b,c in itertools.product(range(q),repeat=3):
        assert F.add(F.add(a,b),c)==F.add(a,F.add(b,c))
        assert F.mul(F.mul(a,b),c)==F.mul(a,F.mul(b,c))
        assert F.mul(a,F.add(b,c))==F.add(F.mul(a,b),F.mul(a,c))
    for a in range(q):
        assert F.add(a,F.neg(a))==0 and F.mul(a,1)==a
        if a: assert F.mul(a,F.inv(a))==1


def verify_field(F: Field) -> dict:
    q=F.q; field_checks(F)
    C=cross(F); X={a+b for a in C for b in C}
    cyc=[check_partition(zero_cycle(F,rev),X) for rev in (False,True)]
    assert set(cyc[0])!=set(cyc[1])
    assert all(len(c)==4*q-3 for c in cyc)
    prod=check_partition([frozenset(a+b for a in ca for b in cb)
                         for ca in scalar_cross(F) for cb in scalar_cross(F)],X)
    assert len(prod)==q*q
    cells=all_zero_cells(F)
    lines=[c for c in cells if len(c)==q]
    planes=[c for c in cells if len(c)==q*q]
    assert len(planes)==4
    skeleton={p for p in X if p[:2]==(0,0) or p[2:]==(0,0)}
    assert len(skeleton)==4*q-3
    assert all(L&skeleton for L in lines)
    for P in planes:
        T=skeleton-P
        assert len(T)==2*(q-1)
        assert all(L&T for L in lines if not L&P)
    glob=check_partition(global_two(F),itertools.product(range(q),repeat=4))
    expected=(q-1)**4+2*q*(q-1)**2+4*q-3
    assert len(glob)==expected
    for A in glob:
        vals={(F.mul(p[0],p[1]),F.mul(p[2],p[3])) for p in A}
        assert len(vals)==1
    return {'field_order':q,'characteristic':F.p,'extension_degree':F.degree,
            'zero_fiber_points':len(X),'all_zero_fiber_affine_cells':len(cells),
            'zero_fiber_lines':len(lines),'zero_fiber_planes':len(planes),
            'cyclic_partition_cells':4*q-3,'product_partition_cells':q*q,
            'full_two_phase_partition_cells':expected,
            'separate_full_partition_cells':(q*q-q+1)**2,
            'exact_full_saving':(q-1)*(q-3),
            'checks':'PASS'}


def split_scalar_check(q: int, r: int) -> dict:
    F=Field(q); values=range(q)
    dots=lambda x,y:sum(a*b for a,b in zip(x,y))%q
    cells=[]
    for x in itertools.product(values,repeat=r):
        ys=list(itertools.product(values,repeat=r))
        if not any(x):
            cells.append(frozenset(x+y for y in ys))
        else:
            for a in values:
                cells.append(frozenset(x+y for y in ys if dots(x,y)==a))
    check_partition(cells,itertools.product(values,repeat=2*r))
    assert len(cells)==q**(r+1)-q+1
    assert Counter(len(c) for c in cells)==Counter({q**r:1,q**(r-1):q**(r+1)-q})
    return {'q':q,'r':r,'cells':len(cells),'checks':'PASS'}



def zero_paired(F: Field, blocks: int) -> list[Cell]:
    """A paired affine partition of C^blocks; a zero-block space is one point."""
    if blocks < 0:
        raise ValueError('blocks must be nonnegative')
    cells = [frozenset([()])]
    for _ in range(blocks // 2):
        cells = [frozenset(a+b for a in left for b in right)
                 for left in cells for right in zero_cycle(F)]
    if blocks % 2:
        cells = [frozenset(a+b for a in left for b in right)
                 for left in cells for right in scalar_cross(F)]
    return cells


def adaptive_full(F: Field, blocks: int) -> list[Cell]:
    """Implement the singular-fiber decomposition and pair only zero blocks."""
    nonzero = [(x, y) for x in range(1, F.q) for y in range(1, F.q)]
    out = []
    for mask in itertools.product((False, True), repeat=blocks):
        zero_indices = [i for i, is_zero in enumerate(mask) if is_zero]
        fixed_indices = [i for i, is_zero in enumerate(mask) if not is_zero]
        for fixed_points in itertools.product(nonzero, repeat=len(fixed_indices)):
            fixed = dict(zip(fixed_indices, fixed_points))
            for zero_cell in zero_paired(F, len(zero_indices)):
                cell = set()
                for z in zero_cell:
                    pieces = dict(fixed)
                    pieces.update({index: z[2*j:2*j+2]
                                   for j, index in enumerate(zero_indices)})
                    cell.add(tuple(coordinate for i in range(blocks)
                                   for coordinate in pieces[i]))
                out.append(frozenset(cell))
    return out


def adaptive_check(q: int, blocks: int) -> dict:
    F = Field(q)
    cells = check_partition(adaptive_full(F, blocks),
                            itertools.product(range(q), repeat=2*blocks))
    for cell in cells:
        values = {tuple(F.mul(point[2*i], point[2*i+1])
                        for i in range(blocks)) for point in cell}
        assert len(values) == 1
    paired_zero = lambda k: (4*q-3)**(k//2) * q**(k%2)
    predicted = sum(comb(blocks, k)*(q-1)**(2*(blocks-k))*paired_zero(k)
                    for k in range(blocks+1))
    assert len(cells) == predicted
    return {'q': q, 'blocks': blocks, 'domain_points': q**(2*blocks),
            'adaptive_full_partition_cells': len(cells),
            'separate_full_partition_cells': (q*q-q+1)**blocks,
            'checks': 'PASS',
            'optimality': 'No general optimality claim for blocks greater than two'}


def main() -> None:
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',type=Path,default=Path('data/exact_checks.json'))
    args=parser.parse_args()
    report={'arithmetic':'exact finite-field operations; no floating point in checks',
            'fields':[verify_field(F) for F in [Field(3),Field(5),Field(7),Field(3,2),Field(11)]],
            'split_scalar':[split_scalar_check(q,r) for q,r in [(3,1),(3,2),(3,3),(5,2)]],
            'adaptive_families':[adaptive_check(q,m) for q,m in [(3,3),(3,4),(5,3)]],
            'logical_status':'finite corroboration, not a formal proof of the general theorems'}
    args.output.parent.mkdir(parents=True,exist_ok=True)
    args.output.write_text(json.dumps(report,indent=2)+'\n',encoding='utf8')
    print(json.dumps(report,indent=2))

if __name__=='__main__':
    main()
