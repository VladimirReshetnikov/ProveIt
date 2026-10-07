#!/usr/bin/env python3
"""Exact certificates for Finite-grid formulae and exact core-avoidance laws.

Python >= 3.10; standard library only.  No network or proof-assistant calls.
Run from any directory: python code/verify.py --max-d 10
The universal compact-formula check is symbolic over all 512 grid supports;
checking a finite list of d values is only an additional consistency test.
"""
from __future__ import annotations
import argparse
from collections import Counter, defaultdict
from fractions import Fraction
from itertools import combinations, permutations, product
from math import comb, gcd, isqrt, prod, pi, sqrt
from pathlib import Path
import json

F = Fraction
GRID = tuple(product((-1, 0, 1), repeat=2))
ROOT = Path(__file__).resolve().parents[1]
DATA = ROOT / "data"

def primitive(values: tuple[int, ...]) -> tuple[int, ...] | None:
    divisor = 0
    for value in values:
        divisor = gcd(divisor, abs(value))
    if not divisor:
        return None
    answer = tuple(value // divisor for value in values)
    if next(value for value in answer if value) < 0:
        answer = tuple(-value for value in answer)
    return answer

def grid_template(mask: int) -> dict | None:
    points = tuple(GRID[i] for i in range(9) if mask >> i & 1)
    basis = None
    for o, u, v in combinations(points, 3):
        a, b = u[0] - o[0], u[1] - o[1]
        c, e = v[0] - o[0], v[1] - o[1]
        determinant = a * e - b * c
        if determinant:
            basis = o, a, b, c, e, determinant
            break
    if basis is None:
        return None
    o, a, b, c, e, determinant = basis
    directions = set()
    for z0, z1, z2 in product((-1, 0, 1), repeat=3):
        # Affine function (A + B*x + C*y)/determinant, by Cramer's rule.
        B = (z1 - z0) * e - (z2 - z0) * b
        C = a * (z2 - z0) - c * (z1 - z0)
        A = determinant * z0 - B * o[0] - C * o[1]
        if not (B or C):
            continue
        if all(A + B*x + C*y in (-determinant, 0, determinant)
               for x, y in points):
            directions.add(primitive((B, C)))
    c1 = 6 if len({x for x, _ in points}) == 2 else 2
    c2 = 6 if len({y for _, y in points}) == 2 else 2
    assert 2 <= len(directions) <= 6
    return dict(mask=mask, points=points, nu=len(directions), c1=c1, c2=c2,
                directions=sorted(directions))

def all_templates() -> list[dict]:
    return [record for mask in range(512)
            if (record := grid_template(mask)) is not None]

def walk_energies(max_d: int):
    """For every T subset of the grid, F_d(T), then exact-support N_d(T)."""
    walks = [{(0, 0): 1} for _ in range(512)]
    supports = [[GRID[i] for i in range(9) if mask >> i & 1]
                for mask in range(512)]
    for d in range(1, max_d + 1):
        energies = []
        for mask, steps in enumerate(supports):
            nxt = defaultdict(int)
            for (x, y), count in walks[mask].items():
                for dx, dy in steps:
                    nxt[x + dx, y + dy] += count
            walks[mask] = dict(nxt)
            energies.append(sum(value * value for value in nxt.values()))
        exact = energies.copy()
        for bit in range(9):
            for mask in range(512):
                if mask >> bit & 1:
                    exact[mask] -= exact[mask ^ (1 << bit)]
        assert min(exact) >= 0
        yield d, energies, exact

def central_trinomial(n: int) -> int:
    return sum(comb(n, 2*j) * comb(2*j, j) for j in range(n//2 + 1))

def H(d: int) -> int:
    return (central_trinomial(2*d) - 2*comb(2*d, d) + 1)//2

def affine_key(points: tuple[tuple[int, int], ...]):
    """Canonical rational affine-equivalence key, not a numerical hash."""
    if not points:
        return ("empty",)
    if len(points) == 1:
        return ("point",)
    candidates = []
    for o, u, v in permutations(points, 3):
        ax, ay = u[0]-o[0], u[1]-o[1]
        bx, by = v[0]-o[0], v[1]-o[1]
        determinant = ax*by - ay*bx
        if determinant:
            candidates.append(tuple(sorted(
                (F((x-o[0])*by-(y-o[1])*bx, determinant),
                 F(ax*(y-o[1])-ay*(x-o[0]), determinant))
                for x, y in points)))
    if candidates:
        return ("plane", min(candidates))
    for o, u in permutations(points, 2):
        axis = 0 if o[0] != u[0] else 1
        candidates.append(tuple(sorted(F(v[axis]-o[axis], u[axis]-o[axis])
                                       for v in points)))
    return ("line", min(candidates))

# Representative masks for the eight nonempty shape terms and the empty term.
COMPACT = {254:F(1,12), 95:F(1,6), 31:F(-1,2), 124:F(1,8),
           15:F(-1,2), 11:F(7,6), 10:F(-1), 8:F(19,24), 0:F(-1,3)}

MANUSCRIPT_SHAPES = {
    254: ((0,0),(1,0),(-1,0),(0,1),(0,-1),(1,-1),(-1,1)),
    95: ((0,0),(1,0),(0,1),(2,0),(1,1),(0,2)),
    31: ((0,0),(1,0),(0,1),(1,1),(0,2)),
    124: ((0,0),(1,0),(-1,0),(0,1),(0,-1)),
    15: ((0,0),(1,0),(0,1),(0,2)),
    11: ((0,0),(1,0),(0,1)), 10: ((0,0),(1,0)), 8: ((0,0),)
}

def certify_compact(templates: list[dict]) -> list[dict]:
    for mask, points in MANUSCRIPT_SHAPES.items():
        support = tuple(GRID[i] for i in range(9) if mask >> i & 1)
        assert affine_key(points) == affine_key(support)
    coefficients = defaultdict(F)
    for t in templates:
        nu = t['nu']
        if nu < 3:
            continue
        weight = F(nu-2, 2*nu*t['c1']*t['c2'])
        mask = t['mask']
        subset = mask
        while True:
            coefficients[subset] += weight * (-1)**(mask.bit_count()-subset.bit_count())
            if not subset:
                break
            subset = (subset-1) & mask
    grouped = defaultdict(F)
    certificate = []
    for mask, weight in sorted(coefficients.items()):
        if weight:
            points = tuple(GRID[i] for i in range(9) if mask >> i & 1)
            key = affine_key(points)
            grouped[key] += weight
            certificate.append(dict(mask=mask, coefficient=str(weight),
                                    affine_key=repr(key)))
    grouped = {key:value for key,value in grouped.items() if value}
    expected = defaultdict(F)
    for mask, weight in COMPACT.items():
        expected[affine_key(tuple(GRID[i] for i in range(9) if mask >> i & 1))] += weight
    assert grouped == dict(expected), "Universal compact-formula identity failed"
    return certificate

def rational_normals(d: int) -> list[tuple[int, ...]]:
    m = 2*d
    w = (1,)*d + (-1,)*d
    return sorted({v for a in product((-1,0,1), repeat=m) if sum(a) == 0
                   if (v := primitive(tuple(a[i]+a[-1]*w[i]
                                            for i in range(m-1)))) is not None})

def flat_histogram(normals: list[tuple[int, ...]], p: int | None = None) -> dict[int, int]:
    pairs = Counter()
    coordinates = list(combinations(range(len(normals[0])), 2))
    for u, v in combinations(normals, 2):
        if p is None:
            key = primitive(tuple(u[i]*v[j]-u[j]*v[i] for i,j in coordinates))
            assert key is not None
        else:
            rows = [[x % p for x in u], [x % p for x in v]]
            rank = 0
            for col in range(len(u)):
                pivot = next((r for r in range(rank, 2) if rows[r][col]), None)
                if pivot is None:
                    continue
                rows[rank], rows[pivot] = rows[pivot], rows[rank]
                inverse = pow(rows[rank][col], -1, p)
                rows[rank] = [inverse*x % p for x in rows[rank]]
                other = 1-rank
                factor = rows[other][col]
                rows[other] = [(x-factor*y) % p for x,y in zip(rows[other],rows[rank])]
                rank += 1
                if rank == 2:
                    break
            assert rank == 2
            key = tuple(rows[0]+rows[1])
        pairs[key] += 1
    histogram = Counter()
    for number in pairs.values():
        multiplicity = (1+isqrt(1+8*number))//2
        assert comb(multiplicity, 2) == number
        histogram[multiplicity] += 1
    return dict(sorted(histogram.items()))

def width_checks() -> list[dict]:
    output = []
    for p in (5,7,11):
        alphabet = {0,1,p-1}
        for k in range(1,9):
            good = 0
            for values in product(sorted(alphabet), repeat=k+1):
                base = values[0]
                slopes = [(x-base) % p for x in values[1:]]
                image = {base}
                for slope in slopes:
                    image |= {(x+slope) % p for x in image}
                    if not image <= alphabet:
                        break
                if image <= alphabet:
                    good += 1
                    assert sum(bool(x) for x in slopes) <= 2
            assert good == 3+6*k+4*comb(k,2)
            output.append(dict(p=p,k=k,affine_ternary_maps=good))
    return output

def odd_core_checks() -> list[dict]:
    output=[]
    for p in (5,7):
        r=(0,3,1,2)
        w=(1,1,-1,-1)
        constellation={(sum(a*b for a,b in zip(w,u)) % p,
                        sum(a*b*c for a,b,c in zip(w,r,u)) % p)
                       for u in product((0,1),repeat=4)}
        assert len(constellation)==15 and (0,0) in constellation
        assert {((-x)%p,(-y)%p) for x,y in constellation}==constellation
        colors=[z for z in product(range(p),repeat=2) if z not in constellation]
        for k in (1,2,3):
            count=sum(1 for row in product(colors,repeat=k)
                      if all(row[i] != row[j] and row[i] != ((-row[j][0])%p,(-row[j][1])%p)
                             for i in range(k) for j in range(i)))
            expected=prod(p*p-15-2*i for i in range(k))
            assert count==expected
            output.append(dict(p=p,k=k,allowed_paired_tuples=count))
    return output

class SmallField:
    """Base-p representation; only addition and prime-field scalars are needed."""
    def __init__(self,p:int,a:int):
        self.p,self.a,self.q=p,a,p**a
        self.digits=[tuple((n//(p**i))%p for i in range(a)) for n in range(self.q)]
        self.add_table=[[sum(((x+y)%p)*p**i for i,(x,y) in enumerate(zip(self.digits[u],self.digits[v])))
                         for v in range(self.q)] for u in range(self.q)]
        self.scales=[[sum((c*x%p)*p**i for i,x in enumerate(self.digits[u]))
                      for u in range(self.q)] for c in range(p)]
    def linear(self,coefficients,values):
        total=0
        for c,x in zip(coefficients,values):
            total=self.add_table[total][self.scales[c%self.p][x]]
        return total
    def pair_linear(self,coefficients,values):
        return (self.linear(coefficients,[z[0] for z in values]),
                self.linear(coefficients,[z[1] for z in values]))

def small_core_checks() -> list[dict]:
    output=[]
    for p,a in ((2,2),(2,3),(3,2)):
        field=SmallField(p,a)
        q=field.q
        w=(1,1,p-1,p-1)
        r=(1,p,0,field.add_table[1][p])
        balanced=[c for c in product(range(p),repeat=4) if sum(c)%p==0
                  and not any(tuple(t*x%p for x in w)==c for t in range(p))]
        assert all(field.linear(c,r)!=0 for c in balanced)
        constellation=set()
        for t in product(range(p),repeat=4):
            c=[u*v%p for u,v in zip(w,t)]
            constellation.add((sum(c)%p,field.linear(c,r)))
        assert len(constellation)==p**3
        colors=[z for z in product(range(q),repeat=2) if z not in constellation]
        for k in (1,2,3) if p==2 and a==3 else (1,2):
            slopes=[]
            for b in product(range(p),repeat=k):
                if any(b) and next(x for x in b if x)==1:
                    slopes.append(b)
            actual=sum(1 for row in product(colors,repeat=k)
                       if all(field.pair_linear(b,row) not in constellation for b in slopes))
            expected=prod(q*q-p**(3+i) for i in range(k))
            assert actual==expected
            output.append(dict(p=p,a=a,k=k,allowed_paired_tuples=actual))
        regular=0
        for first in product(range(q),repeat=3):
            last=field.linear(w[:3],first) # r4 = r1+r2-r3
            rr=first+(last,)
            regular+=all(field.linear(c,rr)!=0 for c in balanced)
        assert regular==q*(q-1)*(q-p)
        output.append(dict(p=p,a=a,regular_cross_sections=regular))
    return output

def asymptotic_diagnostics() -> list[dict]:
    points=[GRID[i] for i in range(9) if 254>>i&1]
    walk={(0,0):1};output=[]
    for d in range(1,65):
        nxt=defaultdict(int)
        for (x,y),v in walk.items():
            for dx,dy in points:
                nxt[x+dx,y+dy]+=v
        walk=dict(nxt)
        if d in (8,16,32,64):
            energy=sum(v*v for v in walk.values())
            ratio=energy/(49**d)*8*pi*sqrt(3)*d/7
            output.append(dict(d=d,scaled_hexagon_energy=ratio,
                               first_correction=1-5/(24*d)))
    return output

def main() -> None:
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--max-d',type=int,default=10)
    args=parser.parse_args()
    if not __debug__:
        raise SystemExit("Run without -O: exact checks use assertions.")
    if not 4<=args.max_d<=100:
        parser.error('--max-d must lie between 4 and 100')
    DATA.mkdir(exist_ok=True)
    templates=all_templates()
    assert len(templates)==458
    assert Counter(t['nu'] for t in templates)=={2:178,3:128,4:76,6:76}
    certificate=certify_compact(templates)
    results=[]
    for d,energies,exact in walk_energies(args.max_d):
        b2=sum((F(exact[t['mask']],t['nu']*t['c1']*t['c2']) for t in templates),F())
        hist=defaultdict(F)
        for t in templates:
            nu=t['nu']
            hist[nu]+=F(exact[t['mask']],nu*(nu-1)*t['c1']*t['c2'])
        assert b2.denominator==1 and all(x.denominator==1 for x in hist.values())
        defect=sum((coefficient*energies[mask] for mask,coefficient in COMPACT.items()),F())
        assert b2==comb(H(d),2)-defect
        assert sum(comb(nu,2)*count for nu,count in hist.items())==comb(H(d),2)
        results.append(dict(d=d,H=H(d),b2=int(b2),defect=int(defect),
                            flat_multiplicity_histogram={nu:int(count) for nu,count in sorted(hist.items())}))
    independent=[]
    for d in (2,3,4):
        normals=rational_normals(d)
        assert len(normals)==H(d)
        exact_hist=flat_histogram(normals)
        expected={nu:count for nu,count in results[d-1]['flat_multiplicity_histogram'].items() if count}
        assert exact_hist==expected
        for p in (17,53):
            modular_hist=flat_histogram(normals,p)
            assert modular_hist==expected
        independent.append(dict(d=d,normal_count=len(normals),histogram=exact_hist,checked_primes=[17,53]))
        (DATA/f'normals_d{d}.json').write_text(json.dumps(normals,indent=2)+'\n')
    output=dict(status='PASS',arithmetic='exact integers and fractions unless labelled diagnostic',
                template_count=len(templates),template_multiplicities=dict(Counter(t['nu'] for t in templates)),
                compact_universal_identity='PASS over every grid support, grouped by exact rational affine equivalence',
                second_coefficients=results,independent_pair_checks=independent,
                affine_width_checks=width_checks(),odd_core_checks=odd_core_checks(),
                small_characteristic_checks=small_core_checks(),
                asymptotic_diagnostics=asymptotic_diagnostics(),
                boundaries=['No exhaustive count of all arrangements.',
                            'Core-avoidance counts are not full nondegeneracy counts.',
                            'No Lean or other proof-assistant build was run.'])
    (DATA/'verification.json').write_text(json.dumps(output,indent=2)+'\n')
    (DATA/'grid_certificate.json').write_text(json.dumps(dict(grid=GRID,templates=templates,
                        compact_coefficients={str(k):str(v) for k,v in COMPACT.items()},
                        compact_support_certificate=certificate),indent=2)+'\n')
    print(json.dumps(dict(status=output['status'],template_count=len(templates),
                          second_coefficients=results,independent_checks=independent),indent=2))

if __name__=='__main__':
    main()
