#!/usr/bin/env python3
"""Exact finite checks for simultaneous phase integration.

Python 3.10+; standard library only. No floating-point mathematics and no network.
These finite checks supplement, and do not replace, the proofs in article.tex.
"""
from __future__ import annotations
import argparse
from collections import Counter
from functools import lru_cache
from itertools import combinations, product
import json
from pathlib import Path
import time

Matrix = tuple[int, ...]  # rows encoded as bit vectors over F_2

def rank(rows: Matrix) -> int:
    pivots: dict[int, int] = {}
    for row in rows:
        while row:
            p = row.bit_length() - 1
            if p in pivots:
                row ^= pivots[p]
            else:
                pivots[p] = row
                break
    return len(pivots)

def add(a: Matrix, b: Matrix) -> Matrix:
    assert len(a) == len(b)
    return tuple(x ^ y for x, y in zip(a, b))

def alt_matrix(n: int, bits: int) -> Matrix:
    rows = [0] * n
    for k, (i, j) in enumerate(combinations(range(n), 2)):
        if (bits >> k) & 1:
            rows[i] ^= 1 << j
            rows[j] ^= 1 << i
    return tuple(rows)

def bilinear(a: Matrix, u: int, v: int) -> int:
    z = 0
    while u:
        bit = u & -u
        z ^= a[bit.bit_length() - 1]
        u ^= bit
    return (z & v).bit_count() & 1

def restrict(a: Matrix, basis: tuple[int, ...]) -> Matrix:
    return tuple(sum(bilinear(a, u, v) << j for j, v in enumerate(basis))
                 for u in basis)

def poly_mul(a: int, b: int) -> int:
    """Multiply F_2[t] polynomials encoded as bit vectors."""
    out = 0
    while b:
        if b & 1:
            out ^= a
        a <<= 1
        b >>= 1
    return out

@lru_cache(maxsize=None)
def generic_half_rank(a: Matrix, b: Matrix) -> int:
    """Largest nonzero principal Pfaffian over F_2[t], not finite sampling."""
    n = len(a)
    assert len(b) == n
    entries = tuple(tuple(((a[i] >> j) & 1) | (((b[i] >> j) & 1) << 1)
                          for j in range(n)) for i in range(n))
    @lru_cache(maxsize=None)
    def pf(indices: tuple[int, ...]) -> int:
        if not indices:
            return 1
        i, tail = indices[0], indices[1:]
        value = 0
        for k, j in enumerate(tail):
            value ^= poly_mul(entries[i][j], pf(tail[:k] + tail[k+1:]))
        return value
    for r in range(n // 2, 0, -1):
        if any(pf(ids) for ids in combinations(range(n), 2*r)):
            return r
    return 0

def rank_profile(a: Matrix, b: Matrix) -> tuple[int, int, int, int, int]:
    r = generic_half_rank(a, b)
    r0, r1, rp = rank(a)//2, rank(b)//2, rank(add(a, b))//2
    return r, r0, r1, rp, r0 + r1 + rp - 2*r

@lru_cache(maxsize=None)
def subspaces(n: int) -> tuple[tuple[int, ...], ...]:
    """Every subspace once, represented by its unique reduced row-echelon basis."""
    result: list[tuple[int, ...]] = []
    for d in range(n+1):
        for piv in combinations(range(n), d):
            free = [(i, j) for i, p in enumerate(piv)
                    for j in range(p+1, n) if j not in piv]
            for mask in range(1 << len(free)):
                rows = [1 << p for p in piv]
                for k, (i, j) in enumerate(free):
                    if (mask >> k) & 1:
                        rows[i] |= 1 << j
                result.append(tuple(rows))
    return tuple(sorted(result, key=lambda x: (-len(x), x)))

def is_isotropic(a: Matrix, basis: tuple[int, ...]) -> bool:
    return all(not bilinear(a, u, v) for u, v in combinations(basis, 2))

def max_common_isotropic(a: Matrix, b: Matrix) -> tuple[int, ...]:
    return next(w for w in subspaces(len(a))
                if is_isotropic(a, w) and is_isotropic(b, w))

def census_n4() -> dict:
    n = 4
    matrices = tuple(alt_matrix(n, mask) for mask in range(64))
    spaces = subspaces(n)
    assert len(spaces) == 67
    hist: Counter = Counter()
    exact_c = stability = 0
    for a, b in product(matrices, repeat=2):
        r, r0, r1, rp, defect = rank_profile(a, b)
        assert defect >= 0
        assert r <= min(r0+r1, r0+rp, r1+rp, (r0+r1+rp)//2)
        w = max_common_isotropic(a, b)
        assert n-len(w) == r
        exact_c += 1
        eligible = [w for w in spaces if n-len(w) <= defect]
        assert any(rank_profile(restrict(a, w), restrict(b, w))[-1] == 0
                   for w in eligible)
        stability += 1
        hist[str(defect)] += 1
    return dict(pairs=64**2, subspaces=67, exact_codimension_checks=exact_c,
                rank_defect_stability_checks=stability,
                defect_histogram=dict(sorted(hist.items())))

def frontier(k: tuple[int, ...]) -> int:
    """Closed optimal finite-test rank budget, any number >=2 of tests."""
    if len(k) < 2 or min(k) < 0:
        raise ValueError('At least two nonnegative budgets are required.')
    ordered = sorted(k)
    return min(sum(ordered[:j]) // (j-1) for j in range(2, len(k)+1))

def check_frontiers() -> dict:
    checks = 0
    for m, cap in [(2, 7), (3, 7), (4, 4), (5, 3)]:
        for budgets in product(range(cap+1), repeat=m):
            bound = frontier(budgets)
            feasible = [r for r in range(sum(budgets)+1)
                        if sum(max(0, r-k) for k in budgets) <= r]
            assert max(feasible) == bound
            counts = [max(0, bound-k) for k in budgets]
            counts[0] += bound-sum(counts)
            assert sum(counts) == bound and min(counts) >= 0
            assert all(bound-c <= k for c, k in zip(counts, budgets))
            checks += 1
    brute = 0
    for budgets in product(range(7), repeat=3):
        optimum = max(a+b+c for a,b,c in product(range(7), repeat=3)
                      if b+c <= budgets[0] and a+c <= budgets[1]
                      and a+b <= budgets[2])
        assert optimum == frontier(budgets)
        brute += 1
    return dict(finite_test_budget_vectors=checks,
                independent_three_colour_enumerations=brute)

def block_pair(coefficients: list[tuple[int, int]]) -> tuple[Matrix, Matrix]:
    n = 2*len(coefficients)
    a, b = [0]*n, [0]*n
    for j, (s,t) in enumerate(coefficients):
        a[2*j] = s << (2*j+1); a[2*j+1] = s << (2*j)
        b[2*j] = t << (2*j+1); b[2*j+1] = t << (2*j)
    return tuple(a), tuple(b)

def canonical_cubic(a: int, b: int, c: int) -> int:
    ax, ay = a & 1, (a >> 1) & 1
    bx, by = b & 1, (b >> 1) & 1
    cx, cy = c & 1, (c >> 1) & 1
    return (ax*bx*cy + ax*by*cx + ay*bx*cx) & 1

def check_examples() -> dict:
    a, b = block_pair([(1,0),(0,1),(1,1)])
    assert rank_profile(a,b) == (3,2,2,2,0)
    w = (1,4,16)
    assert is_isotropic(a,w) and is_isotropic(b,w)
    # Irreducible polynomial t^2+t+1, C=[[0,1],[1,1]].
    ai = (4,8,1,2)
    bi = (8,12,2,3)
    assert rank_profile(ai,bi) == (2,2,2,2,2)
    hyp = [w for w in subspaces(4) if len(w) == 3]
    assert len(hyp) == 15
    assert all(rank_profile(restrict(ai,w),restrict(bi,w)) == (1,1,1,1,1)
               for w in hyp)
    assert rank_profile(restrict(ai,(1,2)),restrict(bi,(1,2)))[-1] == 0
    # A three-generator obstruction in dimension three.
    forms = [alt_matrix(3,1<<i) for i in range(3)]
    assert all(rank(alt_matrix(3,m)) == 2 for m in range(1,8))
    maxdim = max(len(w) for w in subspaces(3)
                 if all(is_isotropic(a,w) for a in forms))
    assert maxdim == 1
    bias_numerator = sum(1-2*canonical_cubic(a,b,c)
                         for a,b,c in product(range(4),repeat=3))
    assert bias_numerator == 32
    return dict(three_plane_profile=list(rank_profile(a,b)),
                irreducible_profile=list(rank_profile(ai,bi)),
                irreducible_hyperplanes_checked=len(hyp),
                three_generator_common_isotropic_dimension=maxdim,
                canonical_cubic_bias='32/64')

# Exact modular derivatives of a Boolean cubic primitive.
def derivative_values(values: tuple[int, ...], h: int, modulus: int=8) -> tuple[int,...]:
    return tuple((values[x^h]-values[x]) % modulus for x in range(len(values)))

def primitive_values(n: int, coeff: dict[int,int]) -> tuple[int,...]:
    return tuple(sum((1 << (s.bit_count()-1))*v for s,v in coeff.items()
                     if (x & s) == s) % 8 for x in range(1<<n))

def tensor_values(n: int, coeff: dict[int,int], a: int,b: int,c: int) -> int:
    value = 0
    for i,j,k in product(range(n),repeat=3):
        if ((a>>i)&1) and ((b>>j)&1) and ((c>>k)&1):
            value ^= coeff[(1<<i)|(1<<j)|(1<<k)]
    return value

def check_primitives() -> dict:
    n = 3
    count = 0
    fourth_count = 0
    for coeffmask in range(128):
        coeff = {s:(coeffmask>>(s-1))&1 for s in range(1,8)}
        values = primitive_values(n,coeff)
        for a,b,c in product(range(8),repeat=3):
            d3 = derivative_values(derivative_values(derivative_values(values,a),b),c)
            expected = 4*tensor_values(n,coeff,a,b,c)
            assert d3 == (expected,)*8
            count += 8
        # If each cubic derivative is constant, every fourth derivative vanishes.
        # This additional basis check is performed independently by iterating values.
        for hs in product([1,2,4],repeat=4):
            ds = values
            for h in hs:
                ds = derivative_values(ds,h)
            assert ds == (0,)*8
            fourth_count += 8
    return dict(integrable_cubic_tensors=128, third_derivative_point_checks=count,
                fourth_derivative_basis_point_checks=fourth_count)


def direct_sum(pairs: list[tuple[Matrix, Matrix]]) -> tuple[Matrix, Matrix]:
    a: list[int] = []
    b: list[int] = []
    offset = 0
    for ai, bi in pairs:
        a.extend(row << offset for row in ai)
        b.extend(row << offset for row in bi)
        offset += len(ai)
    return tuple(a), tuple(b)

def check_exact_profiles() -> dict:
    count = 0
    # K_1 on three coordinates: e0,e1,f; cross entries s,t.
    singular = ((4,0,1),(0,4,2))
    assert rank_profile(*singular) == (1,1,1,1,1)
    roots = [(0,1),(1,0),(1,1)]
    for profile in product(range(4),repeat=3):
        for r in range(max(profile),sum(profile)//2+1):
            defect = sum(profile)-2*r
            pieces = [singular]*defect
            for root,ri in zip(roots,profile):
                pieces.extend([block_pair([root])]*(r-ri))
            a,b = direct_sum(pieces)
            assert len(a) == sum(profile)
            assert rank_profile(a,b) == (r,*profile,defect)
            count += 1
    return dict(exact_rank_profiles_realized_and_symbolically_checked=count)

def rank_prime(matrix: list[list[int]], p: int) -> int:
    if not matrix:
        return 0
    a = [[x%p for x in row] for row in matrix]
    pivot = 0
    for col in range(len(a[0])):
        row = next((i for i in range(pivot,len(a)) if a[i][col]),None)
        if row is None:
            continue
        a[pivot],a[row] = a[row],a[pivot]
        inv = pow(a[pivot][col],-1,p)
        a[pivot] = [x*inv%p for x in a[pivot]]
        for i in range(len(a)):
            if i != pivot and a[i][col]:
                q = a[i][col]
                a[i] = [(x-q*y)%p for x,y in zip(a[i],a[pivot])]
        pivot += 1
        if pivot == len(a):
            break
    return pivot

def check_prime_examples() -> dict:
    records = []
    for p in (2,3,5,7):
        points = [(1,t) for t in range(p)]+[(0,1)]
        n = 2*len(points)
        a,b = [[0]*n for _ in range(n)],[[0]*n for _ in range(n)]
        for j,(s,t) in enumerate(points):
            # Linear factor t*S-s*T vanishes exactly at the selected point.
            a[2*j][2*j+1] = t
            a[2*j+1][2*j] = -t
            b[2*j][2*j+1] = -s
            b[2*j+1][2*j] = s
        ranks = [rank_prime([[s*x+t*y for x,y in zip(ar,br)]
                             for ar,br in zip(a,b)],p) for s,t in points]
        assert ranks == [2*p]*(p+1)
        records.append(dict(prime=p,dimension=n,
                            generic_rank_from_nonzero_block_product=n,
                            evaluated_ranks=ranks))
    return records

def gaussian_mul(z: tuple[int,int], w: tuple[int,int]) -> tuple[int,int]:
    a,b = z; c,d = w
    return a*c-b*d,a*d+b*c

def gaussian_conj(z: tuple[int,int]) -> tuple[int,int]:
    return z[0],-z[1]

def exact_energy_numerator(values: tuple[tuple[int,int],...],
                           tensor: tuple[int,...]) -> tuple[int,int]:
    # f(x)=values[x]/2; denominator is 256*N^4.
    n = len(values)
    re=im=0
    for a,b,c in product(range(n),repeat=3):
        sign = 1-2*tensor[(a*n+b)*n+c]
        for x in range(n):
            z = (1,0)
            for mask in range(8):
                y = x ^ (a if mask&1 else 0) ^ (b if mask&2 else 0) ^ (c if mask&4 else 0)
                value = values[y]
                if mask.bit_count()%2 == 0:
                    value = gaussian_conj(value)
                z = gaussian_mul(z,value)
            re += sign*z[0]; im += sign*z[1]
    return re,im

def check_energy_bounds() -> dict:
    # All symmetric trilinear tensors on F_2^2, 16 deterministic nonunit inputs each.
    palette = ((0,0),(2,0),(-2,0),(0,2),(0,-2),(1,1),(1,-1),(-1,1))
    test_functions = [tuple(palette[(j*j+3*k*j+k*k+5*k)%len(palette)]
                            for j in range(4)) for k in range(16)]
    # Add independent coordinate patterns to ensure amplitude and phase variety.
    test_functions += [tuple(palette[(mask>>(2*j))&7] for j in range(4))
                       for mask in (0,1,7,19,41,97,193,401)]
    counts = 0
    for mask in range(16):
        coeff = ((mask>>0)&1,(mask>>1)&1,(mask>>2)&1,(mask>>3)&1)
        # Coefficients indexed by number of coordinate-1 entries in a basis triple.
        def t(a:int,b:int,c:int)->int:
            value=0
            for i,j,k in product(range(2),repeat=3):
                if ((a>>i)&1) and ((b>>j)&1) and ((c>>k)&1):
                    value ^= coeff[i+j+k]
            return value
        tensor = tuple(t(a,b,c) for a,b,c in product(range(4),repeat=3))
        half_rank = coeff[1]^coeff[2]
        for values in test_functions:
            energy,imag = exact_energy_numerator(values,tensor)
            assert imag == 0 and energy >= 0
            mass = [z[0]*z[0]+z[1]*z[1] for z in values]
            amplitude = sum(sum(mass[x]*mass[x^w] for x in range(4))**2
                            for w in range(4))
            # E denominator 256*N^4; A denominator 256*N^3.
            assert (1<<half_rank)*energy <= 4*amplitude
            counts += 1
    return dict(nonunit_gaussian_rational_energy_bounds=counts,
                cube_denominator='256*N^4')

def run() -> dict:
    start = time.perf_counter()
    result = dict(status='PASS', arithmetic='exact integers, F_2[t], Z/8Z, Gaussian integers, prime fields',
                  n4=census_n4(), frontiers=check_frontiers(),
                  examples=check_examples(), primitives=check_primitives(),
                  exact_profiles=check_exact_profiles(),
                  prime_examples=check_prime_examples(), energy_bounds=check_energy_bounds())
    result['elapsed_seconds'] = round(time.perf_counter()-start,3)
    return result

def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path,
                        default=Path(__file__).with_name('results.json'))
    args = parser.parse_args()
    result = run()
    args.output.parent.mkdir(parents=True,exist_ok=True)
    args.output.write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
    print(json.dumps(result,indent=2))

if __name__ == '__main__':
    main()
