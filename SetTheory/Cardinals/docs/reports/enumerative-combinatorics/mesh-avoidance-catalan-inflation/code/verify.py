#!/usr/bin/env python3
"""Independent exact checks for the A289587 proof (Python standard library).

The direct mesh test does not use the structural characterization or the GF.
Enumerate all 321-avoiders by inserting each new maximum before an increasing
suffix. Defaults: direct mesh checks through n=12; fast checks through n=13;
series through n=200. No network access, external CAS, or floating point needed.
"""
from __future__ import annotations
import argparse
import csv
import json
import math
import time
from collections import Counter
from pathlib import Path

Perm = tuple[int, ...]
R174 = frozenset({(0, 1), (0, 2), (1, 0), (1, 2), (2, 1)})
R234 = frozenset((y, x) for x, y in R174)
OEIS = [1, 1, 1, 3, 6, 18, 47, 139, 405, 1225, 3740, 11602,
        36357, 115049, 366969, 1178791, 3809802]


def next_level(level: list[Perm]) -> list[Perm]:
    result: list[Perm] = []
    for p in level:
        n = len(p)
        start = n
        while start > 0 and (start == n or p[start-1] < p[start]):
            start -= 1
        for pos in range(start, n+1):
            result.append(p[:pos] + (n+1,) + p[pos:])
    return result


def contains_mesh(p: Perm, shading: frozenset[tuple[int, int]]) -> bool:
    """Literal definition for an underlying 12 mesh pattern."""
    n = len(p)
    for i in range(n):
        for j in range(i+1, n):
            a, b = p[i], p[j]
            if a >= b:
                continue
            blocked = False
            for k, c in enumerate(p):
                if k == i or k == j:
                    continue
                col = 0 if k < i else (1 if k < j else 2)
                row = 0 if c < a else (1 if c < b else 2)
                if (col, row) in shading:
                    blocked = True
                    break
            if not blocked:
                return True
    return False


def mesh_occurrences(p: Perm, shading: frozenset[tuple[int, int]]) -> int:
    total = 0
    for i, a in enumerate(p):
        for j in range(i+1, len(p)):
            b = p[j]
            if a >= b:
                continue
            for k, c in enumerate(p):
                if k == i or k == j:
                    continue
                col = 0 if k < i else (1 if k < j else 2)
                row = 0 if c < a else (1 if c < b else 2)
                if (col, row) in shading:
                    break
            else:
                total += 1
    return total


def fixed_points(p: Perm) -> int:
    return sum(v == i for i, v in enumerate(p, 1))


def excedances(p: Perm) -> int:
    return sum(v > i for i, v in enumerate(p, 1))


def has_upper_bond(p: Perm) -> bool:
    return any(p[i] > i+1 and p[i+1] == p[i]+1 for i in range(len(p)-1))


def inverse(p: Perm) -> Perm:
    q = [0] * len(p)
    for i, v in enumerate(p, 1):
        q[v-1] = i
    return tuple(q)


def contract_core(p: Perm) -> tuple[Perm, tuple[int, ...]]:
    """Contract all maximal upper-successions runs; record their lengths.

    The returned lengths are attached to the excedances of the core in order.
    """
    keep: list[int] = []
    lengths: list[int] = []
    i = 0
    while i < len(p):
        keep.append(p[i])
        j = i+1
        if p[i] > i+1:
            while j < len(p) and p[j] == p[j-1]+1:
                j += 1
            lengths.append(j-i)
        i = j
    rank = {v: i for i, v in enumerate(sorted(keep), 1)}
    return tuple(rank[v] for v in keep), tuple(lengths)


def inflate_core(p: Perm, lengths: tuple[int, ...]) -> Perm:
    if len(lengths) != excedances(p):
        raise ValueError('One inflation length is required per core excedance')
    if any(not isinstance(length, int) or length < 1 for length in lengths):
        raise ValueError('Inflation lengths must be positive integers')
    sizes = [1] * len(p)
    it = iter(lengths)
    for i, v in enumerate(p, 1):
        if v > i:
            sizes[i-1] = next(it)
    try:
        next(it)
        raise ValueError('Too many inflation lengths')
    except StopIteration:
        pass
    size_by_value = {v: sizes[i] for i, v in enumerate(p)}
    starts: dict[int, int] = {}
    cursor = 1
    for v in range(1, len(p)+1):
        starts[v] = cursor
        cursor += size_by_value[v]
    return tuple(w for i, v in enumerate(p)
                 for w in range(starts[v], starts[v]+sizes[i]))


def convolution(a: list[int], b: list[int], N: int) -> list[int]:
    out = [0] * (N+1)
    for i, ai in enumerate(a):
        if not ai:
            continue
        for j in range(min(len(b), N+1-i)):
            out[i+j] += ai*b[j]
    return out


def coeffs(N: int) -> tuple[list[int], list[int], list[int], list[int]]:
    """I=x^2+(x+x^2)I+(1+x)I^2; H=1/(1-I); A=H+xH^2."""
    I = [0] * (N+1)
    for n in range(2, N+1):
        I[n] = int(n == 2) + I[n-1] + I[n-2]
        I[n] += sum(I[j]*I[n-j] for j in range(2, n-1))
        I[n] += sum(I[j]*I[n-1-j] for j in range(2, n-2))
    H = [1] + [0]*N
    B = [1] + [0]*N
    for n in range(1, N+1):
        H[n] = sum(I[j]*H[n-j] for j in range(2, n+1))
        B[n] = B[n-1] + sum(I[j]*B[n-j] for j in range(2, n+1))
    A = H[:]
    for n in range(1, N+1):
        A[n] += sum(H[j]*H[n-1-j] for j in range(n))
    return I, H, B, A


def radical_coeffs(N: int) -> list[int]:
    """Expand the OEIS radical independently using S^2=D and exact division."""
    S = [1] + [0]*(N+1)
    d = [1, -2, -5, -2, 1]
    for n in range(1, N+2):
        numer = (d[n] if n < len(d) else 0) - sum(S[j]*S[n-j] for j in range(1,n))
        assert numer % 2 == 0
        S[n] = numer//2
    p = [3, 10, 11, 4, 1]
    q = [3, 5, 1]
    num = [(p[n] if n < len(p) else 0) - sum(q[j]*S[n-j] for j in range(min(n,2)+1))
           for n in range(N+2)]
    assert num[0] == 0
    a = []
    for n in range(N+1):
        val = num[n+1] - (16*a[n-1] if n >= 1 else 0) - (8*a[n-2] if n >= 2 else 0)
        assert val % 8 == 0
        a.append(val//8)
    return a


def narayana_substitution(N: int) -> list[int]:
    """B(x)=C(x,1/(1+x)); independent finite binomial sums."""
    b = [1]+[0]*N
    for n in range(1,N+1):
        b[n] = 1  # k=0, m=n
        for m in range(2,n+1):
            r = n-m
            for k in range(1,m):
                nar_num = math.comb(m,k)*math.comb(m,k+1)
                assert nar_num % m == 0
                b[n] += (-1)**r * (nar_num//m)*math.comb(k+r-1,r)
    return b


def finite_I(n: int) -> int:
    """Positive binomial-sum formula for [x^n] I, derived in the article."""
    ans = 0
    for j in range((n-2)//2+1):
        cat = math.comb(2*j,j)//(j+1)
        for ell in range(j+1):
            d = n-2*j-2-ell
            if d < 0:
                continue
            for b in range(d//2+1):
                a = d-2*b
                multinomial = math.factorial(2*j+a+b)//(math.factorial(2*j)*math.factorial(a)*math.factorial(b))
                ans += cat*math.comb(j,ell)*multinomial
    return ans


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--direct-n', type=int, default=12)
    parser.add_argument('--fast-n', type=int, default=13)
    parser.add_argument('--series-n', type=int, default=200)
    parser.add_argument('--out', type=Path, default=Path(__file__).resolve().parents[1]/'data')
    args = parser.parse_args()
    if not 0 <= args.direct_n <= args.fast_n <= args.series_n:
        parser.error('Require 0 <= direct-n <= fast-n <= series-n')
    args.out.mkdir(parents=True, exist_ok=True)
    start = time.perf_counter()
    I,H,B,A = coeffs(args.series_n)
    assert A == radical_coeffs(args.series_n)
    assert A[:len(OEIS)] == OEIS[:args.series_n+1]
    assert B[:61] == narayana_substitution(min(60,args.series_n))
    assert all(I[n] == finite_I(n) for n in range(min(45,args.series_n)+1))
    rows = []
    level: list[Perm] = [()]
    for n in range(args.fast_n+1):
        catalan = math.comb(2*n,n)//(n+1)
        assert len(level) == catalan
        fixed_counts: Counter[int] = Counter()
        exc_counts: Counter[int] = Counter()
        structural = direct174 = direct234 = 0
        for p in level:
            exc_counts[excedances(p)] += 1
            no_bond = not has_upper_bond(p)
            if no_bond:
                fixed_counts[fixed_points(p)] += 1
            good = no_bond and fixed_points(p) <= 1
            structural += good
            if n <= args.direct_n:
                g174 = not contains_mesh(p,R174)
                g234 = not contains_mesh(p,R234)
                assert g174 == good, (p, g174, good)
                assert g234 == (not contains_mesh(inverse(p),R174)), p
                direct174 += g174
                direct234 += g234
            if n <= 10:
                core, lengths = contract_core(p)
                assert not has_upper_bond(core), (p,core)
                assert fixed_points(p) == fixed_points(core), (p,core)
                assert excedances(core) == len(lengths), (p,core)
                assert inflate_core(core,lengths) == p, (p,core,lengths)
                occ = math.comb(fixed_points(p),2) + sum(math.comb(ell,2) for ell in lengths)
                assert mesh_occurrences(p,R174) == occ, (p,occ)
        assert structural == A[n]
        assert sum(fixed_counts.values()) == B[n]
        assert fixed_counts[0] == H[n]
        # All fixed-point refinements x^r H^(r+1).
        power = [1]+[0]*n
        for r in range(n+1):
            power = convolution(power,H,n)
            assert fixed_counts[r] == power[n-r], (n,r,fixed_counts[r],power[n-r])
        if n:
            assert exc_counts == {k: math.comb(n,k)*math.comb(n,k+1)//n for k in range(n)}
        if n <= args.direct_n:
            assert direct174 == direct234 == A[n]
        rows.append({'n':n,'catalan_permutations':catalan,'structural_count':structural,
                     'direct_mesh_174':direct174 if n <= args.direct_n else None,
                     'direct_mesh_234':direct234 if n <= args.direct_n else None})
        print(f'n={n:2d}: Catalan={catalan:7d}, A289587={structural:7d}, checked')
        if n < args.fast_n:
            level = next_level(level)
    with (args.out/'coefficients.csv').open('w',newline='') as f:
        writer=csv.writer(f); writer.writerow(['n','A289587','no_upper_bonds','no_upper_bonds_no_fixed_points','indecomposable_nontrivial_core'])
        writer.writerows((n,A[n],B[n],H[n],I[n]) for n in range(args.series_n+1))
    with (args.out/'b289587_extended.txt').open('w') as f:
        f.write('# Computed from the proved recurrence; not an official OEIS b-file.\n')
        f.writelines(f'{n} {a}\n' for n,a in enumerate(A))
    result = {'status':'all checks passed','direct_through':args.direct_n,
              'structural_through':args.fast_n,'series_through':args.series_n,
              'core_roundtrip_through':min(10,args.fast_n),
              'full_occurrence_identity_through':min(10,args.fast_n),
              'narayana_substitution_through':min(60,args.series_n),
              'positive_finite_sum_through':min(45,args.series_n),
              'oeis_terms_matched':min(len(OEIS),args.series_n+1),'seconds':time.perf_counter()-start,
              'enumeration':rows}
    (args.out/'verification_results.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:v for k,v in result.items() if k!='enumeration'},indent=2))

if __name__ == '__main__':
    main()
