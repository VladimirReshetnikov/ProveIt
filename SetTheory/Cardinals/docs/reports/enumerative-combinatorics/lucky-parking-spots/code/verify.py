#!/usr/bin/env python3
"""Exact verification and data generation for lucky parking spots.

Python 3.9+; standard library only. All enumerations and formula comparisons use
integers or fractions.Fraction. Decimal is used only for displayed limits.
Run from any directory: python verify.py --output-dir ../data
"""
from __future__ import annotations

import argparse
import csv
import itertools
import json
import platform
import time
from decimal import Decimal, localcontext
from fractions import Fraction as Q
from math import comb, factorial, prod
from pathlib import Path
from typing import List, Tuple

Poly = List[Q]  # ascending powers


def trim(p: Poly) -> Poly:
    while len(p) > 1 and not p[-1]:
        p.pop()
    return p


def add(p: Poly, q: Poly) -> Poly:
    r = [Q(0)] * max(len(p), len(q))
    for i, a in enumerate(p): r[i] += a
    for i, a in enumerate(q): r[i] += a
    return trim(r)


def scale(p: Poly, c: Q) -> Poly:
    return trim([a * c for a in p])


def mul(p: Poly, q: Poly) -> Poly:
    r = [Q(0)] * (len(p) + len(q) - 1)
    for i, a in enumerate(p):
        for k, b in enumerate(q): r[i + k] += a * b
    return trim(r)


def evaluate(p: Poly, n: Q) -> Q:
    result = Q(0)
    for a in reversed(p): result = result * n + a
    return result


def shifted(p: Poly, c: Q) -> Poly:
    """Return the polynomial p(X+c)."""
    r = [Q(0)]
    for a in reversed(p): r = add(mul(r, [c, Q(1)]), [a])
    return r


def f_polynomial(j: int) -> Poly:
    if j < 2: raise ValueError('The polynomial f_j is defined here for j >= 2.')
    # f_j(n) = (1/(2j)) sum_{k=0}^{j-2} binom(n,k) j^k (n-j+1)^(j-2-k).
    result = [Q(0)]
    choose = [Q(1)]
    for k in range(j - 1):
        exponent = j - 2 - k
        power = [Q(comb(exponent, h) * (1-j)**(exponent-h))
                 for h in range(exponent + 1)]
        result = add(result, scale(mul(choose, power), Q(j**k, 2*j)))
        choose = scale(mul(choose, [Q(-k), Q(1)]), Q(1, k+1))
    return trim(result)


def total(n: int) -> int:
    if n < 0: raise ValueError('n must be nonnegative')
    return 1 if n == 0 else (n+1)**(n-1)


def count_formula(n: int, j: int) -> int:
    if not (1 <= j <= n): raise ValueError('Expected 1 <= j <= n.')
    x = n-j+1
    correction = sum(comb(n, k) * j**k * x**(n-1-k) for k in range(j-1))
    result, remainder = divmod((j+1)*total(n)-correction, 2*j)
    if remainder: raise ArithmeticError(('Nonintegral formula', n, j, remainder))
    return result


def triangle_recurrence(max_n: int) -> List[List[int]]:
    """Last-arrival decomposition, independent of the closed binomial formula."""
    p = [total(n) for n in range(max_n+1)]
    rows: List[List[int]] = [[]]
    for n in range(1, max_n+1):
        row = [0]*n
        for a in range(n):
            b = n-1-a
            w = comb(n-1, a)
            for j, value in enumerate(rows[a]):
                row[j] += w*(a+1)*value*p[b]
            for j, value in enumerate(rows[b]):
                row[a+1+j] += w*(a+1)*p[a]*value
            row[a] += w*p[a]*p[b]
        rows.append(row)
    return rows


def brute_preferences(n: int) -> Tuple[int, List[int]]:
    """Simulate every one of the n^n preference lists, rejecting failures."""
    counts = [0]*n
    successful = 0
    full = (1 << n)-1
    for preferences in itertools.product(range(n), repeat=n):
        occupied = 0
        lucky = 0
        for preference in preferences:
            eligible = (full ^ occupied) & ~((1 << preference)-1)
            if not eligible: break
            target_bit = eligible & -eligible
            occupied |= target_bit
            if target_bit == 1 << preference: lucky |= target_bit
        else:
            successful += 1
            while lucky:
                bit = lucky & -lucky
                counts[bit.bit_length()-1] += 1
                lucky ^= bit
    return successful, counts


def direct_state_dp(n: int) -> Tuple[int, List[int]]:
    """Aggregate the direct parking process by its occupied-spot bitmask.

    Each of the n choices of the next preference is processed individually.
    Vector entries count all past successful lucky events at a given spot.
    """
    full = (1 << n)-1
    states = {0: (1, [0]*n)}
    for _ in range(n):
        following = {}
        for occupied, (ways, marks) in states.items():
            for preference in range(n):
                eligible = (full ^ occupied) & ~((1 << preference)-1)
                if not eligible: continue
                bit = eligible & -eligible
                target = occupied | bit
                if target not in following: following[target] = [0, [0]*n]
                value = following[target]
                value[0] += ways
                for j in range(n): value[1][j] += marks[j]
                if bit == 1 << preference: value[1][preference] += ways
        states = following
    return states[full][0], states[full][1]


def outcome_enumeration(n: int) -> Tuple[int, List[int]]:
    counts = [0]*n
    successful = 0
    for sigma in itertools.permutations(range(1, n+1)):
        lengths = []
        for i, label in enumerate(sigma):
            k = i-1
            while k >= 0 and sigma[k] < label: k -= 1
            lengths.append(i-k)
        weight = prod(lengths)
        successful += weight
        for j in range(n): counts[j] += weight // lengths[j]
    return successful, counts


def R_polynomial(j: int) -> Poly:
    return [Q((j-h)*(j-h+1)*j**h, 2*j*j*factorial(h)) for h in range(j)]


def S_convolution(j: int) -> Poly:
    s = scale(R_polynomial(j), Q(-1))
    for a in range(1, j):
        term = [Q(0)]*(a-1) + scale(R_polynomial(j-a), Q(a**(a-1), factorial(a)))
        s = add(s, term)
    return s


def S_closed(j: int) -> Poly:
    if j == 1: return [Q(-1)]
    return ([Q(j**h, 2*j*factorial(h)*(j-h-1)) for h in range(j-1)]
            + [-Q(j**(j-1), j*j*factorial(j-1))])


def limit_data(j: int) -> Tuple[Q, Q, str, str]:
    r = sum((Q(j**k, factorial(k)) for k in range(j-1)), Q(0))/(2*j)
    a = Q(j**(j-1), factorial(j))
    with localcontext() as ctx:
        ctx.prec = 65
        def dec(q: Q) -> Decimal: return Decimal(q.numerator)/Decimal(q.denominator)
        e = (-Decimal(j)).exp()
        left = dec(Q(j+1, 2*j)) - dec(r)*e
        right = dec(Q(j-1, 2*j)) + dec(r+a)*e
        return r, r+a, format(left, '.50f'), format(right, '.50f')


PUBLISHED_FIRST_SIX = {
    1: [1], 2: [3,2], 3: [16,11,9], 4: [125,87,74,64],
    5: [1296,908,783,708,625],
    6: [16807,11824,10266,9421,8733,7776],
    7: [262144,184944,161221,148992,140298,131632],
    8: [4782969,3381341,2955366,2742090,2600879,2480787],
    9: [100000000,70805696,61999923,57671104,54921875,52779840],
    10: [2357947691,1671605646,1465709426,1365730231,1303885965,1258181726]
}
A374533 = [3,11,74,708,8733,131632,2342820,48068672,1116809255]


def run(args: argparse.Namespace) -> dict:
    start = time.perf_counter()
    rows = triangle_recurrence(args.max_n)
    checked = 0
    for n in range(1, args.max_n+1):
        for j, observed in enumerate(rows[n], 1):
            assert count_formula(n, j) == observed, ('closed formula', n, j)
            x = n-j+1
            excess = Q(factorial(n)*j**(j-1)*x**(x-1), factorial(j)*factorial(x))
            assert observed + rows[n][n-j] == total(n)+excess, ('reflection', n, j)
            checked += 1
        assert rows[n][0] == total(n)
        assert rows[n][-1] == n**(n-1)
        assert 2*(n+1)*sum(rows[n]) == n*(n+3)*total(n), ('row sum', n)
        if n >= 2:
            assert 4*rows[n][-2] == (n+1)**(n-1)+(5*n-1)*(n-1)**(n-2)
        if n % 2:
            m = (n+1)//2
            assert Q(rows[n][m-1], total(n)) == Q(1,2)+Q(comb(2*m,m),m*4**m)
    for n, prefix in PUBLISHED_FIRST_SIX.items():
        assert rows[n][:len(prefix)] == prefix, ('published data', n)
    for n, value in enumerate(A374533, 2):
        assert rows[n][-2] == value, ('A374533', n)
    for n in range(1, args.brute_n+1):
        assert brute_preferences(n) == (total(n), rows[n]), ('brute', n)
    for n in range(1, args.dp_n+1):
        assert direct_state_dp(n) == (total(n), rows[n]), ('state DP', n)
    for n in range(1, args.outcome_n+1):
        assert outcome_enumeration(n) == (total(n), rows[n]), ('outcomes', n)
    polys = {}
    for j in range(2, args.poly_j+1):
        p = f_polynomial(j)
        polys[j] = p
        r, _, _, _ = limit_data(j)
        assert len(p) == j-1 and p[-1] == r, ('degree', j)
        centered = shifted(p, Q(j-2,2))
        assert all(not a for k,a in enumerate(centered) if k%2 != (j-2)%2)
        assert S_convolution(j) == S_closed(j), ('convolution lemma', j)
        for n in range(j, args.max_n+1):
            formula = Q(j+1,2*j)*total(n)-evaluate(p,Q(n))*(n-j+1)**(n-j+1)
            assert formula == rows[n][j-1], ('polynomial formula', n, j)
    output = args.output_dir
    output.mkdir(parents=True, exist_ok=True)
    with (output/'triangle.csv').open('w', newline='', encoding='utf-8') as stream:
        writer = csv.writer(stream); writer.writerow(['n','j','C_n_j','parking_functions'])
        for n in range(1,args.max_n+1):
            writer.writerows((n,j,c,total(n)) for j,c in enumerate(rows[n],1))
    with (output/'f_polynomials.json').open('w', encoding='utf-8') as stream:
        json.dump({'variable':'n', 'coefficient_order':'ascending',
                   'polynomials':{str(j):[str(a) for a in p] for j,p in polys.items()}}, stream, indent=2)
        stream.write('\n')
    with (output/'boundary_limits.csv').open('w', newline='', encoding='utf-8') as stream:
        writer=csv.writer(stream); writer.writerow(['j','r_j','r_j_plus_tree_coefficient','rho_j','beta_j_minus_1'])
        for j in range(1, max(50,args.poly_j)+1): writer.writerow((j,*limit_data(j)))
    with (output/'a374533_extension.txt').open('w', encoding='utf-8') as stream:
        stream.write('# Locally generated extension; not an OEIS submission. n C_(n,n-1)\n')
        for n in range(2,args.max_n+1): stream.write(f'{n} {rows[n][-2]}\n')
    result = {
        'status':'PASS', 'python':platform.python_version(),
        'max_n':args.max_n, 'closed_formula_and_reflection_pairs':checked,
        'exhaustive_preference_n':args.brute_n,
        'preference_lists_simulated':sum(n**n for n in range(1,args.brute_n+1)),
        'direct_occupancy_dp_n':args.dp_n,
        'outcome_permutation_n':args.outcome_n,
        'permutations_enumerated':sum(factorial(n) for n in range(1,args.outcome_n+1)),
        'exact_polynomial_and_convolution_max_j':args.poly_j,
        'published_triangle_prefixes_checked':10, 'A374533_terms_checked':9,
        'other_checks':['first and last columns','row sums','next-to-last formula',
                        'odd-size middle column','polynomial parity','leading coefficients'],
        'elapsed_seconds':round(time.perf_counter()-start,3),
        'qualification':'Finite exact checks support the independent mathematical proofs; not a formal proof-assistant verification.'
    }
    (output/'verification.json').write_text(json.dumps(result,indent=2)+'\n', encoding='utf-8')
    return result


def main() -> None:
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--max-n',type=int,default=100)
    parser.add_argument('--poly-j',type=int,default=30)
    parser.add_argument('--brute-n',type=int,default=7)
    parser.add_argument('--dp-n',type=int,default=12)
    parser.add_argument('--outcome-n',type=int,default=8)
    parser.add_argument('--output-dir',type=Path,default=Path(__file__).resolve().parent.parent/'data')
    args=parser.parse_args()
    if min(args.brute_n,args.dp_n,args.outcome_n) < 0 or not 2 <= args.poly_j <= args.max_n:
        parser.error('Require nonnegative enumeration bounds and 2 <= poly-j <= max-n.')
    if args.max_n < max(10,args.brute_n,args.dp_n,args.outcome_n):
        parser.error('max-n must cover all enumeration bounds and the 10 published rows.')
    print(json.dumps(run(args),indent=2))

if __name__ == '__main__': main()
