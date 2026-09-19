#!/usr/bin/env python3
"""Reproduce the exact-integer checks and the data files. No third-party packages.

The independent oracle uses a totient chain with a justified large-exponent
lift, not the fixed-modulus iteration whose correctness is proved in the paper.
Finite verification supplements (and does not replace) the proofs.
"""
from __future__ import annotations
import csv
import json
from functools import lru_cache
from pathlib import Path
from time import perf_counter

from tower_digits import (factor, valuation, stable_residue, tetration_mod,
                         difference_residue, predicted_prime_distance,
                         capped_hyper, knuth_mod, local_lambert_residue)

ROOT = Path(__file__).resolve().parents[1]
DATA = ROOT / 'data'


@lru_cache(maxsize=None)
def phi(n: int) -> int:
    out = n
    for p in factor(n):
        out = out // p * (p - 1)
    return out


def cap_power(a: int, n: int, cap: int) -> int:
    x = 1
    for _ in range(n):
        x *= a
        if x >= cap:
            return cap
    return x


@lru_cache(maxsize=None)
def cap_tower(a: int, h: int, cap: int) -> int:
    if cap <= 1:
        return cap
    if h == 0:
        return 1
    threshold, z = 0, 1
    while z < cap:
        threshold += 1
        z *= a
    e = cap_tower(a, h - 1, threshold)
    return cap if e == threshold else a**e


@lru_cache(maxsize=None)
def oracle(a: int, h: int, modulus: int) -> int:
    if modulus == 1:
        return 0
    if h == 0:
        return 1
    period = phi(modulus)
    small = cap_tower(a, h - 1, period)
    if small < period:
        return pow(a, small, modulus)
    e = oracle(a, h - 1, period) + period
    return pow(a, e, modulus)


def main() -> None:
    start = perf_counter()
    counts: dict[str, int] = {}
    def check(group: str, truth: bool) -> None:
        counts[group] = counts.get(group, 0) + 1
        if not truth:
            raise AssertionError(f'{group}: failed check {counts[group]}')

    # Check the independent oracle against actual, manageable integers.
    for a in range(3, 31):
        exacts = [1, a, a**a]
        if a <= 5:
            exacts.append(a ** (a**a))
        for h, exact in enumerate(exacts):
            for modulus in range(1, 101):
                check('oracle_against_exact_integers', oracle(a, h, modulus) == exact % modulus)

    rows = []
    for q in range(4, 202, 2):
        a = q - 1
        for h in range(0, 11):
            for gap in range(1, 4):
                M = q**(h + 1)
                delta = (oracle(a, h + gap, M) - oracle(a, h, M)) % M
                check('universal_leading_difference', delta == (q - 2) * q**h)
                check('optimized_difference', difference_residue(q, h, gap) == q - 2)
                for p in factor(q):
                    v = predicted_prime_distance(q, h, p)
                    P = p**(v + 1)
                    d = (oracle(a, h + gap, P) - oracle(a, h, P)) % P
                    check('exact_prime_valuations', d != 0 and valuation(d, p) == v)
            for m in range(1, 11):
                check('optimized_tower_against_oracle', tetration_mod(q, h, m) == oracle(a, h, q**m))
        for m in range(1, 11):
            r = stable_residue(q, m)
            check('fixed_point', pow(a, r, q**m) == r)
            for j in (0, 1, 7):
                k = r + j * q**m
                check('fixed_point_representatives', pow(a, k, q**m) == k % q**m)
            check('compatibility', m == 1 or r % q**(m-1) == stable_residue(q, m-1))
            if m >= 2:
                check('second_digit', (oracle(a, m, q*q) // q) == q - 2)
                check('third_conjecture_false', oracle(a, m, q**(m+1)) != stable_residue(q, m+1))
            if q <= 20:
                rows.append({'q': q, 'base': a, 'height': m, 'stable_residue': r,
                             'previous_height_mod_q_to_m': oracle(a, m-1, q**m),
                             'new_digit': r // q**(m-1)})

    # Unique finite fixed points, exhaustively checking all representatives.
    for q in range(4, 26, 2):
        for m in range(1, 4):
            M = q**m
            solutions = [x for x in range(M) if pow(q-1, x, M) == x]
            check('exhaustive_unique_fixed_points', solutions == [stable_residue(q,m)])
            counts['fixed_point_candidates_examined'] = counts.get('fixed_point_candidates_examined',0) + M

    # Independently known small hyperoperations and capped threshold logic.
    for a in range(3, 10):
        for rank, n, value in [(1,0,1),(1,1,a),(1,2,a*a),(1,3,a**3),
                               (2,0,1),(2,1,a),(2,2,a**a),
                               (3,0,1),(3,1,a),(4,1,a)]:
            for cap in range(1, 301):
                check('capped_hyper_exact', capped_hyper(a,rank,n,cap) == min(value,cap))
    for q in range(4, 22, 2):
        a = q - 1
        for m in range(1, 21):
            for n in range(0, 5):
                check('rank_two', knuth_mod(q,2,n,m) == oracle(a,n,q**m))
            check('rank_three_at_two', knuth_mod(q,3,2,m) == oracle(a,a,q**m))
            # H3(3)=T[H3(2)], and H3(2)=T[a] is far above 20.
            check('rank_three_at_three', knuth_mod(q,3,3,m) == stable_residue(q,m))
            check('enormous_rank', knuth_mod(q,10**100,2,m) == stable_residue(q,m))

    # Exact rational-series check of the sign-sensitive local Lambert formula.
    lambert_rows = []
    for q in [4,6,8,10,12,14,18,20,30,42]:
        for p in factor(q):
            for K in [3,6,9]:
                r = local_lambert_residue(q,p,K)
                expected = oracle(q-1,K+2,p**K)
                check('local_lambert_series', r == expected)
                lambert_rows.append({'q':q, 'p':p, 'precision':K, 'residue':r})

    DATA.mkdir(exist_ok=True)
    for filename, entries in [('residues.csv',rows), ('local_lambert.csv',lambert_rows)]:
        with (DATA/filename).open('w',newline='') as f:
            w=csv.DictWriter(f,fieldnames=entries[0].keys()); w.writeheader(); w.writerows(entries)
    witness = {'q':4,'n':2,'m':2,'modulus':64,'T_m':27,
               'T_m_plus_1':3**27,'T_m_mod_modulus':27,'T_m_plus_1_mod_modulus':59,
               'difference':3**27-27,'v2_difference':valuation(3**27-27,2)}
    (DATA/'counterexample.json').write_text(json.dumps(witness,indent=2)+'\n')
    report = {'status':'PASS', 'parameters':{'even_q_min':4,'even_q_max':200,
              'height_min':0,'height_max':10,'gaps':[1,2,3],
              'tower_precision_max':10,'unique_fixed_points_q_max':24},
              'counts':counts,
              'assertions_passed':sum(v for k,v in counts.items() if k != 'fixed_point_candidates_examined'),
              'elapsed_seconds':round(perf_counter()-start,3),
              'note':'Finite checks supplement the exact proofs; no floating-point arithmetic is used.'}
    (DATA/'verification.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(report,indent=2))


if __name__ == '__main__':
    main()
