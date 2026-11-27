#!/usr/bin/env python3
"""Exact finite checks for cubic-character packet agreement.

No floating-point roots of unity are used.  At each nonzero evaluation point
modulo sign we encode the two independent local multiplicities in base k+1.
The exhaustive search compares local Euler polynomials directly, without using
the valuation or Reed--Muller argument in the proof.
"""
from __future__ import annotations

import argparse
from collections import Counter
from fractions import Fraction
from itertools import combinations_with_replacement, product
import json
import math
from pathlib import Path
import platform
import time

import numpy as np


def vectors(r: int) -> np.ndarray:
    return np.array(list(product(range(3), repeat=r)), dtype=np.int16)


def expected_minimum(r: int, k: int) -> Fraction:
    if k >= 3 ** (r - 1):
        return Fraction(2, 3**r)
    a = 0
    while 3 ** (a + 1) <= k:
        a += 1
    if k < 2 * 3**a:
        return Fraction(2, 3 ** (a + 1))
    return Fraction(4, 3 ** (a + 2))


def classify_minimizer(r: int, k: int, left, right) -> bool:
    """Independently recognize the coset description of an extremizer."""
    xs = vectors(r)
    n = len(xs)
    index = {tuple(x): i for i, x in enumerate(xs)}
    c = np.zeros(n, dtype=np.int16)
    for i in left:
        c[i] += 1
    for i in right:
        c[i] -= 1
    periods = []
    for u in xs:
        perm = [index[tuple((x + u) % 3)] for x in xs]
        if np.array_equal(c, c[perm]):
            periods.append(tuple(u))
    period_set = set(periods)
    if k >= 3 ** (r - 1):
        return len(periods) == 3 ** (r - 1) and int(c.sum()) == 0
    a = 0
    while 3 ** (a + 1) <= k:
        a += 1
    if len(periods) != 3**a or not np.all(np.abs(c) <= 1):
        return False
    positive = [tuple(x) for x in xs[c == 1]]
    negative = [tuple(x) for x in xs[c == -1]]
    if k < 2 * 3**a:
        return len(positive) == len(negative) == 3**a
    if len(positive) != 2 * 3**a or len(negative) != 2 * 3**a:
        return False
    def quotient_reps(points):
        out = []
        for x in points:
            if all(tuple((np.array(x)-np.array(y)) % 3) not in period_set for y in out):
                out.append(x)
        return out
    ps, ns = quotient_reps(positive), quotient_reps(negative)
    if len(ps) != 2 or len(ns) != 2:
        return False
    center_difference = tuple((np.array(ps).sum(axis=0)-np.array(ns).sum(axis=0)) % 3)
    return center_difference in period_set


def exhaustive(r: int, k: int, classify_limit: int = 500) -> dict:
    start = time.monotonic()
    xs = vectors(r)
    reps = np.array([x for x in xs if next((int(y) for y in x if y), 0) == 1])
    dots = (xs @ reps.T) % 3
    symbols = (dots == 0).astype(np.int16) + (k+1)*(dots == 1).astype(np.int16)
    packets = np.array(list(combinations_with_replacement(range(len(xs)), k)), dtype=np.int16)
    signatures = symbols[packets].sum(axis=1, dtype=np.int32)
    assert len({tuple(x) for x in signatures}) == len(packets)
    wanted = int(expected_minimum(r, k) * 3**r / 2)
    histogram = np.zeros(len(reps)+1, dtype=np.int64)
    found = len(reps)+1
    witnesses = []
    # Each unordered pair is inspected exactly once.  Projective representatives
    # suffice because equality at -v is the conjugate of equality at v.
    for i in range(len(packets)-1):
        distances = np.count_nonzero(signatures[i+1:] != signatures[i], axis=1)
        histogram += np.bincount(distances, minlength=len(reps)+1)
        local = int(distances.min())
        found = min(found, local)
        if len(witnesses) < classify_limit:
            hits = np.flatnonzero(distances == wanted)
            for offset in hits[:classify_limit-len(witnesses)]:
                j = i + 1 + int(offset)
                assert classify_minimizer(r, k, packets[i], packets[j])
                witnesses.append((i, j))
    assert found == wanted, (r, k, found, wanted)
    total_pairs = math.comb(len(packets), 2)
    assert int(histogram.sum()) == total_pairs
    assert histogram[0] == 0
    i, j = witnesses[0]
    return {
        "rank": r, "packet_size": k, "packets": len(packets),
        "unordered_pairs": total_pairs,
        "minimum_disagreement_density": str(Fraction(2*found, 3**r)),
        "maximal_agreement_density": str(1-Fraction(2*found, 3**r)),
        "extremal_pairs": int(histogram[wanted]),
        "extremal_pairs_checked_against_structure": len(witnesses),
        "witness_A": [xs[v].tolist() for v in packets[i]],
        "witness_C": [xs[v].tolist() for v in packets[j]],
        "distance_histogram_projective": {str(d): int(n) for d, n in enumerate(histogram) if n},
        "seconds": round(time.monotonic()-start, 3),
    }


def divide_pi(a: int, b: int):
    # (u+v*zeta)*(1-zeta)=(u+v)+(-u+2v)*zeta.
    if (a+b) % 3:
        return None
    return ((2*a-b)//3, (a+b)//3)


def valuation(a: int, b: int) -> int:
    assert a or b
    t = 0
    while (q := divide_pi(a, b)) is not None:
        a, b = q
        t += 1
    return t


def valuation_checks(bound: int = 300) -> dict:
    minima = {}
    checked = 0
    for c0 in range(-bound, bound+1):
        for c1 in range(-bound, bound+1):
            c2 = -c0-c1
            if max(abs(c0), abs(c1), abs(c2)) > bound or (c0 == c1 == c2 == 0):
                continue
            t = valuation(c0-c2, c1-c2)
            mass = max(abs(c0), abs(c1), abs(c2))
            lower = 3**((t-1)//2) if t % 2 else 2*3**(t//2-1)
            assert mass >= lower
            minima[t] = min(minima.get(t, mass), mass)
            checked += 1
    for t, mass in minima.items():
        expected = 3**((t-1)//2) if t % 2 else 2*3**(t//2-1)
        assert mass == expected
    return {"local_mass_bound": bound, "nonzero_triples": checked,
            "observed_exact_minimum_mass_by_valuation": minima}


def construction_checks(max_rank: int = 6) -> dict:
    results = []
    for r in range(1, max_rank+1):
        xs = vectors(r)
        dots = (xs @ xs.T) % 3
        for a in range(r):
            U = [i for i, x in enumerate(xs) if not x[a:].any()]
            # Two parallel cosets, with a direction not in U.
            p = Counter(U)
            index = {tuple(x): i for i, x in enumerate(xs)}
            theta = np.zeros(r, dtype=np.int16); theta[a] = 1
            n = Counter(index[tuple((xs[i]+theta) % 3)] for i in U)
            families = [("two_cosets", p, n, Fraction(2, 3**(a+1)), Fraction(4,3))]
            if a+1 < r:
                alpha = theta.copy()
                beta = np.zeros(r, dtype=np.int16); beta[a+1] = 1
                p = Counter(index[tuple((xs[i]+sgn*alpha) % 3)] for i in U for sgn in [1,-1])
                n = Counter(index[tuple((xs[i]+sgn*beta) % 3)] for i in U for sgn in [1,-1])
                families.append(("four_cosets", p, n, Fraction(4,3**(a+2)), Fraction(16,9)))
            for kind, pp, nn, target, norm_target in families:
                c = np.array([pp[i]-nn[i] for i in range(len(xs))], dtype=np.int64)
                H0 = c @ (dots == 0); H1 = c @ (dots == 1); H2 = c @ (dots == 2)
                mask = (H0 != H2) | (H1 != H2)
                density = Fraction(int(mask.sum()), len(xs))
                assert density == target
                # The support is inversion-invariant, so its transform is real;
                # every integer numerator is C0-C1 with C1=C2.
                cc0 = (dots == 0) @ mask.astype(np.int64)
                cc1 = (dots == 1) @ mask.astype(np.int64)
                cc2 = (dots == 2) @ mask.astype(np.int64)
                assert np.array_equal(cc1, cc2)
                norm = Fraction(int(np.abs(cc0-cc1).sum()), len(xs))
                assert norm == norm_target
                results.append({"rank": r, "subspace_dimension": a, "kind": kind,
                                "reduced_packet_size": int(c[c>0].sum()),
                                "disagreement_density": str(density), "fourier_algebra_norm": str(norm)})
    return {"cases": len(results), "results": results}


def prime_example(limit: int = 200000) -> dict:
    # Independent cubic characters at 7,13,19; common modulus 1729.
    moduli = [7, 13, 19]
    primitive_roots = [3, 2, 2]
    tables = []
    for q, g in zip(moduli, primitive_roots):
        vals = {}
        z = 1
        for e in range(q-1):
            assert z not in vals
            vals[z] = e % 3
            z = z*g % q
        assert len(vals) == q-1 and z == 1
        tables.append(vals)
    # a=1, alpha=(0,1,0), beta=(0,0,1), U=<e1>.
    A = [(j,sgn,0) for j in range(3) for sgn in [1,2]]
    C = [(j,0,sgn) for j in range(3) for sgn in [1,2]]
    def disagree(v):
        a = Counter(sum(x*y for x,y in zip(u,v)) % 3 for u in A)
        c = Counter(sum(x*y for x,y in zip(u,v)) % 3 for u in C)
        return a != c
    unit_classes = []
    bad_classes = []
    Q = math.prod(moduli)
    for u in range(1,Q):
        if math.gcd(u,Q) == 1:
            v = tuple(T[u % q] for T,q in zip(tables,moduli))
            unit_classes.append(u)
            if disagree(v):
                bad_classes.append(u)
    assert Fraction(len(bad_classes),len(unit_classes)) == Fraction(4,27)
    sieve = bytearray(b'\x01')*(limit+1)
    sieve[0:2] = b'\x00\x00'
    for p in range(2,math.isqrt(limit)+1):
        if sieve[p]:
            sieve[p*p::p] = b'\x00'*(((limit-p*p)//p)+1)
    eligible, bad = [], []
    badset = set(bad_classes)
    for p in range(2,limit+1):
        if sieve[p] and Q % p:
            eligible.append(p)
            if p % Q in badset:
                bad.append(p)
    return {"modulus": Q, "character_moduli": moduli, "primitive_roots": primitive_roots,
            "packet_A_exponents": A, "packet_C_exponents": C,
            "reduced_classes": len(unit_classes), "disagreeing_classes": len(bad_classes),
            "exact_disagreement_density": "4/27", "exact_agreement_density": "23/27",
            "disagreeing_residue_classes": bad_classes, "prime_cutoff": limit,
            "eligible_primes": len(eligible), "disagreeing_primes": len(bad),
            "first_distinguishing_primes": bad[:20]}


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--output', type=Path, default=Path(__file__).resolve().parents[1]/'results'/'cubic_checks.json')
    parser.add_argument('--quick', action='store_true', help='smaller exhaustive search')
    args = parser.parse_args()
    cases = [(1,k) for k in range(1,9)] + [(2,k) for k in range(1,7)] + [(3,k) for k in range(1,4)] + [(4,k) for k in range(1,3)]
    if args.quick:
        cases = [(1,1),(1,3),(2,1),(2,2),(2,3),(3,2)]
    rows = []
    for r,k in cases:
        row = exhaustive(r,k)
        rows.append(row)
        print(f'r={r} k={k}: {row["unordered_pairs"]:,} pairs, delta={row["minimum_disagreement_density"]}', flush=True)
    result = {"method": "exact local-multiplicity comparison of every unordered pair of multisets",
              "python": platform.python_version(), "numpy": np.__version__,
              "exhaustive_cases": rows,
              "total_unordered_pairs": sum(x['unordered_pairs'] for x in rows),
              "structural_extremizers_checked": sum(x['extremal_pairs_checked_against_structure'] for x in rows),
              "valuation_checks": valuation_checks(),
              "construction_checks": construction_checks(),
              "prime_example": prime_example(),
              "all_checks_passed": True}
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2)+'\n')
    print(f'PASS: {result["total_unordered_pairs"]:,} exhaustive comparisons; saved {args.output}', flush=True)


if __name__ == '__main__':
    main()
