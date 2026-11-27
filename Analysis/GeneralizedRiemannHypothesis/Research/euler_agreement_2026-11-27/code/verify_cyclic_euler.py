#!/usr/bin/env python3
"""Exact finite checks for cyclic Euler-packet matching.

Uses only the Python standard library.  All packet comparisons and Fourier
calculations are exact; there is no floating-point arithmetic.  Exhaustion
checks every unordered pair of multisets in each stated (E,k) case.  These
finite checks supplement, and do not replace, the general proof.

Run: python3 verify_cyclic_euler.py > cyclic_euler_verification.json
"""

from collections import Counter
from fractions import Fraction
from functools import lru_cache
from itertools import combinations, combinations_with_replacement, product
from math import comb, gcd, prod
import json


def prime_factors(n):
    result = []
    d = 2
    while d * d <= n:
        if n % d == 0:
            result.append(d)
            while n % d == 0:
                n //= d
        d += 1
    if n > 1:
        result.append(n)
    return result


def predicted(E, k):
    ps = prime_factors(E)
    t = min(len(ps), (2 * k).bit_length() - 1)
    return t, prod((Fraction(p - 1, p) for p in ps[:t]), start=Fraction(1))


def density(E, A, C):
    disagree = [v for v in range(E)
                if sorted(v * x % E for x in A)
                != sorted(v * x % E for x in C)]
    return Fraction(len(disagree), E), disagree


def exhaustive_packets(E, k):
    packets = list(combinations_with_replacement(range(E), k))
    # Unit evaluations are injective, and hence distinguish every distinct
    # pair.  Check every remaining evaluation directly as a root histogram.
    unit_count = sum(gcd(v, E) == 1 for v in range(E))
    nonunits = [v for v in range(1, E) if gcd(v, E) != 1]
    signatures = [tuple(tuple(sorted(v * x % E for x in A)) for v in nonunits)
                  for A in packets]
    spectrum = Counter()
    best = E + 1
    witness = None
    for i, s in enumerate(signatures):
        for j in range(i):
            h = unit_count + sum(a != b for a, b in zip(s, signatures[j]))
            spectrum[h] += 1
            if h < best:
                best = h
                witness = [list(packets[j]), list(packets[i])]
    t, bound = predicted(E, k)
    assert Fraction(best, E) == bound, (E, k, best, bound)
    assert sum(spectrum.values()) == comb(len(packets), 2)
    assert density(E, *witness)[0] == bound
    return {
        "E": E, "k": k, "t": t, "packet_count": len(packets),
        "pairs_checked": comb(len(packets), 2),
        "minimum_disagreement": str(Fraction(best, E)),
        "predicted_minimum": str(bound), "witness": witness,
        "distance_spectrum": {str(Fraction(h, E)): count
                              for h, count in sorted(spectrum.items())},
    }


def parity_box(E, k):
    t, bound = predicted(E, k)
    steps = [E // p for p in prime_factors(E)[:t]]
    A, C = [], []
    for mask in range(1 << t):
        x = sum(h for i, h in enumerate(steps) if mask >> i & 1) % E
        (A if mask.bit_count() % 2 == 0 else C).append(x)
    assert len(set(A + C)) == 1 << t
    assert len(A) == len(C) == 1 << (t - 1)
    padding = [0] * (k - len(A))
    A += padding
    C += padding
    actual, dis = density(E, A, C)
    expected_dis = [v for v in range(E)
                    if all(v % p for p in prime_factors(E)[:t])]
    assert dis == expected_dis and actual == bound
    return {"E": E, "k": k, "A": sorted(A), "C": sorted(C),
            "minimum_disagreement": str(actual), "disagreement_evaluations": dis}


def marginal_checks(shape, values):
    coords = list(product(*(range(n) for n in shape)))
    masks = sorted(range(1 << len(shape)), key=int.bit_count)
    checked = 0
    equality = 0
    for c in product(values, repeat=len(coords)):
        if not any(c) or sum(c):
            continue
        norm = sum(abs(z) for z in c)
        r = None
        for mask in masks:
            marginal = Counter()
            for x, z in zip(coords, c):
                if z:
                    marginal[tuple(v for i, v in enumerate(x) if mask >> i & 1)] += z
            if any(marginal.values()):
                r = mask.bit_count()
                break
        assert r is not None and norm >= 1 << r, (shape, c, r)
        checked += 1
        equality += norm == 1 << r
    return {"shape": shape, "coefficient_values": values,
            "balanced_nonzero_arrays_checked": checked,
            "equality_arrays": equality}


def trim(poly):
    while len(poly) > 1 and poly[-1] == 0:
        poly.pop()
    return poly


def monic_division(numerator, denominator):
    n = list(numerator)
    d = list(denominator)
    assert d[-1] == 1
    q = [0] * max(1, len(n) - len(d) + 1)
    for i in range(len(n) - len(d), -1, -1):
        a = n[i + len(d) - 1]
        q[i] = a
        if a:
            for j, b in enumerate(d):
                n[i + j] -= a * b
    return trim(q), trim(n[:len(d) - 1] or [0])


@lru_cache(None)
def cyclotomic(n):
    p = [-1] + [0] * (n - 1) + [1]
    for d in range(1, n):
        if n % d == 0:
            p, rem = monic_division(p, cyclotomic(d))
            assert rem == [0]
    return tuple(p)


def exact_cylinder_fourier(E, selected):
    # Direct DFT in Q[zeta_E], via polynomial reduction modulo Phi_E.
    # It independently checks the factored Fourier-norm expression.
    phi = cyclotomic(E)
    points = [v for v in range(E) if all(v % p for p in selected)]
    coeffs = []
    for x in range(E):
        poly = [0] * E
        for v in points:
            poly[-x * v % E] += 1
        _, rem = monic_division(poly, phi)
        assert len(rem) == 1, (E, selected, x, rem)
        coeffs.append(Fraction(rem[0], E))
    mean = Fraction(len(points), E)
    norm = sum(abs(a) for a in coeffs)
    expected = (1 << len(selected)) * mean
    assert coeffs[0] == mean and norm == expected
    assert sum(coeffs) == 0
    return {"E": E, "selected_primes": list(selected), "mean": str(mean),
            "exact_fourier_norm": str(norm), "predicted_norm": str(expected),
            "nonzero_fourier_coefficients": sum(bool(x) for x in coeffs),
            "method": "integer polynomial DFT reduced modulo cyclotomic polynomial"}


def arithmetic_example():
    E, Q, generator = 30, 31, 3
    A = [2, 18, 23, 27]
    C = [3, 8, 12, 17]
    residues = [pow(generator, v, Q) for v in range(E)]
    assert len(set(residues)) == E
    actual, ds = density(E, A, C)
    assert actual == Fraction(4, 15)
    assert ds == [v for v in range(E) if gcd(v, E) == 1]
    bad_residues = sorted(residues[v] for v in ds)
    assert all(0 < x < E for x in A + C)
    limit = 100000
    sieve = bytearray(b"\x01") * (limit + 1)
    sieve[:2] = b"\x00\x00"
    for p in range(2, int(limit ** 0.5) + 1):
        if sieve[p]:
            sieve[p * p:limit + 1:p] = b"\x00" * ((limit - p * p) // p + 1)
    primes = [p for p in range(2, limit + 1) if sieve[p] and p != Q]
    bad_primes = [p for p in primes if p % Q in bad_residues]
    return {"Q": Q, "E": E, "primitive_root": generator,
            "A_exponents": A, "C_exponents": C,
            "all_factors_primitive_conductor_31": True,
            "disagreement_density": str(actual), "agreement_density": "11/15",
            "disagreement_residue_classes": bad_residues,
            "first_distinguishing_primes": bad_primes[:20],
            "illustrative_prime_count_bound": limit,
            "unramified_primes_counted": len(primes),
            "distinguishing_primes_counted": len(bad_primes)}


def main():
    cases = [(E, k) for E in range(2, 17) for k in range(1, 4)]
    cases += [(E, 2) for E in (18, 20, 24, 30)]
    cases += [(E, 4) for E in (6, 8, 10, 12)]
    exhaustive = [exhaustive_packets(E, k) for E, k in cases]
    constructions = [parity_box(E, k) for E in (4, 6, 12, 30, 60, 210, 420)
                     for k in (1, 2, 3, 4, 7, 8, 9)]
    marginals = [marginal_checks(shape, values) for shape, values in (
        ((2, 2), (-2, -1, 0, 1, 2)),
        ((2, 3), (-2, -1, 0, 1, 2)),
        ((2, 2, 2), (-1, 0, 1)),
    )]
    fourier = []
    for E in (4, 8, 9, 12, 18, 30, 60, 210):
        ps = prime_factors(E)
        for r in range(1, len(ps) + 1):
            for selected in combinations(ps, r):
                fourier.append(exact_cylinder_fourier(E, selected))
    output = {
        "status": "all exact checks passed",
        "arithmetic": "integer and fractions.Fraction; no approximate comparisons",
        "exhaustive_case_count": len(exhaustive),
        "total_packet_pairs_checked": sum(x["pairs_checked"] for x in exhaustive),
        "exhaustive_packet_cases": exhaustive,
        "extremal_construction_checks": constructions,
        "marginal_lemma_checks": marginals,
        "fourier_norm_checks": fourier,
        "primitive_conductor_example": arithmetic_example(),
        "scope": "Finite exact checks supplement the proof; no GRH numerical validation claimed.",
    }
    print(json.dumps(output, indent=2))


if __name__ == "__main__":
    main()
