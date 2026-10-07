#!/usr/bin/env python3
"""Direct exact checks of the repeated-filter expectation theorem.

Run: python code/verify_expectations.py
Dependencies: Python standard library only.

This finite audit computes actual containment probabilities with one Fourier
factor per DISTINCT selected point. It then compares the resulting exact
expectations with the article's general inequalities. In particular, it does
not replace repeated-point probabilities by a product over occurrences.

Attribution: the powered-cosine kernel and positive Fourier weighting already
occur in source 04, Section 4 (R8--R12), of the consolidated ProveIt Ramsey
research report. Source 40 also records one-filter torsion signals. The present
checks concern repeated fixed-degree amplification and its error bounds.

These checks are finite regressions, not a formal proof of the general theorem.
"""
from fractions import Fraction as F
from functools import lru_cache
from itertools import product
from math import comb, gcd
from pathlib import Path
import json


@lru_cache(None)
def coefficient_rows(q, d):
    cs = {n: comb(2*q, q+n) for n in range(-q, q+1)}
    out = []
    for initial in product(range(-q, q+1), repeat=d-1):
        last = -sum(initial)
        if -q <= last <= q:
            row = initial + (last,)
            a = 1
            for n in row:
                a *= cs[n]
            out.append((row, a))
    return out


def bad_repetition_regression():
    """A bad repeated tuple whose actual survival exceeds its formal product."""
    N, H, q = 2, 4, 1
    vertices = (0, 0, 1, 1)
    phi = {0: 0, 1: 1}
    signs = (1, 1, -1, -1)
    domain_discrepancy = sum(e*x for e, x in zip(signs, vertices)) % N
    target_discrepancy = sum(e*phi[x] for e, x in zip(signs, vertices)) % H
    assert domain_discrepancy == 0 and target_discrepancy == 2

    def occurrence_average(points):
        numerator = sum(
            coefficient
            for row, coefficient in coefficient_rows(q, len(points))
            if sum(n*x for n, x in zip(row, points)) % N == 0
            and sum(n*phi[x] for n, x in zip(row, points)) % H == 0
        )
        return F(numerator, (4**q)**len(points))

    actual = occurrence_average(tuple(sorted(set(vertices))))
    formal = occurrence_average(vertices)
    assert actual == F(1, 4)
    assert formal == F(9, 64)
    assert actual > formal
    return {
        "domain_modulus": N,
        "target_modulus": H,
        "subset": [0, 1],
        "map": {"0": 0, "1": 1},
        "tuple": list(vertices),
        "domain_discrepancy": domain_discrepancy,
        "target_discrepancy": target_discrepancy,
        "cosine_degree": q,
        "layers": 1,
        "actual_containment_probability": str(actual),
        "formal_occurrence_product": str(formal),
        "actual_minus_formal": str(actual-formal),
        "interpretation": "The formal occurrence product is smaller than the actual probability of retaining this bad tuple, so it cannot supply the required bad-tuple upper bound."
    }


def one_case(N, H, B, phi, q, k):
    m = 4
    den = 4**q
    b = len(B)
    P = sum(F(comb(2*q, q+n), den)**m for n in range(-q, q+1))
    Q = sum(F(comb(2*q, q+n), den)**m
            for n in range(-q, q+1) if n % 2 == 0)
    R2 = F(comb(4*q, 2*q), 4**(2*q))
    Rm = F(comb(2*q*m, q*m), 4**(q*m))
    tau = max(gcd(N, d) for d in range(1, 2*q+1))
    cache = {}

    def survival(vertices):
        key = tuple(sorted(set(vertices)))
        if key not in cache:
            numerator = 0
            for row, coefficient in coefficient_rows(q, len(key)):
                if (sum(n*x for n, x in zip(row, key)) % N == 0
                        and sum(n*phi[x] for n, x in zip(row, key)) % H == 0):
                    numerator += coefficient
            cache[key] = F(numerator, den**len(key))**k
            assert 0 <= cache[key] <= 1
        return cache[key]

    Bset = set(B)
    good = bad = distinct_bad = repeated_bad = 0
    egood = ebad = edistinct_bad = erepeated_bad = F(0)
    for x, y, z in product(B, repeat=3):
        w = (x+y-z) % N
        if w not in Bset:
            continue
        vertices = (x, y, z, w)
        probability = survival(vertices)
        if (phi[x]+phi[y]-phi[z]-phi[w]) % H == 0:
            good += 1
            egood += probability
        else:
            bad += 1
            ebad += probability
            if len(set(vertices)) == m:
                distinct_bad += 1
                edistinct_bad += probability
            else:
                repeated_bad += 1
                erepeated_bad += probability
    assert egood >= P**k * good
    assert edistinct_bad <= Q**k * distinct_bad + tau*(Rm**k-P**k)*b**(m-2)
    assert erepeated_bad <= comb(m, 2)*R2**k*b**(m-2)
    assert ebad <= Q**k*bad + (tau*(Rm**k-P**k)+comb(m, 2)*R2**k)*b**(m-2)
    needs_extra_relations = edistinct_bad > Q**k * distinct_bad
    return good, bad, repeated_bad, needs_extra_relations


def main():
    count = with_bad = with_repeated_bad = needs_extra_relations = 0
    bad_repetition_example = bad_repetition_regression()
    # A repeated singleton really has one factor, rather than four.
    singleton_actual = F(sum(c for _, c in coefficient_rows(1, 1)), 4)
    singleton_occurrence_product = F(sum(c for _, c in coefficient_rows(1, 4)), 4**4)
    assert singleton_actual == F(1, 2)
    assert singleton_occurrence_product == F(35, 128)
    assert singleton_actual > singleton_occurrence_product
    for N in (2, 3, 4, 5, 6, 8, 9):
        for H in (2, 3, 4, 6):
            for B in (tuple(range(N)), tuple(range(1, N))):
                for mode in range(3):
                    if mode == 0:
                        phi = {x: x*x % H for x in B}
                    elif mode == 1:
                        phi = {x: (x//2) % H for x in B}
                    else:
                        phi = {x: int(x == B[-1]) % H for x in B}
                    for q in (1, 2, 3):
                        for k in (1, 2, 3):
                            g, u, ur, extra = one_case(N, H, B, phi, q, k)
                            count += 1
                            with_bad += int(u > 0)
                            with_repeated_bad += int(ur > 0)
                            needs_extra_relations += int(extra)
    assert with_bad > 0 and with_repeated_bad > 0 and needs_extra_relations > 0
    result = {
        "cases": count,
        "cases_with_bad_tuples": with_bad,
        "cases_with_repeated_bad_tuples": with_repeated_bad,
        "cases_requiring_nonprincipal_correction": needs_extra_relations,
        "inequality_assertions": 4 * count,
        "arithmetic": "fractions.Fraction only",
        "domain_moduli": [2, 3, 4, 5, 6, 8, 9],
        "codomain_moduli": [2, 3, 4, 6],
        "tuple_order": 4,
        "cosine_degrees": [1, 2, 3],
        "layer_counts": [1, 2, 3],
        "subsets": ["full cyclic domain", "domain with zero removed"],
        "maps": ["x squared modulo H", "floor(x/2) modulo H",
                 "indicator of the last element of the subset"],
        "repeated_singleton_regression": {
            "actual_survival": str(singleton_actual),
            "incorrect_occurrence_product": str(singleton_occurrence_product)
        },
        "repeated_bad_tuple_regression": bad_repetition_example,
        "checks": ["good expectation lower bound including repetitions",
                   "distinct bad weighted Fourier error bound",
                   "repeated bad Holder moment bound",
                   "combined bad expectation bound"],
        "scope": "Finite regression checks, not a substitute for the general written proof.",
        "generated_by": "code/verify_expectations.py"
    }
    path = Path(__file__).resolve().parents[1] / "data" / "expectation_checks.json"
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
