#!/usr/bin/env python3
"""Exact finite checks for fejer-arrangement-selection.tex.

Python >= 3.10, standard library only. These tests supplement, not replace,
the proofs. No floating-point Fourier identities or external CAS are used.
"""
from __future__ import annotations

import argparse
import itertools as it
import json
import math
import random
from fractions import Fraction as F
from pathlib import Path


def kernel_coefficients(length: int) -> dict[int, F]:
    if length < 2:
        raise ValueError("length must be at least two")
    return {j: F(length - abs(j), length * length)
            for j in range(1 - length, length)}


def fejer_masses(s: int, length: int) -> tuple[F, F, F]:
    c = kernel_coefficients(length)
    a = sum((x ** s for x in c.values()), F(0))
    b = c[0] ** s
    return a, b, a / b


def parity(bits: tuple[int, ...]) -> int:
    return (-1) ** sum(bits)


def vertices(k: int, d: int, prime: int, rng: random.Random):
    h = [rng.randrange(1, prime) for _ in range(k)]
    anchors = [[rng.randrange(prime) for _ in range(k)] for _ in range(2*d)]
    r = [rng.randrange(prime) for _ in range(2*d-1)]
    sigma = [1]*d + [-1]*d
    r.append(sum(sigma[j]*r[j] for j in range(2*d-1)) % prime)
    points, signs = [], []
    for j in range(2*d):
        for eps in it.product((0, 1), repeat=k):
            point = tuple((anchors[j][i] + eps[i]*h[i]) % prime for i in range(k))
            points.append(point + (r[j],))
            signs.append(sigma[j]*parity(eps))
    return points, signs


def moment_check() -> int:
    """Constant full-cube polynomial iff parity: all coefficient vectors mod 3.

    h_i=1; coefficients of every nonconstant x-monomial are checked.
    This includes 3^8 coefficient vectors for k=3.
    """
    count = 0
    prime = 3
    for k in (1, 2, 3):
        eps_list = list(it.product((0, 1), repeat=k))
        proper = [a for a in it.product((0, 1), repeat=k) if not all(a)]
        for coeff in it.product(range(prime), repeat=2**k):
            # coefficient of product_{i not in A} x_i equals sum_eta eta eps_A
            constant = all(sum(c * math.prod(e[i] for i in range(k) if a[i])
                               for c, e in zip(coeff, eps_list)) % prime == 0
                           for a in proper)
            is_parity = all(c % prime == coeff[0]*parity(e) % prime
                            for c, e in zip(coeff, eps_list))
            assert constant == is_parity, (k, coeff)
            count += 1
    return count


def coefficient_identity_check(k: int, d: int, length: int, seed: int) -> dict:
    """Exact orthogonality sum for a generic single-feature arrangement."""
    prime = 1000003
    rng = random.Random(seed)
    s = 2*d*2**k
    h = length-1
    c = kernel_coefficients(length)
    all_vectors = list(it.product(range(-h, h+1), repeat=s))
    chosen = None
    for attempt in range(40):
        points, signs = vertices(k, d, prime, rng)
        f = [math.prod(point) % prime for point in points]
        relations = [vec for vec in all_vectors
                     if sum(x*y for x, y in zip(vec, f)) % prime == 0]
        intended = {tuple(j*x for x in signs) for j in range(-h, h+1)}
        if set(relations) == intended:
            chosen = (points, signs, f, relations, attempt+1)
            break
    assert chosen is not None, "Could not find a regular example in 40 attempts"
    points, signs, f, relations, attempts = chosen
    assert len(set(points)) == s
    # Good phi = F; bad phi differs at exactly one distinct vertex.
    good = f[:]
    bad = f[:]
    bad[0] = (bad[0]+1) % prime
    good_mass = F(0)
    bad_mass = F(0)
    for vec in relations:
        weight = math.prod(c[j] for j in vec)
        if sum(j*x for j, x in zip(vec, good)) % prime == 0:
            good_mass += weight
        if sum(j*x for j, x in zip(vec, bad)) % prime == 0:
            bad_mass += weight
    a, b, ratio = fejer_masses(s, length)
    assert good_mass == a and bad_mass == b
    return {"k": k, "d": d, "L": length, "prime": prime,
            "coefficient_vectors_checked": len(all_vectors),
            "attempts": attempts, "points": points, "signs": signs,
            "feature_relations": len(relations),
            "good_mass": str(a), "bad_mass": str(b), "gain": str(ratio)}


def total_count_check() -> int:
    """Every B subset of F_3^2, k=d=1; count labeled arrangements."""
    p = 3
    points = list(it.product(range(p), repeat=2))
    checked = 0
    for mask in range(1 << len(points)):
        bset = {points[j] for j in range(len(points)) if mask & (1 << j)}
        count = 0
        for h, x1, x2, r in it.product(range(p), repeat=4):
            v = [(x1, r), ((x1+h) % p, r), (x2, r), ((x2+h) % p, r)]
            count += all(z in bset for z in v)
        assert count <= len(bset)*p*p
        if len(bset) == p*p:
            assert count == p**4
        checked += 1
    return checked


def exhaustive_exception_check() -> dict:
    """All 625 arrangements over F_5, k=d=1, H=1; verifies regularity logic.

    The conservative exceptional bound is allowed to exceed the universe.
    This test checks the definitions and injectivity, not sharpness.
    """
    p, s, hband = 5, 4, 1
    signs = (1, -1, -1, 1)
    intended = {tuple(j*x for x in signs) for j in (-1, 0, 1)}
    coeffs = list(it.product((-1, 0, 1), repeat=s))
    exceptional = regular = 0
    for h, x1, x2, r in it.product(range(p), repeat=4):
        pts = [(x1, r), ((x1+h) % p, r), (x2, r), ((x2+h) % p, r)]
        features = [(x*y) % p for x, y in pts]
        rels = {c for c in coeffs if sum(x*y for x,y in zip(c,features)) % p == 0}
        assert intended <= rels
        if rels == intended:
            regular += 1
            assert len(set(pts)) == s
        else:
            exceptional += 1
    C = (1+1)*((2*hband+1)**s-(2*hband+1))//2
    assert exceptional <= C*p**3
    return {"arrangements": p**4, "regular": regular,
            "exceptional": exceptional, "upper_bound": C*p**3}


def constant_checks() -> dict:
    n = 0
    for s in (4, 8, 16, 32):
        for length in range(2, 41):
            a, b, ratio = fejer_masses(s, length)
            assert ratio >= F(2*length, s+1)
            assert ratio <= length
            assert a <= ratio**(-(s-1))
            assert sum(kernel_coefficients(length).values()) == 1
            n += 1
    parameter_cases = 0
    for s in (4, 8, 32):
        for alpha, eta in it.product((F(1), F(1,2), F(1,10)), repeat=2):
            x = F(2*(s+1), 1)/(alpha*eta)
            length = (x.numerator+x.denominator-1)//x.denominator
            a, b, ratio = fejer_masses(s, length)
            gamma = alpha**s*eta**(s-1)/(3**(s-1)*(s+1)**s)
            assert ratio >= 4/(alpha*eta)
            assert alpha*a/2 >= gamma
            assert alpha*a-2*b/eta >= alpha*a/2
            assert length <= F(3*(s+1), 1)/(alpha*eta)
            parameter_cases += 1
    return {"kernel_cases": n, "selection_parameter_cases": parameter_cases}


def comparison_table() -> list[dict]:
    rows = []
    alpha = eta = 0.1
    beta = 0.5
    for k in (1, 2, 3, 4):
        d = 8
        s = 2*d*2**k
        old_e = s*2**(s-1)
        neglog_new = -s*math.log10(alpha)-(s-1)*math.log10(eta) \
            +(s-1)*math.log10(3)+s*math.log10(s+1)
        neglog_old = old_e * math.log10(4/(alpha*eta))
        log_threshold = math.log10(k+1)-15*math.log10(beta) \
            + s*math.log10(18*(s+1)**2/(alpha*eta)**2)
        rows.append({"k": k, "s": s, "old_exponent": str(old_e),
                     "minus_log10_old_retention": neglog_old,
                     "minus_log10_new_retention": neglog_new,
                     "log10_new_sufficient_field_size": log_threshold})
    return rows


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=Path("verification-results.json"))
    args = parser.parse_args()
    result = {"status": "PASS", "arithmetic": "exact integers and fractions, except illustrative log table",
              "moment_coefficient_vectors": moment_check(),
              "all_small_subsets": total_count_check(),
              "exception_test": exhaustive_exception_check(),
              "kernel_and_constants": constant_checks(),
              "orthogonality_examples": [coefficient_identity_check(*case) for case in
                    [(1,1,2,712), (1,1,3,713), (2,1,2,714), (1,2,2,715)]],
              "comparison": comparison_table(),
              "scope": "Finite checks supplement the paper's proofs; no Lean formalization is claimed."}
    args.output.write_text(json.dumps(result, indent=2)+"\n", encoding="utf-8")
    print(json.dumps({k:v for k,v in result.items() if k not in ("orthogonality_examples", "comparison")}, indent=2))
    print("Wrote", args.output)


if __name__ == "__main__":
    main()
