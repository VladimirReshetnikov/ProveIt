#!/usr/bin/env python3
"""Exact cyclic-group checks for robust finite-field labels.

This program checks finite instances; it is not a proof of the uniform theorem.
If F_{q^r}^* = <g> has order N=q^r-1, it represents g^k by k mod N.
Subfield membership, Frobenius degree, order, norm, and scalar scaling are then
computed by exact integer arithmetic, without constructing a finite-field model.
"""

from __future__ import annotations

import argparse
import json
import math
import random
from fractions import Fraction
from pathlib import Path


def factor(n: int) -> dict[int, int]:
    assert n >= 1
    out: dict[int, int] = {}
    p = 2
    while p * p <= n:
        while n % p == 0:
            out[p] = out.get(p, 0) + 1
            n //= p
        p = 3 if p == 2 else p + 2
    if n > 1:
        out[n] = out.get(n, 0) + 1
    return out


def phi(n: int) -> int:
    value = n
    for p in factor(n):
        value = value // p * (p - 1)
    return value


def is_prime_power(q: int) -> bool:
    return q > 1 and len(factor(q)) == 1


def three_power_degrees(r: int) -> list[int]:
    assert r >= 3
    values = [1]
    while values[-1] < r:
        values.append(values[-1] * 3)
    assert values[-1] == r
    return values


def frobenius_degree(q: int, r: int, k: int) -> int:
    """Least d | r with (g^k)^(q^d)=g^k, independently of the label test."""
    n = q**r - 1
    order = n // math.gcd(k, n)
    for d in three_power_degrees(r):
        if pow(q, d, order) == 1 % order:
            return d
    raise AssertionError("Frobenius did not close")


def run_case(q: int, r: int, m: int, exhaustive: bool,
             selection_modulus: int | None = None) -> dict:
    assert is_prime_power(q)
    assert q % 3 == 1 and m % 3 == 0
    assert (q - 1) % (m * m) == 0
    selection = m if selection_modulus is None else selection_modulus
    assert selection % 3 == 0 and m % selection == 0
    degrees = three_power_degrees(r)
    n, a = q**r - 1, q ** (r // 3)
    h = 3 * (a - 1)
    k_index = n // h
    assert n % h == 0
    assert k_index == (a * a + a + 1) // 3
    assert math.gcd(k_index, m) == 1
    assert math.gcd(k_index, selection) == 1
    assert h % m == 0 and (n // m) % m == 0
    n_factors = factor(n)
    coefficient_primes = list(n_factors)
    # A prime outside n has no primary part to remove; include one example.
    outside = 2
    while outside in n_factors or factor(outside) != {outside: 1}:
        outside += 1
    coefficient_primes.append(outside)
    removers = {ell: ell ** n_factors.get(ell, 0) for ell in coefficient_primes}

    if exhaustive:
        exponents = range(n)
    else:
        rng = random.Random(20261127 + q + r + m)
        selected = set(range(min(512, n)))
        for landmark in (k_index, n // m, n // 3, h, n - 1):
            for shift in range(-2 * m, 2 * m + 1):
                selected.add((landmark + shift) % n)
        for multiplier in range(1, 64):
            selected.add((multiplier * k_index) % n)
        selected.update(rng.randrange(n) for _ in range(4096))
        exponents = sorted(selected)

    checked, admissible, primitive_norm, nonprimitive_norm = 0, 0, 0, 0
    beyond_conservative, beyond_examples = 0, []
    removal_checks, scaling_checks = 0, 0
    examples = []
    norm_part = 1
    for prime, valuation in factor(q - 1).items():
        if selection % prime == 0:
            norm_part *= prime**valuation
    for exponent in exponents:
        checked += 1
        in_h = (3 * exponent * (a - 1)) % n == 0
        assert in_h == (exponent % k_index == 0)
        good = math.gcd(exponent, selection) == 1 and not in_h
        if not good:
            continue
        admissible += 1
        norm_order = (q - 1) // math.gcd(exponent, q - 1)
        assert norm_order % norm_part == 0
        if selection == m:
            assert norm_order % (m * m) == 0
        primitive_norm += norm_order == q - 1
        nonprimitive_norm += norm_order != q - 1
        assert frobenius_degree(q, r, exponent) == r
        for ell, remover in removers.items():
            # Raising to ell^v_ell(n) removes the entire ell-primary order.
            # All intermediate powers then retain degree r as well.
            assert frobenius_degree(q, r, (exponent * remover) % n) == r
            removal_checks += 1
        for t in range(m):
            scaled = (exponent + t * (n // m)) % n
            assert math.gcd(scaled, selection) == 1
            assert (3 * scaled * (a - 1)) % n != 0
            assert frobenius_degree(q, r, scaled) == r
            scaling_checks += 1
        if len(examples) < 3 and norm_order != q - 1:
            examples.append({"exponent": exponent, "element_order": n // math.gcd(exponent, n),
                             "norm_order": norm_order})
        if math.gcd(exponent, m) != 1:
            beyond_conservative += 1
            if len(beyond_examples) < 3:
                beyond_examples.append({"exponent": exponent,
                                        "gcd_with_scalar_modulus": math.gcd(exponent, m),
                                        "element_order": n // math.gcd(exponent, n),
                                        "norm_order": norm_order})

    expected = Fraction(phi(selection), selection) * (q**r - 3 * a + 2)
    assert expected.denominator == 1
    expected = int(expected)
    assert expected % r == 0
    if exhaustive:
        assert admissible == expected
    return {
        "q": q, "r": r, "M": m, "selection_modulus": selection, "group_order": n,
        "group_order_factorization": n_factors, "H_order": h, "H_index": k_index,
        "gcd_H_index_M": math.gcd(k_index, m), "frobenius_degrees_checked": degrees,
        "mode": "exhaustive" if exhaustive else "deterministic_sample",
        "exponents_checked": checked, "admissible_exponents_checked": admissible,
        "expected_admissible_elements": expected, "expected_irreducible_labels": expected // r,
        "exact_count_verified_by_enumeration": exhaustive,
        "full_primary_removal_checks": removal_checks,
        "scalar_scaling_checks": scaling_checks,
        "primitive_norm_examples_checked": primitive_norm,
        "nonprimitive_norm_examples_checked": nonprimitive_norm,
        "nonprimitive_norm_examples": examples,
        "norm_primary_part_guaranteed": norm_part,
        "beyond_conservative_checked": beyond_conservative,
        "beyond_conservative_examples": beyond_examples,
        "status": "pass",
    }


def counterexamples() -> dict:
    # q=19, r=3: N=6858=2*3^3*127, H has order 54, index 127.
    q, r = 19, 3
    n = q**r - 1
    exponent = 127
    assert (q - 1) // math.gcd(exponent, q - 1) == q - 1
    assert frobenius_degree(q, r, exponent) == r
    removed = (exponent * 27) % n
    assert frobenius_degree(q, r, removed) == 1
    primitive_norm_only = {
        "q": q, "r": r, "exponent": exponent, "element_order": n // math.gcd(exponent, n),
        "norm_order": 18, "degree_before": 3, "coefficient_prime": 3,
        "primary_removal_power": 27, "degree_after": 1,
        "reason": "Norm primitive and irreducible, but inside H; the 3-primary part carries the extension degree.",
    }
    exponent = 54
    assert n // math.gcd(exponent, n) == 127
    assert frobenius_degree(q, r, exponent) == 3
    assert frobenius_degree(q, r, (exponent * 127) % n) == 1
    irreducible_only = {
        "q": q, "r": r, "exponent": exponent, "element_order": 127,
        "norm_order": 1, "degree_before": 3, "coefficient_prime": 127,
        "degree_after": 1,
        "reason": "Irreducibility alone permits a single primary component to carry the whole orbit.",
    }
    # With M|q-1 but not M^2|q-1, even scalar stability can fail.
    q, r, m = 7, 3, 6
    n = q**r - 1
    exponent, scaled = 1, 1 + n // m
    assert math.gcd(exponent, m) == 1
    assert math.gcd(scaled, m) != 1
    assert (q - 1) % m == 0 and (q - 1) % (m * m) != 0
    weak_modulus = {
        "q": q, "r": r, "M": m, "exponent": exponent, "scaled_exponent": scaled,
        "gcd_before": 1, "gcd_after": math.gcd(scaled, m),
        "scalar_order": m,
        "reason": "M divides q-1 alone does not ensure stability under all M-torsion scalars or norm order divisible by M^2.",
    }
    return {"primitive_norm_only": primitive_norm_only, "irreducible_only": irreducible_only,
            "weakened_modulus_hypothesis": weak_modulus}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path,
                        default=Path(__file__).with_name("robust_labels_results.json"))
    args = parser.parse_args()
    cases = [(19, 3, 3, True), (37, 3, 6, True), (73, 3, 6, True),
             (109, 3, 6, True), (64, 3, 3, True), (19, 9, 3, False),
             (37, 9, 6, False), (433, 3, 12, False), (1801, 3, 15, False)]
    results = [run_case(*case) for case in cases]
    data = {
        "description": "Exact cyclic-group checks for robust finite-field labels",
        "scope": "Finite verification only; not a proof of the uniform theorem or a Lean kernel check.",
        "hypotheses": "q prime power, q=1 mod3, r=3^a with a>=1, 3|M, M^2|q-1",
        "criterion": "For z=g^k, gcd(k,M)=1 and z^3 not in F_(q^(r/3))^*",
        "count": "phi(M)/M * (q^r - 3*q^(r/3) + 2)",
        "cases": results,
        "counterexamples": counterexamples(),
        "total_exponents_checked": sum(x["exponents_checked"] for x in results),
        "total_primary_removal_checks": sum(x["full_primary_removal_checks"] for x in results),
        "total_scalar_scaling_checks": sum(x["scalar_scaling_checks"] for x in results),
        "status": "all checks passed",
    }
    args.output.write_text(json.dumps(data, indent=2) + "\n")
    print(json.dumps({k: data[k] for k in ("status", "total_exponents_checked",
                                          "total_primary_removal_checks", "total_scalar_scaling_checks")}, indent=2))
    print("Results written to", args.output)


if __name__ == "__main__":
    main()
