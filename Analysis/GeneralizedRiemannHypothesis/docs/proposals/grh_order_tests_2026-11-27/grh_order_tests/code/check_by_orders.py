#!/usr/bin/env python3
"""Finite checks for the proposed weakening of primitive labels.

Pinned source: VladimirReshetnikov/ProveIt,
89d12dd40424f1217fd818d84877b3da52396a3b.

This is independent integer/cyclic-group arithmetic, not a Lean proof or a
verification of the repository's RH/GRH theorem. It uses no external packages.
Elements of F_(q^r)^* are represented by exponents of a primitive generator.
The main counts are checked independently by summing Euler phi(d) over element
orders d dividing q^r-1; small cases also exhaust every exponent and every
allowed scalar. The degree tests are multiplicative orders of q modulo d.
"""

from __future__ import annotations

from fractions import Fraction
from math import gcd
from pathlib import Path
import argparse
import json


COMMIT = "89d12dd40424f1217fd818d84877b3da52396a3b"


def factor(n: int) -> dict[int, int]:
    assert n >= 1
    answer: dict[int, int] = {}
    p = 2
    while p * p <= n:
        while n % p == 0:
            answer[p] = answer.get(p, 0) + 1
            n //= p
        p = 3 if p == 2 else p + 2
    if n > 1:
        answer[n] = answer.get(n, 0) + 1
    return answer


def divisors_from_factorization(factors: dict[int, int]) -> list[int]:
    answer = [1]
    for p, exponent in factors.items():
        answer = [d * p**j for d in answer for j in range(exponent + 1)]
    return sorted(answer)


def totient(n: int) -> int:
    answer = n
    for p in factor(n):
        answer = answer // p * (p - 1)
    return answer


def valuation(n: int, p: int) -> int:
    assert n > 0
    result = 0
    while n % p == 0:
        result += 1
        n //= p
    return result


def is_three_power_at_least_three(r: int) -> bool:
    if r < 3:
        return False
    while r % 3 == 0:
        r //= 3
    return r == 1


def setup(q: int, r: int, N: int) -> tuple[int, int, int, dict[int, int]]:
    assert q >= 2 and len(factor(q)) == 1, "q must be a prime power"
    assert is_three_power_at_least_three(r)
    assert N % 3 == 0 and (q - 1) % (N * N) == 0
    return q**r - 1, (q**r - 1) // (q - 1), q ** (r // 3), factor(N)


def norm_tests(norm_order: int, q: int, N_factors: dict[int, int], mode: str) -> bool:
    """Check norm conditions directly through multiplicative orders."""
    m = q - 1
    if (m // 3) % norm_order == 0:
        return False
    for p, e in N_factors.items():
        if p == 3:
            continue
        if mode == "power":
            # Proposed flagship: y^(m/p^e) != 1.
            if (m // p**e) % norm_order == 0:
                return False
        elif mode == "threshold":
            # Optional larger class: v_p(ord y) > v_p(N).
            if valuation(norm_order, p) <= e:
                return False
        elif mode == "full":
            # Simpler initial version: full p-primary norm for every p | N.
            if (m // p) % norm_order == 0:
                return False
        else:
            raise ValueError(mode)
    return True


def qualifies_order(d: int, q: int, r: int, N: int, mode: str = "power") -> bool:
    M, E, B, N_factors = setup(q, r, N)
    assert M % d == 0
    y_order = d // gcd(d, E)
    return norm_tests(y_order, q, N_factors, mode) and 3 * (B - 1) % d != 0


def density(q: int, N: int, mode: str = "power") -> Fraction:
    answer = Fraction(2, 3)
    for p, e in factor(N).items():
        if p == 3:
            continue
        if mode == "power":
            exponent = e
        elif mode == "threshold":
            exponent = valuation(q - 1, p) - e
        elif mode == "full":
            exponent = 1
        else:
            raise ValueError(mode)
        answer *= 1 - Fraction(1, p**exponent)
    return answer


def degree_of_element_order(q: int, r: int, d: int) -> int:
    """Minimal d0 | r with q^d0 == 1 modulo the element's order d."""
    j = 1
    while j <= r:
        if pow(q, j, d) == 1 % d:
            return j
        j *= 3
    raise AssertionError("element order is inconsistent with the extension")


def check_case(q: int, r: int, N: int, exhaustive: bool = False) -> dict:
    M, E, B, N_factors = setup(q, r, N)
    M_factors = factor(M)
    orders = divisors_from_factorization(M_factors)
    C = B * B + B + 1
    K = C // 3
    assert C % 3 == 0 and C % 9 != 0
    assert gcd(K, q - 1) == 1

    counts = {}
    degree_checks = 0
    power_class_orders = []
    for mode in ("full", "power", "threshold"):
        selected = [d for d in orders if qualifies_order(d, q, r, N, mode)]
        count = sum(totient(d) for d in selected)
        expected = density(q, N, mode) * (M - 3 * (B - 1))
        assert expected.denominator == 1 and count == expected.numerator
        assert count % r == 0
        counts[mode] = {"density": str(density(q, N, mode)),
                        "elements": count, "polynomials": count // r}
        if mode == "power":
            power_class_orders = selected

    assert counts["full"]["elements"] <= counts["power"]["elements"]
    assert counts["power"]["elements"] <= counts["threshold"]["elements"]
    assert qualifies_order(M, q, r, N)
    assert counts["power"]["elements"] >= totient(M)

    for d in power_class_orders:
        y_order = d // gcd(d, E)
        beta_order = d // gcd(d, B - 1)
        assert y_order % N == 0
        assert valuation(y_order, 3) == valuation(q - 1, 3)
        assert beta_order % 3 == 0 and beta_order != 3
        assert valuation(beta_order, 3) == 1
        for p, e in N_factors.items():
            if p != 3:
                assert valuation(y_order, p) >= e + 1
        for ell, multiplicity in factor(d).items():
            for u in range(multiplicity + 2):
                new_order = d // gcd(d, ell**u)
                assert degree_of_element_order(q, r, new_order) == r
                degree_checks += 1

    exponent_checks = scalar_checks = 0
    if exhaustive:
        # Compute predicate directly from powers in C_M, not from the count formula.
        norm_exponents = [(q - 1) // 3] + [
            (q - 1) // p**e for p, e in N_factors.items() if p != 3
        ]

        def good(t: int) -> bool:
            return (all((E * t * v) % M != 0 for v in norm_exponents)
                    and (3 * (B - 1) * t) % M != 0)

        observed_count = 0
        for t in range(M):
            accepted = good(t)
            observed_count += accepted
            exponent_checks += 1
            assert good(q * t % M) == accepted
            for j in range(N):
                assert good((t + j * (M // N)) % M) == accepted
                scalar_checks += 1
        assert observed_count == counts["power"]["elements"]

    return {
        "q": q, "r": r, "N": N, "M_factorization": M_factors,
        "primitive_polynomials": totient(M) // r,
        "counts": counts,
        "element_orders_checked": len(orders),
        "prime_power_degree_checks": degree_checks,
        "exhaustive_exponent_checks": exponent_checks,
        "scalar_invariance_checks": scalar_checks,
    }


def check_boundaries() -> list[dict]:
    result = []
    q, r, N = 19, 3, 3
    M, E, B, fs = setup(q, r, N)
    d = M // gcd(M, 2)
    assert d < M and qualifies_order(d, q, r, N)
    result.append({"case": "strictly_nonprimitive_accepted", "q": q, "r": r,
                   "N": N, "generator_exponent": 2, "order": d})

    t = 127
    d = M // gcd(M, t)
    assert norm_tests(d // gcd(d, E), q, fs, "power")
    assert 3 * (B - 1) % d == 0
    assert degree_of_element_order(q, r, d // gcd(d, 3)) == 1
    result.append({"case": "dropping_root_exclusion_fails", "q": q,
                   "generator_exponent": t, "collapsing_prime": 3})

    t = 27
    d = M // gcd(M, t)
    assert 3 * (B - 1) % d != 0
    assert not norm_tests(d // gcd(d, E), q, fs, "power")
    assert degree_of_element_order(q, r, d // gcd(d, 127)) == 1
    result.append({"case": "dropping_full_three_norm_fails", "q": q,
                   "generator_exponent": t, "collapsing_prime": 127})

    q, r, N = 37, 3, 6
    M, E, B, fs = setup(q, r, N)
    t, shifted = 2, 2 + M // 2
    d, d_shifted = M // gcd(M, t), M // gcd(M, shifted)
    old_norm, new_norm = d // gcd(d, E), d_shifted // gcd(d_shifted, E)
    assert old_norm == 18 and new_norm == 9
    assert old_norm % N == 0 and new_norm % N != 0
    result.append({"case": "norm_divisibility_alone_not_scale_invariant",
                   "q": q, "r": r, "N": N, "generator_exponent": t,
                   "scalar": -1, "old_norm_order": old_norm,
                   "new_norm_order": new_norm})
    return result


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path,
                        default=Path(__file__).with_name("good_label_checks.json"))
    args = parser.parse_args()
    cases = [
        (19, 3, 3, True), (37, 3, 6, True), (64, 3, 3, True),
        (73, 3, 6, False), (163, 3, 9, False), (433, 3, 12, False),
        (577, 3, 12, False), (1297, 3, 36, False), (19, 9, 3, False),
    ]
    checked = [check_case(*case) for case in cases]
    # Concrete repository-shaped norm modulus H^(s+6), with s=0 and H=6.
    uniform_N = 6**6
    uniform_density = density(1 + uniform_N**2, uniform_N)
    assert uniform_density == Fraction(21, 32) and uniform_density >= Fraction(5, 8)
    # Elementary finite telescoping estimate used in the written proof.
    for n in range(2, 10001):
        assert n**6 >= 16 * n * (n - 1)

    answer = {
        "source_commit": COMMIT,
        "status": "all finite checks passed",
        "scope": "cyclic-group arithmetic sanity checks; not a Lean proof",
        "cases": checked,
        "boundary_counterexamples": check_boundaries(),
        "repository_shaped_modulus": {"H": 6, "s": 0, "N": uniform_N,
                                       "density": str(uniform_density)},
        "total_exponent_checks": sum(c["exhaustive_exponent_checks"] for c in checked),
        "total_scalar_checks": sum(c["scalar_invariance_checks"] for c in checked),
        "total_prime_power_degree_checks": sum(c["prime_power_degree_checks"] for c in checked),
    }
    args.output.write_text(json.dumps(answer, indent=2) + "\n")
    print(json.dumps({k: answer[k] for k in (
        "status", "total_exponent_checks", "total_scalar_checks",
        "total_prime_power_degree_checks")}, indent=2))


if __name__ == "__main__":
    main()
