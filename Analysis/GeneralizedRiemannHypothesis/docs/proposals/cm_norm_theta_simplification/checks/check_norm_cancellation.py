#!/usr/bin/env python3
"""Exact finite checks for compressed local theta norm cancellation.

This script uses only Python's standard library. It checks finite congruence
models and formal polynomial identities. It does not verify the Lean theorem,
the CM theta integrality theorem, p-adic convergence, or the global RH proof.

Run:
    python3 check_norm_cancellation.py --output checks.json
"""

from __future__ import annotations

import argparse
import json
from fractions import Fraction as Q
from pathlib import Path


D_VALUES = (7, 23, 31, 47, 71, 79, 103, 127)
P_VALUES = (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47)
ODD_PRECISION = 7
TWO_PRECISION = 12


def require(statement: bool, message: str) -> None:
    """Checks remain enabled even if Python is invoked with -O."""
    if not statement:
        raise AssertionError(message)


def is_prime(n: int) -> bool:
    return n >= 2 and all(n % k for k in range(2, int(n**0.5) + 1))


def prime_factors(n: int) -> tuple[int, ...]:
    factors = []
    q = 2
    while q * q <= n:
        if n % q == 0:
            factors.append(q)
            while n % q == 0:
                n //= q
        q += 1
    if n > 1:
        factors.append(n)
    return tuple(factors)


def qmul(x: tuple[int, int], y: tuple[int, int], d: int, modulus: int) -> tuple[int, int]:
    """Multiply in (Z/modulus Z)[w]/(w^2+d)."""
    a, b = x
    c, e = y
    return ((a * c - d * b * e) % modulus, (a * e + b * c) % modulus)


def qpow(x: tuple[int, int], exponent: int, d: int, modulus: int) -> tuple[int, int]:
    value = (1, 0)
    while exponent:
        if exponent & 1:
            value = qmul(value, x, d, modulus)
        x = qmul(x, x, d, modulus)
        exponent >>= 1
    return value


def qnorm(x: tuple[int, int], d: int, modulus: int) -> int:
    return (x[0] ** 2 + d * x[1] ** 2) % modulus


def hensel_norm_minus_one(a: int, b: int, d: int, p: int, precision: int) -> list[dict]:
    """Lift a^2+d*b^2=-1, changing a coordinate with unit derivative."""
    require(p > 2 and d % p != 0, "This lift is for odd unramified primes.")
    require((a * a + d * b * b + 1) % p == 0, "Bad starting norm solution.")
    require(a % p != 0 or b % p != 0, "The norm -1 solution is a unit.")
    records = []
    modulus = p
    for k in range(1, precision + 1):
        require((a * a + d * b * b + 1) % modulus == 0, "Norm lift failed.")
        require(qnorm((a, b), d, modulus) == modulus - 1, "Norm is not -1.")
        records.append({"k": k, "modulus": modulus, "a": a, "b": b})
        if k == precision:
            break
        quotient = (a * a + d * b * b + 1) // modulus
        if a % p:
            correction = (-quotient * pow(2 * a, -1, p)) % p
            a += correction * modulus
        else:
            correction = (-quotient * pow(2 * d * b, -1, p)) % p
            b += correction * modulus
        modulus *= p
    for old, new in zip(records, records[1:]):
        require(new["a"] % old["modulus"] == old["a"], "Incompatible a lift.")
        require(new["b"] % old["modulus"] == old["b"], "Incompatible b lift.")
    return records


def inert_case(d: int, p: int) -> dict:
    """Test both a norm Hensel lift and the exact-order Teichmuller choice."""
    require(p > 2 and pow((-d) % p, (p - 1) // 2, p) == p - 1,
            "The quadratic polynomial must be irreducible mod p.")
    order = 2 * (p + 1)
    divisors = prime_factors(order)
    witness = None
    for a in range(p):
        for b in range(p):
            z = (a, b)
            if qnorm(z, d, p) != p - 1:
                continue
            if qpow(z, order, d, p) == (1, 0) and all(
                qpow(z, order // ell, d, p) != (1, 0) for ell in divisors
            ):
                witness = z
                break
        if witness is not None:
            break
    require(witness is not None, "No order-2(p+1) residue witness found.")
    a, b = witness
    lifts = hensel_norm_minus_one(a, b, d, p, ODD_PRECISION)
    modulus = p**ODD_PRECISION
    # In an unramified quadratic residue ring, repeated p^2-powering strips
    # the principal-unit part. The subsequent exact assertions independently
    # check the properties required by the proposed root-of-unity argument.
    zeta = qpow(witness, p ** (2 * ODD_PRECISION), d, modulus)
    require(qpow(zeta, p * p - 1, d, modulus) == (1, 0), "Teichmuller equation failed.")
    require(qpow(zeta, p + 1, d, modulus) == (modulus - 1, 0), "Norm power is not -1.")
    require(qnorm(zeta, d, modulus) == modulus - 1, "Quadratic norm is not -1.")
    require(qpow(zeta, order, d, modulus) == (1, 0), "Root-of-unity order failed.")
    require(all(qpow(zeta, order // ell, d, modulus) != (1, 0) for ell in divisors),
            "Root has smaller order than required.")
    conjugate = (zeta[0], -zeta[1] % modulus)
    require(qpow(zeta, p, d, modulus) == conjugate, "Frobenius/conjugation mismatch.")
    require((1 + qnorm(zeta, d, modulus)) % modulus == 0, "Two-copy norm sum is not zero.")
    return {"d": d, "p": p, "case": "inert", "order": order,
            "residue_witness": list(witness), "norm_lifts": lifts,
            "teichmuller_at_max_precision": list(zeta)}


def odd_split_roots(d: int, p: int, precision: int) -> list[dict]:
    roots = [r for r in range(1, p) if (r * r + d) % p == 0]
    require(len(roots) == 2, "Expected two distinct roots at an odd split prime.")
    r = roots[0]
    modulus = p
    records = []
    for k in range(1, precision + 1):
        require((r * r + d) % modulus == 0, "Square-root lift failed.")
        records.append({"k": k, "modulus": modulus, "root": r})
        if k < precision:
            correction = (-((r * r + d) // modulus) * pow(2 * r, -1, p)) % p
            r += correction * modulus
            modulus *= p
    return records


def two_adic_split_roots(d: int, precision: int) -> list[dict]:
    require(d % 8 == 7 and precision >= 3, "Expected -d=1 mod 8.")
    # Keep ALL branches: at p=2 the derivative is not invertible, and a
    # greedy root at one finite precision may fail to lift at the next.
    roots = {r for r in range(8) if (r * r + d) % 8 == 0}
    require(len(roots) == 4, "Expected four roots modulo 8.")
    modulus = 8
    for _ in range(3, precision):
        roots = {r + t * modulus for r in roots for t in (0, 1)
                 if ((r + t * modulus) ** 2 + d) % (2 * modulus) == 0}
        modulus *= 2
        require(len(roots) == 4, "Expected four roots at every higher precision.")
    root = min(roots)
    return [{"k": k, "modulus": 2**k, "root": root % (2**k)}
            for k in range(1, precision + 1)]


def split_case(d: int, p: int) -> dict:
    records = two_adic_split_roots(d, TWO_PRECISION) if p == 2 else odd_split_roots(d, p, ODD_PRECISION)
    for row in records:
        r, modulus = row["root"], row["modulus"]
        b = pow(r, -1, modulus)
        # alpha=b*sqrt(-d). At the chosen embedding sqrt(-d)->r,
        # alpha maps to 1; the conjugate embedding maps it to -1.
        require((r * r + d) % modulus == 0, "Not a root of -d.")
        require(b * r % modulus == 1, "Chosen embedding is not 1.")
        require((-b * r) % modulus == modulus - 1, "Conjugate embedding is not -1.")
        require(d * b * b % modulus == modulus - 1, "Norm of b*sqrt(-d) is not -1.")
        require((1 + d * b * b) % modulus == 0, "Two-copy norm cancellation failed.")
        row.update({"b": b, "alpha_coordinates": [0, b], "embedded_alpha": 1,
                    "norm_alpha": modulus - 1})
    for old, new in zip(records, records[1:]):
        require(new["root"] % old["modulus"] == old["root"], "Root branches incompatible.")
        require(new["b"] % old["modulus"] == old["b"], "Inverses incompatible.")
    return {"d": d, "p": p, "case": "split", "root_and_norm_lifts": records}


def ramified_case(d: int) -> dict:
    require(is_prime(d) and d % 8 == 7, "Expected an allowed ramified prime.")
    p = d
    squares = {a * a % p for a in range(1, p)}
    negative_squares = {(-s) % p for s in squares}
    # Norm(a+b*sqrt(-d)) reduces to a^2; a unit has a nonzero residue.
    require(not (squares & negative_squares), "Two nonzero square norms unexpectedly cancel.")
    require(pow(p - 1, (p - 1) // 2, p) == p - 1, "-1 must be a nonsquare.")
    solutions = [(a, b) for a in range(1, p) for b in range(1, p)
                 if (1 + a * a + b * b) % p == 0]
    require(len(solutions) == p + 1, "Wrong number of three-unit cancellation pairs.")
    a, b = solutions[0]
    # Here a and b are rational p-adic scalars, so their CM norms are a^2,b^2.
    lifts = hensel_norm_minus_one(a, b, 1, p, ODD_PRECISION)
    for row in lifts:
        modulus, aa, bb = row["modulus"], row["a"], row["b"]
        require(aa % p != 0 and bb % p != 0, "Three-copy scales must be units.")
        require((1 + aa * aa + bb * bb) % modulus == 0, "Three-copy cancellation failed.")
    return {"d": d, "p": p, "case": "ramified",
            "two_unit_norm_cancellations_mod_p": 0,
            "three_unit_solutions_mod_p": len(solutions), "three_copy_lifts": lifts}


def padd(a: list[Q], b: list[Q]) -> list[Q]:
    return [x + y for x, y in zip(a, b)]


def pscale(a: list[Q], c: Q) -> list[Q]:
    return [c * x for x in a]


def pmul(a: list[Q], b: list[Q]) -> list[Q]:
    size = len(a)
    return [sum((a[k] * b[n - k] for k in range(n + 1)), Q(0)) for n in range(size)]


def pexp(a: list[Q]) -> list[Q]:
    require(a[0] == 0, "Formal exponential expects zero constant coefficient.")
    # Coefficients solve (exp a)'=a' exp a in Q[[z]], truncated exactly.
    output = [Q(1)]
    for n in range(1, len(a)):
        output.append(sum((k * a[k] * output[n - k] for k in range(1, n + 1)), Q(0)) / n)
    return output


def pprod(factors: list[list[Q]], size: int) -> list[Q]:
    output = [Q(1)] + [Q(0)] * (size - 1)
    for factor in factors:
        output = pmul(output, factor)
    return output


def formal_cancellation_checks() -> dict:
    # These are arbitrary formal series, not numerical evaluations of theta.
    # delta and s are separate variables in the general identity; arithmetic
    # membership of actual norm pairs is checked in the finite local models.
    size = 11
    series = [
        [Q(0)] + [Q((-1) ** n, 2 * n + 1) for n in range(1, size)],
        [Q(0) if n % 2 else Q(n + 1, n + 2) for n in range(size)],
    ]
    series[1][0] = Q(0)
    samples = [([Q(1), Q(2)], [Q(1), Q(-1)]),
               ([Q(1), Q(2), Q(3)], [Q(1), Q(4), Q(-5)]),
               ([Q(1), Q(2)], [Q(1), Q(4)])]
    checks = 0
    for g in series:
        for deltas, weights in samples:
            scaled_g = [[coefficient * delta**n for n, coefficient in enumerate(g)] for delta in deltas]
            theta_product = pprod([pexp(pscale(h, Q(-1))) for h in scaled_g], size)
            corrections = [pexp(padd(pscale(g, s), pscale(h, Q(-1))))
                           for s, h in zip(weights, scaled_g)]
            correction_product = pprod(corrections, size)
            expected = pmul(pexp(pscale(g, -sum(weights))), correction_product)
            require(theta_product == expected, "General formal norm-weight identity failed.")
            if sum(weights) == 0:
                require(theta_product == correction_product, "Zero norm-sum did not cancel.")
            else:
                require(theta_product != correction_product, "Nonzero norm-sum test lost its residual.")
            inverse_corrections = [pexp(padd(pscale(g, -s), h))
                                   for s, h in zip(weights, scaled_g)]
            require(pmul(correction_product, pprod(inverse_corrections, size)) == [Q(1)] + [Q(0)] * (size - 1),
                    "Formal unit/inverse identity failed.")
            checks += 1
    return {"formal_series_models": len(series), "parameter_samples": len(samples),
            "coefficient_precision": size - 1, "exact_identity_checks": checks,
            "note": "Formal rational identities only; no claim that arbitrary sample pairs are CM norm pairs."}


def run() -> dict:
    require(all(is_prime(d) and d % 8 == 7 for d in D_VALUES), "Bad discriminant sample.")
    require(all(is_prime(p) for p in P_VALUES), "Bad prime sample.")
    cases = []
    for d in D_VALUES:
        for p in P_VALUES:
            if p == d:
                continue  # Ramified cases are tested once each below, including larger d.
            if p == 2:
                cases.append(split_case(d, p))
            elif pow((-d) % p, (p - 1) // 2, p) == 1:
                cases.append(split_case(d, p))
            else:
                cases.append(inert_case(d, p))
        cases.append(ramified_case(d))
    summary = {kind: sum(row["case"] == kind for row in cases) for kind in ("split", "inert", "ramified")}
    summary["split_at_2"] = sum(row["case"] == "split" and row["p"] == 2 for row in cases)
    summary["total_local_cases"] = len(cases)
    return {
        "status": "PASS",
        "scope": "Exact finite congruence and formal-series sanity checks; not a Lean or p-adic proof.",
        "parameters": {"d": D_VALUES, "unramified_test_primes": P_VALUES,
                       "odd_prime_precision": ODD_PRECISION, "two_adic_precision": TWO_PRECISION},
        "summary": summary, "formal_checks": formal_cancellation_checks(), "local_cases": cases,
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=Path("checks.json"))
    arguments = parser.parse_args()
    results = run()
    arguments.output.write_text(json.dumps(results, indent=2) + "\n", encoding="utf-8")
    print("PASS: exact local norm-cancellation checks")
    print(json.dumps(results["summary"], sort_keys=True))
    print("Odd-prime precision: p^7; split-at-2 precision: 2^12.")
    print("PASS: 6 formal-series identity tests through degree 10, including nonzero-residual controls.")
    print("Scope: finite sanity checks; no Lean replay or p-adic convergence proof is asserted.")
    print(f"Detailed results: {arguments.output}")


if __name__ == "__main__":
    main()
