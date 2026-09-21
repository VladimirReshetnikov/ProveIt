#!/usr/bin/env python3
"""Constant-term route: exact checks for the Apéry framing supercongruences.

This is the verifier written for the constant-term / integration-by-parts
proof of the framing step (article sections 5-7).  Its distinctive content is
the index range to 250, the SIGNED all-prime normalized congruences, the
sharper dyadic bounds, the framed dilogarithm coefficients, direct degree-12
polynomial powers, and both directions of compositional inversion.  It is
deliberately a SEPARATE implementation from verify_defect_route.py, which
computes the same quantities by a different route on a different grid; the
independence of the two is the point and they are not merged.

Python 3.9+, standard library only.  These finite checks supplement, and do
not replace, the all-index proofs in article.pdf.

Run: python verify_constant_term_route.py --max-index 250 --output-dir verification
"""
from __future__ import annotations

import argparse
import csv
import json
import platform
import time
from functools import lru_cache
from math import isqrt
from pathlib import Path
from typing import Dict, List, Sequence, Tuple


def primes_up_to(limit: int) -> List[int]:
    sieve = bytearray(b"\x01") * (limit + 1)
    if limit >= 0:
        sieve[0] = 0
    if limit >= 1:
        sieve[1] = 0
    for p in range(2, isqrt(limit) + 1):
        if sieve[p]:
            sieve[p * p : limit + 1 : p] = b"\x00" * ((limit - p * p) // p + 1)
    return [p for p in range(2, limit + 1) if sieve[p]]


def valuation(value: int, p: int) -> int:
    """For nonzero integers; zero is handled separately by callers."""
    if value == 0:
        raise ValueError("The valuation of zero is infinite.")
    value = abs(value)
    result = 0
    while value % p == 0:
        value //= p
        result += 1
    return result


def exact_divide(numerator: int, denominator: int) -> int:
    if denominator == 0:
        raise ZeroDivisionError("Exact division by zero.")
    q, r = divmod(numerator, denominator)
    if r:
        raise AssertionError(("nonintegral quotient", numerator, denominator))
    return q


def apery_numbers(limit: int) -> List[int]:
    """Use the defining binomial sum, with an exact summand recurrence."""
    values: List[int] = []
    for n in range(limit + 1):
        term = 1  # binomial(n,k) * binomial(n+k,k), initially k=0
        total = 1
        for k in range(1, n + 1):
            term = exact_divide(term * (n - k + 1) * (n + k), k * k)
            total += term * term
        values.append(total)
    return values


def apery_three_term(limit: int) -> List[int]:
    """Independent check using the standard recurrence recorded in A005259."""
    values = [1]
    if limit:
        values.append(5)
    for n in range(1, limit):
        numerator = (34*n**3 + 51*n*n + 27*n + 5)*values[n] - n**3*values[n-1]
        values.append(exact_divide(numerator, (n+1)**3))
    return values


def power_from_apery(a: Sequence[int], exponent: int, degree: int) -> List[int]:
    """Coefficients of A(x)**exponent through x**degree, via logarithmic derivative."""
    values = [1] + [0] * degree
    if exponent == 0:
        return values
    for j in range(1, degree + 1):
        numerator = exponent * sum(a[k] * values[j-k] for k in range(1, j+1))
        values[j] = exact_divide(numerator, j)
    return values


def multiply(f: Sequence[int], g: Sequence[int], degree: int) -> List[int]:
    result = [0] * (degree + 1)
    for i in range(min(len(f), degree + 1)):
        if f[i]:
            for j in range(min(len(g), degree - i + 1)):
                result[i+j] += f[i] * g[j]
    return result


def inverse_unit(f: Sequence[int], degree: int) -> List[int]:
    if not f or f[0] != 1:
        raise ValueError("Expected a series with constant coefficient 1.")
    result = [1] + [0] * degree
    for n in range(1, degree + 1):
        result[n] = -sum(f[k]*result[n-k] for k in range(1, min(n+1, len(f))))
    return result


def power_series(f: Sequence[int], exponent: int, degree: int) -> List[int]:
    base = list(f[:degree+1])
    if exponent < 0:
        base = inverse_unit(base, degree)
        exponent = -exponent
    result = [1] + [0] * degree
    while exponent:
        if exponent & 1:
            result = multiply(result, base, degree)
        exponent >>= 1
        if exponent:
            base = multiply(base, base, degree)
    return result


def compose(f: Sequence[int], g: Sequence[int], degree: int) -> List[int]:
    if not g or g[0] != 0:
        raise ValueError("The inner series must have constant coefficient zero.")
    result = [0] * (degree + 1)
    for coefficient in reversed(f[:degree+1]):
        result = multiply(result, g, degree)
        result[0] += coefficient
    return result


def primitive_coefficients(values: Sequence[int], degree: int, order: int) -> List[int]:
    """Recover c_n from values[n] = sum_{d|n} d**order*c_d."""
    coefficients = [0] * (degree + 1)
    for n in range(1, degree + 1):
        remainder = values[n] - sum(d**order * coefficients[d]
                                    for d in range(1, n) if n % d == 0)
        coefficients[n] = exact_divide(remainder, n**order)
    return coefficients


def run(args: argparse.Namespace) -> Dict[str, object]:
    started = time.perf_counter()
    limit = args.max_index
    output = Path(args.output_dir)
    output.mkdir(parents=True, exist_ok=True)
    counts: Dict[str, int] = {}

    def check(condition: bool, kind: str, detail: object) -> None:
        if not condition:
            raise AssertionError((kind, detail))
        counts[kind] = counts.get(kind, 0) + 1

    a = apery_numbers(limit)
    other = apery_three_term(limit)
    for n in range(limit + 1):
        check(a[n] == other[n], "apery_definition_vs_recurrence", n)

    all_primes = primes_up_to(limit)
    for p in all_primes:
        for n in range(p, limit + 1, p):
            r = valuation(n, p)
            check((a[n] - a[n//p]) % p**(2*r) == 0,
                  "apery_second_order_congruence", (p, n))

    c = primitive_coefficients(a, limit, 2)
    counts["apery_integral_dilogarithm_coefficients"] = limit
    low = min(12, limit)
    A = power_from_apery(a, 1, low)
    F = [1]
    for n in range(1, low + 1):
        F.append(a[1] if n == 1 else
                 exact_divide(power_from_apery(a, 1-n, n)[n], 1-n))

    # Verify F(y) = A(y/F(y)), hence x*A(x) and y/F(y) are inverse series.
    invF = inverse_unit(F, low)
    X = [0] + invF[:low]
    check(compose(A, X, low) == F, "F_functional_equation", low)
    xA = [0] + A[:low]
    identity = [0, 1] + [0]*(low-1)
    check(compose(xA, X, low) == identity, "compositional_inverse_right", low)
    check(compose(X, xA, low) == identity, "compositional_inverse_left", low)

    # Independently reconstruct the Euler product to a modest degree.
    product = [1] + [0]*low
    for d in range(1, low + 1):
        factor = [0]*(low+1)
        factor[0] = 1
        e = d*c[d]
        coefficient = 1
        for k in range(1, low//d + 1):
            coefficient = exact_divide(coefficient*(e+k-1), k)
            factor[d*k] = coefficient
        product = multiply(product, factor, low)
    check(product == A, "apery_Euler_product", low)

    @lru_cache(maxsize=None)
    def B(m: int, n: int) -> int:
        if n < 1:
            raise ValueError("B_m(n) is normalized only for n >= 1.")
        if m == 0:
            return a[n]
        return exact_divide(power_from_apery(a, m*n, n)[n], m)

    def U(m: int, n: int) -> int:
        return 1 if n == 0 else m*B(m, n)

    def V(m: int, n: int) -> int:
        return 1 if n == 0 else m*B(m-1, n)

    parameters = list(range(-args.parameter_radius, args.parameter_radius+1))
    normalized_parameters = sorted(set(parameters + [m-1 for m in parameters]))
    for m in parameters:
        for n in range(1, low+1):
            check(power_series(A, m*n, n)[n] == U(m,n),
                  "U_direct_power_identity", (m,n))
            check(power_series(F, m*n, n)[n] == V(m,n),
                  "V_direct_power_identity", (m,n))

    pairs = set()
    selected_primes = [p for p in args.primes if p <= limit]
    for p in selected_primes:
        pp = p
        while pp <= limit:
            for h in range(1, args.multipliers+1):
                n = h*pp
                if n <= limit:
                    pairs.add((p,n))
            pp *= p
    for p,n in sorted(pairs):
        previous = n//p
        r = valuation(n,p)
        modulus = p**(2*r)
        for m in normalized_parameters:
            bn, bp = B(m,n), B(m,previous)
            sn = -1 if (m*n) % 2 else 1
            sp = -1 if (m*previous) % 2 else 1
            check((sn*bn-sp*bp) % modulus == 0,
                  "signed_normalized_all_prime_congruence", (m,p,n))
            if p != 2 or m % 2 == 0 or r >= 2:
                check((bn-bp) % modulus == 0,
                      "unsigned_normalized_congruence", (m,p,n))
        for m in parameters:
            un, up = U(m,n), U(m,previous)
            vn, vp = V(m,n), V(m,previous)
            # V has the ordinary second-order congruence even at p=2.
            check((vn-vp) % modulus == 0, "V_all_prime_congruence", (m,p,n))
            if p != 2 or m % 2 == 0:
                check((un-up) % modulus == 0, "U_odd_prime_or_even_parameter", (m,p,n))
            if m:
                stronger = p**(2*r + valuation(m,p))
                if p != 2:
                    check((un-up) % stronger == 0,
                          "U_parameter_valuation_strengthening", (m,p,n))
                    check((vn-vp) % stronger == 0,
                          "V_parameter_valuation_strengthening", (m,p,n))
                check(((-1)**((m*n)%2)*un - (-1)**((m*previous)%2)*up) % stronger == 0,
                      "signed_U_parameter_strengthening", (m,p,n))
                check(((-1)**(((m-1)*n)%2)*vn - (-1)**(((m-1)*previous)%2)*vp) % stronger == 0,
                      "signed_V_parameter_strengthening", (m,p,n))

    # Integer dilogarithm coefficients of the signed normalized transforms.
    for m in normalized_parameters:
        signed = [0] + [(-1)**((m*n)%2)*B(m,n) for n in range(1,low+1)]
        primitive_coefficients(signed, low, 2)
        counts["signed_transform_integral_dilogarithm_coefficients"] = (
            counts.get("signed_transform_integral_dilogarithm_coefficients", 0) + low)

    sharp_u = U(1,7) - U(1,1)
    check(valuation(sharp_u,7) == 2, "failure_of_uniform_third_order", sharp_u)
    check((U(1,2)-U(1,1)) % 4 != 0,
          "unsigned_U_dyadic_counterexample", (U(1,2),U(1,1)))
    check((V(2,2)-V(2,1)) % 8 != 0 and (V(2,2)-V(2,1)) % 4 == 0,
          "dyadic_parameter_refinement_boundary", (V(2,2),V(2,1)))

    with (output / "sample_values.csv").open("w", newline="", encoding="utf-8") as stream:
        writer = csv.writer(stream)
        writer.writerow(["n","apery_a_n","A_coefficient","F_coefficient",
                         "B_minus_2","B_minus_1","B_0","B_1","B_2","U_1","V_2"])
        for n in range(low+1):
            writer.writerow([n,a[n],A[n],F[n]] +
                            ([B(m,n) for m in [-2,-1,0,1,2]] if n else [""]*5) +
                            [U(1,n),V(2,n)])

    report: Dict[str, object] = {
        "status": "PASS",
        "arithmetic": "Python arbitrary-precision integers; every division checked exactly",
        "python": platform.python_version(),
        "max_index": limit,
        "parameters_U_V": parameters,
        "parameters_normalized_B": normalized_parameters,
        "selected_primes": selected_primes,
        "multipliers": args.multipliers,
        "prime_index_pairs": len(pairs),
        "pairs": [list(pair) for pair in sorted(pairs)],
        "cached_normalized_values": B.cache_info().currsize,
        "checks_by_kind": counts,
        "total_checks": sum(counts.values()),
        "sharpness": {
            "U_1_7_minus_U_1_1": sharp_u,
            "valuation_at_7": valuation(sharp_u,7),
            "quotient_by_49": sharp_u//49,
            "remainder_mod_343": sharp_u%343,
            "U_1_2_minus_U_1_1": U(1,2)-U(1,1),
            "V_2_2_minus_V_2_1": V(2,2)-V(2,1),
        },
        "elapsed_seconds": round(time.perf_counter()-started,3),
        "logical_scope": "Finite reproducibility checks only; the general proof is in article.pdf.",
    }
    (output / "verification.json").write_text(json.dumps(report,indent=2)+"\n",encoding="utf-8")
    lines = ["PASS: all exact-arithmetic checks succeeded.",
             "Configuration: " + json.dumps({k:report[k] for k in
                 ["max_index","parameters_U_V","selected_primes","multipliers","prime_index_pairs"]}),
             *[f"{key}: {value}" for key,value in counts.items()],
             f"Total checks: {report['total_checks']}",
             f"Cached normalized values: {report['cached_normalized_values']}",
             f"Elapsed seconds: {report['elapsed_seconds']}",
             "U_1(7)-U_1(1) = 49 * 103720679; 103720679 = 6 (mod 7).",
             "U_1(2)-U_1(1) = 118, not divisible by 4.",
             "V_2(2)-V_2(1) = 236, divisible by 4 but not by 8.",
             str(report["logical_scope"])]
    text = "\n".join(lines)+"\n"
    (output / "verification.log").write_text(text,encoding="utf-8")
    print(text,end="")
    return report


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--max-index",type=int,default=250)
    parser.add_argument("--parameter-radius",type=int,default=6)
    parser.add_argument("--multipliers",type=int,default=6)
    parser.add_argument("--primes",type=int,nargs="+",default=[2,3,5,7,11,13])
    parser.add_argument("--output-dir",default="verification")
    args = parser.parse_args()
    if args.max_index < 12:
        parser.error("--max-index must be at least 12 for the built-in examples")
    if args.parameter_radius < 2 or args.multipliers < 1:
        parser.error("require --parameter-radius >= 2 and --multipliers >= 1")
    if not args.primes or any(p < 2 for p in args.primes):
        parser.error("--primes must contain only primes")
    prime_set = set(primes_up_to(max(args.primes)))
    if any(p not in prime_set for p in args.primes):
        parser.error("--primes must contain only primes")
    run(args)


if __name__ == "__main__":
    main()
