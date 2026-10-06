#!/usr/bin/env python3
"""First possible p-adic residue for the second lacunary iterate.

Let F_p(x) = sum_{j >= 0} x**(p**j), let a_2(n) = [x**n] F_p(F_p(x)),
and write n = sum_i d_i p**i.  When n >= 1 and n == 1 (mod p-1), put
w = (sum_i d_i - 1)/(p-1).  This module evaluates the proven formula

  a_2(n)/p**w = (-1)**w / prod_i(d_i!) *
      sum_k [z**(p**k)] prod_i (z + z**p + ... + z**(p**i))**d_i  (mod p).

The product is calculated with a dictionary of nonzero coefficients; no
integer coefficient of the original composition is needed.  If n is zero
or is outside n == 1 (mod p-1), leading_residue returns 0 by convention:
the original coefficient itself is zero, and no normalized quotient is
being asserted.  digit_weight returns None in this unsupported case.

All arithmetic is exact and uses the Python standard library.  Run

  python leading_residue.py --prime 3 --degree 51
  python leading_residue.py --verify ../data/leading_residue_verification.json

The verifier uses a separate ordinary-power-series composition algorithm.
It tests the digit formula through degree 300 for primes 2, 3, 5 and 7,
checks top-digit stability, and checks the three proved sharp families.
"""

from __future__ import annotations

import argparse
import json
from math import factorial, isqrt
from pathlib import Path


def require_prime(p: int) -> None:
    if p < 2 or any(p % d == 0 for d in range(2, isqrt(p) + 1)):
        raise ValueError("p must be prime")


def base_p_digits(n: int, p: int) -> list[int]:
    """Return digits in increasing order of place value."""
    if n < 0:
        raise ValueError("n must be nonnegative")
    digits = []
    while n:
        digits.append(n % p)
        n //= p
    return digits


def digit_weight(p: int, n: int) -> int | None:
    """Return w=(s_p(n)-1)/(p-1), or None for unsupported n."""
    require_prime(p)
    digits = base_p_digits(n, p)
    if n == 0 or (n - 1) % (p - 1):
        return None
    return (sum(digits) - 1) // (p - 1)


def digit_polynomial(p: int, n: int) -> dict[int, int]:
    """Return prod_i (z+z^p+...+z^(p^i))^d_i over F_p, sparsely."""
    require_prime(p)
    digits = base_p_digits(n, p)
    result = {0: 1}
    powers = []
    place = 1
    for digit in digits:
        powers.append(place)
        for _ in range(digit):
            new: dict[int, int] = {}
            for exponent, coefficient in result.items():
                for shift in powers:
                    target = exponent + shift
                    new[target] = (new.get(target, 0) + coefficient) % p
            result = {e: c for e, c in new.items() if c}
        place *= p
    return result


def leading_residue(p: int, n: int) -> int:
    """Return a_2(n)/p^w modulo p; return 0 for unsupported n.

    The returned representative is an integer in range(p).  For unsupported
    n, digit_weight(p,n) is None and the coefficient a_2(n) is identically 0.
    """
    weight = digit_weight(p, n)
    if weight is None:
        return 0
    digits = base_p_digits(n, p)
    polynomial = digit_polynomial(p, n)
    pure_sum = 0
    place = 1
    while place <= n:
        pure_sum += polynomial.get(place, 0)
        place *= p
    denominator = 1
    for digit in digits:
        denominator = denominator * factorial(digit) % p
    return (pow(-1, weight, p) * pow(denominator, -1, p) * pure_sum) % p


def multiply_truncated(a: list[int], b: list[int], degree: int,
                       modulus: int) -> list[int]:
    """Ordinary multiplication, independent of the digit formula."""
    result = [0] * (degree + 1)
    nonzero_a = [(i, c) for i, c in enumerate(a) if c]
    nonzero_b = [(i, c) for i, c in enumerate(b) if c]
    for i, ai in nonzero_a:
        for j, bj in nonzero_b:
            if i + j > degree:
                break
            result[i + j] = (result[i + j] + ai * bj) % modulus
    return result


def direct_second_iterate(p: int, degree: int, modulus: int) -> list[int]:
    """Compute F_p(F_p(x)) by ordinary truncated polynomial powers."""
    f = [0] * (degree + 1)
    place = 1
    while place <= degree:
        f[place] = 1
        place *= p
    result = [0] * (degree + 1)
    power = f
    exponent = 1
    while exponent <= degree:
        result = [(a + b) % modulus for a, b in zip(result, power)]
        exponent *= p
        if exponent > degree:
            break
        raised = [1] + [0] * degree
        for _ in range(p):
            raised = multiply_truncated(raised, power, degree, modulus)
        power = raised
    return result


def sharp_family_degree(p: int, weight: int, top_place: int) -> int:
    """The three proved families, with their indicated minimum top place."""
    if weight == 1 and top_place >= 1:
        return p ** top_place + p - 1
    if weight in (2, 3) and top_place >= weight + 1:
        return p ** top_place + (p - 1) * sum(p ** j for j in range(1, weight + 1))
    raise ValueError("family requires w=1,r>=1; w=2,r>=3; or w=3,r>=4")


def verify(output_path: Path, degree: int = 300) -> dict:
    report: dict = {
        "status": "passed",
        "arithmetic": "exact Python integer arithmetic; no floating point",
        "formula": "a_2(n)/p^w mod p, w=(s_p(n)-1)/(p-1)",
        "unsupported_convention": "n=0 or n != 1 mod (p-1): coefficient and output are zero; w is null",
        "direct_composition": [],
        "top_digit_stability": [],
        "sharp_families": [],
    }
    for p in (2, 3, 5, 7):
        weights = [digit_weight(p, n) for n in range(1, degree + 1)]
        max_weight = max(w for w in weights if w is not None)
        modulus = p ** (max_weight + 1)
        coefficients = direct_second_iterate(p, degree, modulus)
        supported = 0
        unsupported = 0
        for n in range(degree + 1):
            weight = digit_weight(p, n)
            residue = leading_residue(p, n)
            if weight is None:
                assert coefficients[n] == residue == 0, (p, n)
                unsupported += 1
            else:
                assert coefficients[n] % p ** weight == 0, (p, n, weight)
                actual = coefficients[n] // p ** weight % p
                assert actual == residue, (p, n, weight, actual, residue)
                supported += 1
        report["direct_composition"].append({
            "prime": p, "maximum_degree": degree, "modulus": modulus,
            "supported_coefficients_checked": supported,
            "zero_coefficients_checked": unsupported,
            "status": "passed",
        })

    # Vary the leading digit and the lower remainder independently.
    # Include only supported exponents with more than one digit token.
    for p in (2, 3, 5):
        checked = 0
        top_place = 2
        for leading_digit in range(1, p):
            for remainder in range(p ** top_place):
                n = leading_digit * p ** top_place + remainder
                weight = digit_weight(p, n)
                if weight is None or weight == 0:
                    continue
                expected = leading_residue(p, n)
                for shift in (1, 2):
                    moved = leading_digit * p ** (top_place + shift) + remainder
                    assert digit_weight(p, moved) == weight
                    assert leading_residue(p, moved) == expected, (p, n, moved)
                    checked += 1
        report["top_digit_stability"].append({
            "prime": p, "initial_top_place": top_place,
            "extra_places": [1, 2], "comparisons": checked,
            "status": "passed",
        })

    for p in (2, 3, 5):
        for weight in (1, 2, 3):
            minimum_top_place = 1 if weight == 1 else weight + 1
            for top_place in (minimum_top_place, minimum_top_place + 1):
                n = sharp_family_degree(p, weight, top_place)
                assert digit_weight(p, n) == weight
                residue = leading_residue(p, n)
                assert residue == 1, (p, weight, n, residue)
                report["sharp_families"].append({
                    "prime": p, "weight": weight, "top_place": top_place,
                    "degree": n, "normalized_residue": residue,
                    "status": "passed",
                })
    output_path.parent.mkdir(parents=True, exist_ok=True)
    output_path.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    return report


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--prime", type=int)
    parser.add_argument("--degree", type=int)
    parser.add_argument("--verify", type=Path)
    parser.add_argument("--verification-degree", type=int, default=300)
    args = parser.parse_args()
    if args.verify is not None:
        report = verify(args.verify, args.verification_degree)
        total = sum(r["supported_coefficients_checked"] + r["zero_coefficients_checked"]
                    for r in report["direct_composition"])
        print(f"Passed {total} direct-composition coefficient checks; "
              f"stability and sharp families passed. Wrote {args.verify}.")
    elif args.prime is not None and args.degree is not None:
        print(json.dumps({"prime": args.prime, "degree": args.degree,
                          "weight": digit_weight(args.prime, args.degree),
                          "normalized_residue": leading_residue(args.prime, args.degree)}))
    else:
        parser.error("supply --prime and --degree, or --verify")


if __name__ == "__main__":
    main()
