#!/usr/bin/env python3
"""Exact, finite arithmetic for Q(theta), theta^3 - theta - 1 = 0.

Python 3 standard library only.  The output illustrates the proposed Hecke
L-function target.  It is NOT a proof or numerical verification of RH.

Usage:
    python3 cubic23_exact.py --output-dir ./results

The assertions check exact algebra and the stated finite coefficient range.
No modular-form or eta-product identity is assumed or claimed.
"""

from __future__ import annotations

import argparse
import csv
import hashlib
import json
from math import gcd, isqrt
from pathlib import Path


def polynomial_multiply(a: tuple[int, ...], b: tuple[int, ...]) -> tuple[int, ...]:
    """Multiply coefficient lists in ascending order, using exact integers."""
    out = [0] * (len(a) + len(b) - 1)
    for i, ai in enumerate(a):
        for j, bj in enumerate(b):
            out[i + j] += ai * bj
    while len(out) > 1 and out[-1] == 0:
        out.pop()
    return tuple(out)


def polynomial_mod(a: tuple[int, ...], p: int) -> tuple[int, ...]:
    return tuple(x % p for x in a)


def f(x: int) -> int:
    return x**3 - x - 1


def primes_up_to(limit: int) -> list[int]:
    if limit < 2:
        return []
    sieve = bytearray(b"\x01") * (limit + 1)
    sieve[0:2] = b"\x00\x00"
    for p in range(2, isqrt(limit) + 1):
        if sieve[p]:
            sieve[p * p : limit + 1 : p] = b"\x00" * (
                (limit - p * p) // p + 1
            )
    return [p for p in range(2, limit + 1) if sieve[p]]


def reduced_forms(discriminant: int) -> list[tuple[int, int, int]]:
    """Enumerate primitive reduced positive definite forms of negative D.

    Reduction conventions: |b| <= a <= c, with b >= 0 on either boundary
    |b| = a or a = c.  The standard reduced-form bound is 3*a^2 <= |D|.
    """
    assert discriminant < 0 and discriminant % 4 in (0, 1)
    out = []
    for a in range(1, isqrt((-discriminant) // 3) + 1):
        for b in range(-a, a + 1):
            numerator = b * b - discriminant
            if numerator % (4 * a):
                continue
            c = numerator // (4 * a)
            if c < a:
                continue
            if (abs(b) == a or a == c) and b < 0:
                continue
            if gcd(gcd(a, abs(b)), c) != 1:
                continue
            assert b * b - 4 * a * c == discriminant
            out.append((a, b, c))
    return out


def prime_record(p: int) -> dict:
    roots = [r for r in range(p) if f(r) % p == 0]
    # All primes except 23 are separable because disc(f) = -23.
    repeated = [r for r in roots if (3 * r * r - 1) % p == 0]
    if p == 23:
        assert roots == [3, 10] and repeated == [10]
        return {
            "prime": p,
            "ramified": True,
            "roots_mod_p": roots,
            "factorization_degrees": "1,1 (ramification 1,2)",
            "frobenius_cycle_type": "ramified",
            "hecke_trace": 1,
            "zeta_F_denominator": [1, -2, 1],
            "hecke_denominator": [1, -1],
        }
    assert not repeated
    if len(roots) == 3:
        splitting, cycle, trace = "1,1,1", "identity", 2
        zeta_den, hecke_den = [1, -3, 3, -1], [1, -2, 1]
    elif len(roots) == 1:
        splitting, cycle, trace = "1,2", "transposition", 0
        zeta_den, hecke_den = [1, -1, -1, 1], [1, 0, -1]
    elif len(roots) == 0:
        splitting, cycle, trace = "3", "3-cycle", -1
        zeta_den, hecke_den = [1, 0, 0, -1], [1, 1, 1]
    else:
        raise AssertionError(f"Impossible separable cubic root count at p={p}")
    return {
        "prime": p,
        "ramified": False,
        "roots_mod_p": roots,
        "factorization_degrees": splitting,
        "frobenius_cycle_type": cycle,
        "hecke_trace": trace,
        "zeta_F_denominator": zeta_den,
        "hecke_denominator": hecke_den,
    }


def reciprocal_series(denominator: list[int], degree: int) -> list[int]:
    """Coefficients of 1/D(t) through t^degree, for D(0)=1."""
    assert denominator[0] == 1
    coeffs = [1] + [0] * degree
    for k in range(1, degree + 1):
        coeffs[k] = -sum(
            denominator[j] * coeffs[k - j]
            for j in range(1, min(k, len(denominator) - 1) + 1)
        )
    return coeffs


def multiplicative_coefficients(limit: int) -> list[int]:
    """Euler-product coefficients for the cubic class-character target."""
    prime_powers = {}
    for p in primes_up_to(limit):
        power, max_k = p, 0
        while power <= limit:
            max_k += 1
            power *= p
        prime_powers[p] = reciprocal_series(
            prime_record(p)["hecke_denominator"], max_k
        )
    values = [0] * (limit + 1)
    values[1] = 1
    primes = list(prime_powers)
    for n in range(2, limit + 1):
        remainder, value = n, 1
        for p in primes:
            if p * p > remainder:
                break
            exponent = 0
            while remainder % p == 0:
                remainder //= p
                exponent += 1
            if exponent:
                value *= prime_powers[p][exponent]
        if remainder > 1:
            value *= prime_powers[remainder][1]
        values[n] = value
    return values


def ceil_div(numerator: int, denominator: int) -> int:
    assert denominator > 0
    return -((-numerator) // denominator)


def theta_coefficients(form: tuple[int, int, int], limit: int) -> list[int]:
    """Count all integer pairs Q(x,y)=n for 0 <= n <= limit, exactly.

    The bounds are exhaustive, using
        4*a*Q(x,y) = (2*a*x+b*y)^2 + |D|*y^2.
    Thus there is no arbitrary numerical search box.
    """
    a, b, c = form
    abs_d = 4 * a * c - b * b
    assert a > 0 and abs_d > 0
    counts = [0] * (limit + 1)
    y_bound = isqrt((4 * a * limit) // abs_d)
    for y in range(-y_bound, y_bound + 1):
        square_bound = isqrt(4 * a * limit - abs_d * y * y)
        x_min = ceil_div(-square_bound - b * y, 2 * a)
        x_max = (square_bound - b * y) // (2 * a)
        for x in range(x_min, x_max + 1):
            n = a * x * x + b * x * y + c * y * y
            assert 0 <= n <= limit
            assert 4 * a * n == (2 * a * x + b * y) ** 2 + abs_d * y * y
            counts[n] += 1
    assert counts[0] == 1
    return counts


def write_csv(path: Path, fieldnames: list[str], rows: list[dict]) -> None:
    with path.open("w", newline="", encoding="utf-8") as stream:
        writer = csv.DictWriter(stream, fieldnames=fieldnames)
        writer.writeheader()
        writer.writerows(rows)


def run(output_dir: Path, prime_limit: int, coefficient_limit: int) -> dict:
    assert prime_limit >= 23 and coefficient_limit >= 1
    output_dir.mkdir(parents=True, exist_ok=True)

    # For X^3 + bX^2 + cX + d, use the exact cubic discriminant formula.
    b, c, d = 0, -1, -1
    disc = b * b * c * c - 4 * c**3 - 4 * b**3 * d - 27 * d * d + 18 * b * c * d
    assert disc == -23
    # Monic cubics over Q are reducible iff they have an integral root dividing d.
    rational_root_candidates = [-1, 1]
    assert all(f(r) != 0 for r in rational_root_candidates)

    forms = reduced_forms(-23)
    assert forms == [(1, 1, 6), (2, -1, 3), (2, 1, 3)]

    factor_mod23 = polynomial_multiply(
        polynomial_multiply((-10, 1), (-10, 1)), (-3, 1)
    )
    assert polynomial_mod(factor_mod23, 23) == polynomial_mod((-1, -1, 0, 1), 23)

    euler_table = [
        {"type": "identity", "zeta_F_denominator": [1, -3, 3, -1], "hecke_denominator": [1, -2, 1]},
        {"type": "transposition", "zeta_F_denominator": [1, -1, -1, 1], "hecke_denominator": [1, 0, -1]},
        {"type": "3-cycle", "zeta_F_denominator": [1, 0, 0, -1], "hecke_denominator": [1, 1, 1]},
        {"type": "ramified prime 23", "zeta_F_denominator": [1, -2, 1], "hecke_denominator": [1, -1]},
    ]
    for row in euler_table:
        assert polynomial_multiply((1, -1), tuple(row["hecke_denominator"])) == tuple(row["zeta_F_denominator"])

    prime_rows = [prime_record(p) for p in primes_up_to(prime_limit)]
    for row in prime_rows:
        assert polynomial_multiply((1, -1), tuple(row["hecke_denominator"])) == tuple(row["zeta_F_denominator"])
    split_csv_rows = [
        {
            "prime": row["prime"],
            "ramified": int(row["ramified"]),
            "roots_mod_p": ";".join(map(str, row["roots_mod_p"])),
            "factorization_degrees": row["factorization_degrees"],
            "frobenius_cycle_type": row["frobenius_cycle_type"],
            "hecke_trace": row["hecke_trace"],
            "hecke_denominator_coefficients": ";".join(map(str, row["hecke_denominator"])),
        }
        for row in prime_rows
    ]
    splitting_path = output_dir / "cubic23_prime_splitting.csv"
    write_csv(splitting_path, list(split_csv_rows[0]), split_csv_rows)

    principal_theta = theta_coefficients((1, 1, 6), coefficient_limit)
    other_theta = theta_coefficients((2, 1, 3), coefficient_limit)
    inverse_theta = theta_coefficients((2, -1, 3), coefficient_limit)
    assert other_theta == inverse_theta
    l_coeffs = multiplicative_coefficients(coefficient_limit)
    coefficient_rows = []
    for n in range(1, coefficient_limit + 1):
        difference = principal_theta[n] - other_theta[n]
        assert difference % 2 == 0
        theta_value = difference // 2
        assert theta_value == l_coeffs[n], (n, theta_value, l_coeffs[n])
        coefficient_rows.append(
            {
                "n": n,
                "r_x2_xy_6y2": principal_theta[n],
                "r_2x2_xy_3y2": other_theta[n],
                "theta_difference_over_2": theta_value,
                "euler_product_coefficient": l_coeffs[n],
                "equal": True,
            }
        )
    coeff_path = output_dir / "cubic23_coefficient_comparison.csv"
    write_csv(coeff_path, list(coefficient_rows[0]), coefficient_rows)

    counts = {}
    for row in prime_rows:
        kind = row["frobenius_cycle_type"]
        counts[kind] = counts.get(kind, 0) + 1

    result = {
        "purpose": "Exact finite illustrations for a proposed Hecke L-function extension; not proof or verification of RH.",
        "dependencies": "Python 3 standard library only",
        "polynomial": "X^3-X-1",
        "polynomial_coefficients_ascending": [-1, -1, 0, 1],
        "discriminant": disc,
        "irreducible_over_Q": True,
        "irreducibility_reason": "A reducible cubic over Q has a rational root; monic rational-root candidates +/-1 both fail.",
        "rational_root_values": {str(r): f(r) for r in rational_root_candidates},
        "reduced_forms_discriminant_minus23": forms,
        "reduced_form_count": len(forms),
        "mod23_factorization": "(X-10)^2*(X-3)",
        "mod23_factorization_checked": True,
        "euler_denominator_convention": "Integer arrays in ascending powers of t=p^(-s); D_F(t)=(1-t)*D_Hecke(t).",
        "euler_denominator_identities": euler_table,
        "prime_splitting_limit": prime_limit,
        "prime_count": len(prime_rows),
        "cycle_type_counts": counts,
        "theta_identity_compared": "(Theta_(1,1,6)-Theta_(2,1,3))/2 versus Euler-product L coefficients",
        "coefficient_range_inclusive": [1, coefficient_limit],
        "coefficient_agreements": coefficient_limit,
        "theta_enumeration_complete_in_range": True,
        "theta_completeness_reason": "4aQ=(2ax+by)^2+23y^2 supplies exhaustive exact integer bounds.",
        "all_assertions_passed": True,
        "csv_sha256": {
            splitting_path.name: hashlib.sha256(splitting_path.read_bytes()).hexdigest(),
            coeff_path.name: hashlib.sha256(coeff_path.read_bytes()).hexdigest(),
        },
        "limitations": [
            "Finite coefficient agreement is not a proof of a global theta/Hecke identity.",
            "No assertion or computation of zeros of L-functions is made.",
            "Class field theory identifies the order-3 ideal-class character; that identification is explained in the report, not established by these computations.",
            "No eta-product identity is assumed or asserted.",
        ],
    }
    (output_dir / "cubic23_results.json").write_text(
        json.dumps(result, indent=2, ensure_ascii=False) + "\n", encoding="utf-8"
    )
    return result


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output-dir", type=Path, default=Path(__file__).resolve().parent)
    parser.add_argument("--prime-limit", type=int, default=1000)
    parser.add_argument("--coefficient-limit", type=int, default=500)
    args = parser.parse_args()
    result = run(args.output_dir, args.prime_limit, args.coefficient_limit)
    print(json.dumps({
        "all_assertions_passed": result["all_assertions_passed"],
        "reduced_forms": result["reduced_forms_discriminant_minus23"],
        "prime_count": result["prime_count"],
        "coefficient_agreements": result["coefficient_agreements"],
        "cycle_type_counts": result["cycle_type_counts"],
        "output_dir": str(args.output_dir.resolve()),
    }, indent=2))


if __name__ == "__main__":
    main()
