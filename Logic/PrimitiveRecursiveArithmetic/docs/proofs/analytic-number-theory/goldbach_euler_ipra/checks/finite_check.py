#!/usr/bin/env python3
"""Exact finite checks accompanying the iPRA Goldbach--Euler proof.

This program is *not* a substitute for the proof.  It checks the finite
identities, canonical decompositions, and sample instances used in the paper,
using Python's exact Fraction arithmetic.
"""

from __future__ import annotations

import argparse
import json
from fractions import Fraction
from functools import reduce
from math import gcd, isqrt
from pathlib import Path
from typing import Dict, Iterable, List, Sequence, Tuple


def factor_exponents(n: int) -> List[Tuple[int, int]]:
    """Return the prime factorization of n >= 2 as (prime, exponent) pairs."""
    if n < 2:
        raise ValueError("factor_exponents expects n >= 2")
    x = n
    out: List[Tuple[int, int]] = []
    p = 2
    while p * p <= x:
        if x % p == 0:
            e = 0
            while x % p == 0:
                x //= p
                e += 1
            out.append((p, e))
        p = 3 if p == 2 else p + 2
    if x > 1:
        out.append((x, 1))
    return out


def canonical_power(n: int) -> Tuple[int, int]:
    """Return the unique (root-free base r, exponent e) with n = r**e."""
    fs = factor_exponents(n)
    e = reduce(gcd, (a for _, a in fs))
    r = 1
    for p, a in fs:
        r *= p ** (a // e)
    assert r ** e == n
    return r, e


def is_perfect_power(n: int) -> bool:
    return n >= 4 and canonical_power(n)[1] >= 2


def is_root_free(n: int) -> bool:
    return n >= 2 and canonical_power(n)[1] == 1


def perfect_powers_up_to(n: int) -> List[int]:
    """Distinct perfect powers in increasing order."""
    if n < 4:
        return []
    values = set()
    for a in range(2, isqrt(n) + 1):
        v = a * a
        while v <= n:
            values.add(v)
            if v > n // a:
                break
            v *= a
    return sorted(values)


def target_partial(n: int) -> Fraction:
    return sum((Fraction(1, p - 1) for p in perfect_powers_up_to(n)), Fraction(0))


def canonical_pairs_up_to(n: int) -> List[Tuple[int, int]]:
    return [canonical_power(p) for p in perfect_powers_up_to(n)]


def finite_geom_denominator(r: int, s: int, i_max: int) -> Tuple[Fraction, Fraction]:
    """Check 1/(r^s-1) = finite geometric prefix + exact remainder."""
    lhs = Fraction(1, r**s - 1)
    prefix = sum((Fraction(1, r ** (s * i)) for i in range(1, i_max + 1)), Fraction(0))
    remainder = Fraction(1, r ** (s * i_max) * (r**s - 1))
    assert lhs == prefix + remainder
    return prefix, remainder


def finite_geom_exponent(m: int, s_max: int) -> Fraction:
    """Check sum_{s=2}^S m^-s closed form."""
    lhs = sum((Fraction(1, m**s) for s in range(2, s_max + 1)), Fraction(0))
    rhs = Fraction(1, m * (m - 1)) - Fraction(1, m**s_max * (m - 1))
    assert lhs == rhs
    return lhs


def telescoping(m_max: int) -> Fraction:
    lhs = sum((Fraction(1, m * (m - 1)) for m in range(2, m_max + 1)), Fraction(0))
    rhs = Fraction(1) - Fraction(1, m_max)
    assert lhs == rhs
    return lhs


def lower_rectangle(r_max: int, s_max: int) -> Tuple[Fraction, Fraction]:
    """Return T(R,S) and U(R,S), checking T >= U.

    T is the canonical-root rectangle from target terms.
    U is sum_{m<=R, 2<=s<=S} m^-s.
    """
    t = sum(
        (Fraction(1, r**s - 1)
         for r in range(2, r_max + 1) if is_root_free(r)
         for s in range(2, s_max + 1)),
        Fraction(0),
    )
    u = sum(
        (Fraction(1, m**s) for m in range(2, r_max + 1) for s in range(2, s_max + 1)),
        Fraction(0),
    )
    assert t >= u

    closed = Fraction(1) - Fraction(1, r_max) - sum(
        (Fraction(1, m**s_max * (m - 1)) for m in range(2, r_max + 1)),
        Fraction(0),
    )
    assert u == closed
    return t, u


def upper_truncation(n: int, i_max: int) -> Tuple[Fraction, Fraction]:
    """Check the finite upper-bound core A_{N,I} < 1 - 1/N^I."""
    pairs = canonical_pairs_up_to(n)
    truncated = sum(
        (Fraction(1, r ** (s * i)) for r, s in pairs for i in range(1, i_max + 1)),
        Fraction(0),
    )

    seen: Dict[int, int] = {}
    grouped_bound = Fraction(0)
    roots = sorted({r for r, _ in pairs})
    for r in roots:
        exponents = [s for rr, s in pairs if rr == r]
        for i in range(1, i_max + 1):
            m = r**i
            if m in seen:
                raise AssertionError(f"canonical-root injection failed at m={m}")
            seen[m] = 1
            finite_group = sum((Fraction(1, m**s) for s in exponents), Fraction(0))
            weight = Fraction(1, m * (m - 1))
            assert finite_group < weight
            grouped_bound += weight

    assert truncated < grouped_bound
    full_telescoping_bound = Fraction(1) - Fraction(1, n**i_max)
    assert grouped_bound <= full_telescoping_bound
    assert truncated < 1
    return truncated, grouped_bound


def check_canonical(limit: int) -> None:
    for n in range(2, limit + 1):
        r, e = canonical_power(n)
        assert r >= 2 and e >= 1 and r**e == n
        assert is_root_free(r)
        # Brute-force uniqueness in the requested finite audit range.
        witnesses: List[Tuple[int, int]] = []
        for a in range(2, n + 1):
            if not is_root_free(a):
                continue
            v = a
            j = 1
            while v <= n:
                if v == n:
                    witnesses.append((a, j))
                if v > n // a:
                    break
                v *= a
                j += 1
        assert witnesses == [(r, e)], (n, witnesses, (r, e))


def proof_constants(k: int) -> Dict[str, str | int]:
    r = 2 ** (k + 1)
    s = 2 * k + 2
    b = r**s
    base_error = Fraction(1, r)
    exponent_error = Fraction(r, 2**s)
    target_error = Fraction(1, 2**k)
    assert base_error + exponent_error == target_error
    return {
        "k": k,
        "R": str(r),
        "S": s,
        "B": str(b),
        "B_power_of_two_exponent": 2 * (k + 1) ** 2,
        "base_error": str(base_error),
        "exponent_error": str(exponent_error),
        "total_error_bound": str(target_error),
    }


def decimal(q: Fraction, digits: int = 16) -> str:
    return f"{q.numerator / q.denominator:.{digits}f}"


def run(output_dir: Path, canonical_limit: int = 3000) -> str:
    output_dir.mkdir(parents=True, exist_ok=True)

    check_canonical(canonical_limit)
    for r, s, i in [(2, 2, 5), (3, 4, 3), (5, 2, 4), (6, 5, 2)]:
        finite_geom_denominator(r, s, i)
    for m, s in [(2, 8), (3, 7), (10, 5)]:
        finite_geom_exponent(m, s)
    for m in [2, 3, 10, 100]:
        telescoping(m)

    lower_rows = []
    for k in range(0, 8):
        r = 2 ** (k + 1)
        s = 2 * k + 2
        t, u = lower_rectangle(r, s)
        threshold = Fraction(1) - Fraction(1, 2**k)
        assert u >= threshold
        lower_rows.append({
            "k": k,
            "R": r,
            "S": s,
            "T_decimal": decimal(t),
            "U_decimal": decimal(u),
            "threshold_decimal": decimal(threshold),
            "T_ge_U": True,
            "U_ge_threshold": True,
        })

    upper_rows = []
    for n, i in [(16, 3), (64, 4), (256, 4), (1000, 5)]:
        a_i, group = upper_truncation(n, i)
        exact = target_partial(n)
        assert exact <= 1
        upper_rows.append({
            "N": n,
            "I": i,
            "target_partial_decimal": decimal(exact),
            "truncated_decimal": decimal(a_i),
            "grouped_weight_decimal": decimal(group),
        })

    modulus_samples = []
    for k in range(0, 3):
        b = 2 ** (2 * (k + 1) ** 2)
        exact = target_partial(b)
        error = Fraction(1) - exact
        bound = Fraction(1, 2**k)
        assert 0 <= error <= bound
        modulus_samples.append({
            "k": k,
            "B": str(b),
            "partial_decimal": decimal(exact),
            "error_decimal": decimal(error),
            "bound_decimal": decimal(bound),
        })

    constants = [proof_constants(k) for k in range(0, 13)]
    certificate = {
        "description": "Finite exact checks for the constructive Goldbach--Euler proof",
        "canonical_uniqueness_checked_through": canonical_limit,
        "first_perfect_powers": perfect_powers_up_to(1024)[:30],
        "constants": constants,
        "lower_rectangle_checks": lower_rows,
        "upper_truncation_checks": upper_rows,
        "modulus_sample_checks": modulus_samples,
    }
    (output_dir / "certificate.json").write_text(json.dumps(certificate, indent=2) + "\n", encoding="utf-8")

    lines: List[str] = []
    lines.append("Goldbach--Euler constructive proof: exact finite check report")
    lines.append("=" * 69)
    lines.append(f"Canonical root decomposition brute-force checked through n={canonical_limit}.")
    lines.append("Finite geometric identities and telescoping identities: PASS.")
    lines.append("")
    lines.append("Lower-rectangle checks:")
    for row in lower_rows:
        lines.append(
            f"  k={row['k']:2d} R={row['R']:4d} S={row['S']:2d} "
            f"T={row['T_decimal']} U={row['U_decimal']} "
            f"threshold={row['threshold_decimal']}"
        )
    lines.append("")
    lines.append("Upper-truncation checks:")
    for row in upper_rows:
        lines.append(
            f"  N={row['N']:4d} I={row['I']} target={row['target_partial_decimal']} "
            f"truncated={row['truncated_decimal']} grouped={row['grouped_weight_decimal']}"
        )
    lines.append("")
    lines.append("Direct modulus samples:")
    for row in modulus_samples:
        lines.append(
            f"  k={row['k']} B={row['B']} partial={row['partial_decimal']} "
            f"error={row['error_decimal']} <= {row['bound_decimal']}"
        )
    lines.append("")
    lines.append("All exact checks passed.")
    report = "\n".join(lines) + "\n"
    (output_dir / "finite_check_report.txt").write_text(report, encoding="utf-8")
    return report


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--output-dir", type=Path, default=Path(__file__).resolve().parent)
    parser.add_argument("--canonical-limit", type=int, default=3000)
    args = parser.parse_args()
    print(run(args.output_dir, args.canonical_limit), end="")


if __name__ == "__main__":
    main()
