#!/usr/bin/env python3
"""Exact certificates for Gregory sign thresholds; Python standard library only.

The computation proves Gr(3)=11, Gr(4)=36, Gr(5)=113, Gr(6)=346,
using the cumulative-positivity lemma in the accompanying article. No
floating-point calculation is used in any assertion. The JSON contains
rational data, not trusted assumptions: every entry is recomputed.
"""
from __future__ import annotations
import argparse
from fractions import Fraction
import json
from math import comb, factorial, lcm
from pathlib import Path
import sys

if not __debug__:
    raise RuntimeError("Run without -O: exact verification requires assertions")

if hasattr(sys, "set_int_max_str_digits"):
    sys.set_int_max_str_digits(0)

CASES = ((3, 11, 12), (4, 36, 40), (5, 113, 126), (6, 346, 378))
DEFAULT = Path(__file__).resolve().parents[1] / "data" / "exact_certificates.json"


def coefficients(max_order: int, max_index: int) -> list[list[Fraction]]:
    """Invert log(1+x)/x, then apply the differential order recurrence."""
    if max_order < 1 or max_index < 0:
        raise ValueError("Require max_order >= 1 and max_index >= 0")
    classical = [Fraction(1)]
    for n in range(1, max_index + 1):
        classical.append(-sum((Fraction((-1)**k, k+1) * classical[n-k]
                               for k in range(1, n+1)), Fraction(0)))
    rows = [[Fraction(1)] + [Fraction(0)] * max_index, classical]
    for m in range(1, max_order):
        old = rows[-1]
        rows.append([Fraction(1)] + [
            Fraction(m-n, m) * old[n] + Fraction(m-n+1, m) * old[n-1]
            for n in range(1, max_index+1)])
    return rows


def signed_falling_polynomial(n: int) -> list[int]:
    """Coefficients of (-1)^(n-1) t(t-1)...(t-n+1)."""
    if n < 1:
        raise ValueError("n must be positive")
    p = [1]
    for j in range(n):
        q = [0] * (len(p)+1)
        for k, value in enumerate(p):
            q[k] -= j * value
            q[k+1] += value
        p = q
    return p if n % 2 else [-v for v in p]


def multiply(p: list[int], q: list[int]) -> list[int]:
    out = [0] * (len(p)+len(q)-1)
    for i, a in enumerate(p):
        for j, b in enumerate(q):
            out[i+j] += a*b
    return out


def exact_prefixes(m: int, n: int, endpoints: list[int]) -> dict[int, Fraction]:
    """Integrate the polynomial-density formula exactly at integer endpoints."""
    if m < 1 or n <= m or any(T < 0 or T > m for T in endpoints):
        raise ValueError("Require m >= 1, n > m, and endpoints in [0,m]")
    p = signed_falling_polynomial(n)
    denominator_lcm = lcm(*range(1, n+m+1))
    denominator = factorial(n) * factorial(m-1) * denominator_lcm
    result = {}
    for T in endpoints:
        numerator = 0
        for j in range(T):
            shift = [comb(m-1, k)*(-j)**(m-1-k) for k in range(m)]
            product = multiply(p, shift)
            integral = sum(
                value * (denominator_lcm // (k+1)) * (T**(k+1)-j**(k+1))
                for k, value in enumerate(product))
            numerator += (-1)**j * comb(m, j) * integral
        result[T] = Fraction(numerator, denominator)
    return result


def encode(q: Fraction) -> dict[str, str]:
    return {"numerator": str(q.numerator), "denominator": str(q.denominator)}


def make_certificate() -> dict:
    rows = coefficients(max(m for m, _, _ in CASES), max(N for _, _, N in CASES))
    assert rows[1][1] == Fraction(1, 2)
    assert rows[2][3] == 0 and rows[2][4] == -Fraction(1, 240)
    assert exact_prefixes(2, 4, [2])[2] == Fraction(1, 240)
    print("PASS base cases Gr(1)=1 and Gr(2)=4 (using the article\'s sign argument).", flush=True)
    cases = []
    for m, threshold, anchor in CASES:
        signed = lambda n: (-1)**(n-1) * rows[m][n]
        before = signed(threshold-1)
        assert before < 0, (m, "lower obstruction")
        finite = {n: signed(n) for n in range(threshold, anchor)}
        assert all(value > 0 for value in finite.values()), (m, "finite interval")
        endpoints = sorted(set(range(2, m+1, 2)) | {m})
        prefixes = exact_prefixes(m, anchor, endpoints)
        assert all(value > 0 for value in prefixes.values()), (m, "tail certificate")
        assert prefixes[m] == signed(anchor), (m, "anchor consistency")
        # A genuinely independent integral check of both sides of the threshold.
        for n in (threshold-1, threshold):
            assert exact_prefixes(m, n, [m])[m] == signed(n)
        cases.append({
            "order": m, "threshold": threshold, "tail_anchor": anchor,
            "lower_obstruction": {"n": threshold-1, "value": encode(before)},
            "finite_positive_coefficients": {str(n): encode(value)
                                              for n, value in finite.items()},
            "positive_prefixes_at_anchor": {str(T): encode(value)
                                             for T, value in prefixes.items()},
        })
        print(f"PASS Gr({m})={threshold}: negative at {threshold-1}; "
              f"{len(finite)} positive coefficients before anchor {anchor}; "
              f"positive exact cumulative integrals at {endpoints}.", flush=True)
    assert 113 * 100 < 47 * 3**5
    print("PASS literal conjecture counterexample: 11300 < 11421.", flush=True)
    return {"schema": "gregory-sign-certificates-v1", "cases": cases}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--write", action="store_true", help="Rebuild the certificate JSON")
    parser.add_argument("--certificate", type=Path, default=DEFAULT)
    args = parser.parse_args()
    calculated = make_certificate()
    if args.write:
        args.certificate.parent.mkdir(parents=True, exist_ok=True)
        args.certificate.write_text(json.dumps(calculated, indent=2)+"\n", encoding="utf-8")
        print(f"Wrote {args.certificate}")
    else:
        stored = json.loads(args.certificate.read_text(encoding="utf-8"))
        if calculated != stored:
            raise AssertionError("Certificate data differ from recomputed exact values")
        print("PASS all saved certificate values match independent recomputation.")


if __name__ == "__main__":
    main()
