#!/usr/bin/env python3
"""Exact-integer regression checks for the finitary Barnes-G core.

These are executable checks, not proofs in iPRA.  Every checked equality is an
identity between primitive-recursive integer expressions; the paper gives the
uniform induction proofs and the Lean blueprint gives their intended object-
theory targets.
"""
from __future__ import annotations
import argparse, json, math
from pathlib import Path


def factorial(n: int) -> int:
    assert n >= 0
    out = 1
    for k in range(1, n + 1):
        out *= k
    return out


def superfactorial(n: int) -> int:
    """sf(n)=0!1!...n!, with sf(-1)=1 by empty product convention."""
    out = 1
    for k in range(0, n + 1):
        out *= factorial(k)
    return out


def barnes_g_nat(n: int) -> int:
    """The positive-integer Barnes value G(n); this routine is for n>=1."""
    assert n >= 1
    return superfactorial(n - 2)


def hyperfactorial(n: int) -> int:
    out = 1
    for k in range(1, n + 1):
        out *= k ** k
    return out


def odd_double_factorial(i: int) -> int:
    """(2i-1)!!, with value 1 at i=0."""
    out = 1
    for j in range(1, i + 1):
        out *= 2 * j - 1
    return out


def half_coefficient(k: int) -> int:
    """c_k in MathWorld (23), k>=2."""
    assert k >= 2
    out = 1
    for i in range(1, k - 1):
        out *= odd_double_factorial(i)
    return out


def run(limit: int) -> dict:
    assert limit >= 6
    checks: list[dict] = []

    # Functional equation at positive integers.
    for n in range(1, limit):
        lhs = barnes_g_nat(n + 1)
        rhs = factorial(n - 1) * barnes_g_nat(n)
        checks.append({"family": "integer_recurrence", "n": n, "ok": lhs == rhs})

    # Hyperfactorial relation G(n) H(n-1) = ((n-1)!)^(n-1).
    for n in range(1, limit + 1):
        lhs = barnes_g_nat(n) * hyperfactorial(n - 1)
        rhs = factorial(n - 1) ** (n - 1)
        checks.append({"family": "hyperfactorial_relation", "n": n, "ok": lhs == rhs})

    # Finite Gamma-product identity at positive integer arguments.
    # prod_{i=1}^m Gamma(k+i) = G(k+m+1)/G(k+1), k>=1.
    for k in range(1, min(limit, 10)):
        for m in range(0, min(limit - k, 9)):
            lhs = 1
            for i in range(1, m + 1):
                lhs *= factorial(k + i - 1)
            rhs_num = barnes_g_nat(k + m + 1)
            rhs_den = barnes_g_nat(k + 1)
            checks.append({
                "family": "finite_gamma_product", "k": k, "m": m,
                "ok": lhs * rhs_den == rhs_num,
            })

    # The coefficient in the odd half-integer formula is integral and has
    # the primitive recurrence c_{k+1}=c_k(2k-3)!!.
    for k in range(2, limit):
        ck = half_coefficient(k)
        cnext = half_coefficient(k + 1)
        checks.append({
            "family": "half_coefficient_recurrence", "k": k,
            "ok": cnext == ck * odd_double_factorial(k - 1),
            "c_k": str(ck),
        })

    # The displayed initial sequence from MathWorld, n=0,...,11.
    expected = [0, 1, 1, 1, 2, 12, 288, 34560, 24883200,
                125411328000, 5056584744960000, 1834933472251084800000]
    actual = [0] + [barnes_g_nat(n) for n in range(1, len(expected))]
    checks.append({"family": "initial_sequence", "ok": actual == expected,
                   "actual": [str(x) for x in actual]})

    failed = [c for c in checks if not c["ok"]]
    return {
        "checker": "verify_finite_core.py",
        "arithmetic": "exact Python integers only",
        "limit": limit,
        "checks": len(checks),
        "failures": len(failed),
        "all_ok": not failed,
        "failed_examples": failed[:10],
        "sample_values": {
            "G(1..12)": [str(barnes_g_nat(n)) for n in range(1, 13)],
            "c_2..c_10": [str(half_coefficient(k)) for k in range(2, 11)],
        },
    }


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--limit", type=int, default=24)
    ap.add_argument("--output", type=Path)
    ns = ap.parse_args()
    result = run(ns.limit)
    text = json.dumps(result, indent=2, sort_keys=True) + "\n"
    if ns.output:
        ns.output.parent.mkdir(parents=True, exist_ok=True)
        ns.output.write_text(text, encoding="utf-8")
    print(text, end="")
    raise SystemExit(0 if result["all_ok"] else 1)


if __name__ == "__main__":
    main()
