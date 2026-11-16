#!/usr/bin/env python3
"""Exact rational coefficient checks used by the Meijer-G report.

These checks are regression evidence.  They verify finite coefficient
identities, not the universal analytic theorems or object-iPRA derivations.
"""
from __future__ import annotations

from fractions import Fraction
from math import factorial, comb
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / "evidence" / "exact_coefficients.json"


def rising(a: Fraction, k: int) -> Fraction:
    out = Fraction(1)
    for j in range(k):
        out *= a + j
    return out


def hyp_coeff(upper: list[Fraction], lower: list[Fraction], k: int) -> Fraction:
    out = Fraction(1, factorial(k))
    for a in upper:
        out *= rising(a, k)
    for b in lower:
        out /= rising(b, k)
    return out


def check(name: str, lhs: Fraction, rhs: Fraction, k: int, records: list[dict]) -> None:
    ok = lhs == rhs
    records.append({
        "name": name,
        "k": k,
        "lhs": str(lhs),
        "rhs": str(rhs),
        "ok": ok,
    })
    if not ok:
        raise AssertionError(f"{name} failed at k={k}: {lhs} != {rhs}")


def main() -> None:
    records: list[dict] = []
    for k in range(0, 25):
        # Gamma duplication in rational form.
        check("half_pochhammer", rising(Fraction(1, 2), k),
              Fraction(factorial(2*k), 4**k * factorial(k)), k, records)
        check("three_half_pochhammer", rising(Fraction(3, 2), k),
              Fraction(factorial(2*k+1), 4**k * factorial(k)), k, records)

        # Hypergeometric reductions used in elementary cases.
        check("log_2F1_coefficient",
              hyp_coeff([Fraction(1), Fraction(1)], [Fraction(2)], k),
              Fraction(1, k+1), k, records)
        check("rational_2F1_coefficient",
              hyp_coeff([Fraction(1), Fraction(1)], [Fraction(1)], k),
              Fraction(1), k, records)
        check("arctan_2F1_coefficient",
              hyp_coeff([Fraction(1), Fraction(1, 2)], [Fraction(3, 2)], k),
              Fraction(1, 2*k+1), k, records)
        check("arcsin_2F1_coefficient",
              hyp_coeff([Fraction(1, 2), Fraction(1, 2)], [Fraction(3, 2)], k),
              Fraction(comb(2*k, k), 4**k * (2*k+1)), k, records)

        # Bessel J coefficient after the prefactor (x/2)^nu / Gamma(nu+1),
        # checked at a rational sample nu=3/2.
        nu = Fraction(3, 2)
        check("bessel_J_0F1_ratio",
              hyp_coeff([], [nu + 1], k),
              Fraction(1, factorial(k)) / rising(nu + 1, k), k, records)

        # Incomplete-gamma and Lerch Pochhammer quotients.
        for a in (Fraction(2, 3), Fraction(5, 4), Fraction(7, 3)):
            check(f"poch_ratio_a={a}",
                  rising(a, k) / rising(a + 1, k),
                  a / (a + k), k, records)
            for n in range(0, 5):
                pos = (rising(a, k) / rising(a + 1, k)) ** n / (a ** n)
                neg = (a ** n) * (rising(a + 1, k) / rising(a, k)) ** n
                check(f"lerch_positive_a={a}_n={n}", pos,
                      Fraction(1, 1) / ((a + k) ** n), k, records)
                check(f"lerch_negative_a={a}_n={n}", neg,
                      (a + k) ** n, k, records)

    summary = {
        "checks": len(records),
        "all_passed": all(r["ok"] for r in records),
        "max_k": 24,
        "records": records,
    }
    OUT.write_text(json.dumps(summary, indent=2), encoding="utf-8")
    print(f"wrote {OUT}")
    print(f"{summary['checks']} exact coefficient checks passed")


if __name__ == "__main__":
    main()
