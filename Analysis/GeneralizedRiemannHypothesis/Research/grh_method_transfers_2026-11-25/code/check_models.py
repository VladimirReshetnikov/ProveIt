#!/usr/bin/env python3
"""Exact finite-model checks for the report. Python standard library only.

These verify finite algebra and rational inequalities, not an infinite RH bound.
"""
from fractions import Fraction as F
from itertools import permutations
from pathlib import Path
import json
import math

ROOT = Path(__file__).resolve().parents[1]


def parity(p):
    return -1 if sum(p[i] > p[j] for i in range(len(p))
                    for j in range(i + 1, len(p))) % 2 else 1


def group_checks():
    rows = []
    for n in range(3, 7):
        group = list(permutations(range(n)))
        chi = lambda p: sum(i == v for i, v in enumerate(p)) - 1
        means = {s: F(sum(chi(p) for p in group if parity(p) == s),
                      sum(parity(p) == s for p in group)) for s in (-1, 1)}
        norm = F(sum(chi(p) ** 2 for p in group), len(group))
        assert means == {-1: F(0), 1: F(0)} and norm == 1
        for a, b in [(F(0), F(0)), (F(2), F(-1)), (F(1, 3), F(7, 5))]:
            mse = sum((F(chi(p)) - (a if parity(p) == 1 else b)) ** 2
                      for p in group) / len(group)
            assert mse == 1 + (a * a + b * b) / 2
        rows.append({"group": f"S{n}", "order": len(group),
                     "dimension": n - 1, "coset_means": [0, 0],
                     "norm_squared": str(norm)})
    return rows


def convexity_checks():
    # H(t)=sum a_j (1/j-t)_+ is convex. These are exact rational tests
    # across many knots, including intervals containing multiple knots.
    weights = {j: F((j * j + 11 * j + 7) % 17, j + 1) for j in range(2, 90)}
    H = lambda t: sum(a * max(F(1, j) - t, F(0)) for j, a in weights.items())
    count = 0
    for k in range(2, 30):
        u, v = F(1, k + 15), F(1, k)
        for j in range(1, 10):
            lam = F(j, 10)
            t = (1 - lam) * u + lam * v
            assert H(t) <= (1 - lam) * H(u) + lam * H(v)
            count += 1
    # Exact preservation of the square-root envelope on reciprocal grids:
    # ((1-lambda)sqrt(u)+lambda sqrt(v))^2 <= (1-lambda)u+lambda v.
    for n in range(1, 100):
        u, v = F(1, (n + 1) ** 4), F(1, n ** 4)
        for j in range(11):
            lam = F(j, 10)
            lhs = ((1 - lam) / (n + 1) ** 2 + lam / n ** 2) ** 2
            assert lhs <= (1 - lam) * u + lam * v
            count += 1
    return {"exact_rational_cases": count}


def ramification_checks():
    rows = []
    count = 0
    for ell in (2, 3, 5, 7):
        for m in (1, 2, 5, 10, 30, 100):
            k = 0
            while ell ** (k + 1) <= m:
                k += 1
            for h in range(k + 1, k + 5):
                e = ell ** (h - 1) * (ell - 1)
                local = []
                for j in range(1, m + 1):
                    z, vj = j, 0
                    while z % ell == 0:
                        z //= ell
                        vj += 1
                    local.append(F(ell ** vj, e))
                assert max(local) == F(ell ** k, e)
                budget = 2 * max(local)
                assert budget * e == 2 * ell ** k
                assert budget >= F(2, e)
                count += 1
        for h in (1, 2, 4, 8):
            e = ell ** (h - 1) * (ell - 1)
            rows.append({"ell": ell, "h": h, "e": e,
                         "nonzero_module_normalized_length": str(F(1, e))})
    return {"exact_parameter_cases": count, "nonzero_module_examples": rows}


def main():
    out = {"status": "PASS", "scope": "Exact finite algebra only; no conjecture verification",
           "periodic_projection": group_checks(), "convexity": convexity_checks(),
           "ramification": ramification_checks()}
    (ROOT / "results").mkdir(exist_ok=True)
    (ROOT / "results" / "exact_checks.json").write_text(json.dumps(out, indent=2) + "\n")
    print(json.dumps({"status": out["status"], "groups": 4,
                      "rational_checks": out["convexity"]["exact_rational_cases"],
                      "ramification_cases": out["ramification"]["exact_parameter_cases"]}))


if __name__ == "__main__":
    main()
