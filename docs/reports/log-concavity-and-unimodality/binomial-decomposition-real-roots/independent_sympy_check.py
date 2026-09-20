#!/usr/bin/env python3
"""Optional independent symbolic check (requires SymPy).

This script does not import verify.py.  It checks the complete cubic domain
by exact Sturm counts and checks the saved canonical outputs with a separate
linear-search expansion.  No approximate roots are used.
"""
from __future__ import annotations

import csv
from math import comb
from pathlib import Path

try:
    import sympy as sp
except ImportError as exc:
    raise SystemExit("This optional check requires SymPy; verify.py does not.") from exc

x = sp.Symbol("x")
base = Path(__file__).resolve().parent


def check(condition: bool, message: str) -> None:
    if not condition:
        raise AssertionError(message)


def poly(coefficients):
    return sp.Poly(sum(int(c)*x**i for i, c in enumerate(coefficients)), x)


def all_real_sturm(coefficients):
    p = poly(coefficients).sqf_part()
    return p.degree() <= 0 or p.count_roots(-sp.oo, sp.oo) == p.degree()


def split_linear(coefficients):
    g, h = [1], []
    for k, value in enumerate(coefficients[1:], 1):
        r, kap = 0, 0
        for j in range(k, 0, -1):
            if value == 0:
                break
            a = j
            while comb(a + 1, j) <= value:
                a += 1
            value -= comb(a, j)
            r += comb(a - 1, j)
            kap += comb(a - 1, j - 1)
        check(value == 0, "remainder did not vanish")
        g.append(r)
        h.append(kap)
    return g, h


with (base / "data/cubics_a_le8.csv").open(newline="", encoding="utf-8") as stream:
    rows = list(csv.DictReader(stream))
saved = {(int(row["a"]), int(row["b"]), int(row["c"])): row for row in rows}
retained = set()
candidate_count = output_checks = 0
for a in range(3, 9):
    for b in range(3, a*a // 3 + 1):
        for c in range(1, a*a*a // 27 + 1):
            candidate_count += 1
            f = [1, a, b, c]
            is_real = all_real_sturm(f)
            exact_discriminant = int(poly(f).discriminant())
            check(is_real == (exact_discriminant >= 0), "Sturm/discriminant mismatch")
            if not is_real:
                continue
            retained.add((a, b, c))
            row = saved[(a, b, c)]
            check(exact_discriminant == int(row["F_discriminant"]), "input disc")
            g, h = split_linear(f)
            check(g == [1] + [int(row[f"g{i}"]) for i in range(1, 4)], "G split")
            check(h == [1] + [int(row[f"h{i}"]) for i in range(1, 3)], "H split")
            check(all_real_sturm(g) == (row["G_all_real"] == "True"), "G roots")
            check(all_real_sturm(h) == (row["H_all_real"] == "True"), "H roots")
            output_checks += 2
check(retained == set(saved), "CSV omissions or extra rows")
check(candidate_count == 621 and len(retained) == 124, "domain count mismatch")
print(f"SymPy version: {sp.__version__}")
print(f"Exact Sturm checks: {candidate_count} inputs, {output_checks} outputs")
print("All 124 retained cubic triples and both canonical outputs agree")
print("INDEPENDENT SYMBOLIC CHECK PASSED")
