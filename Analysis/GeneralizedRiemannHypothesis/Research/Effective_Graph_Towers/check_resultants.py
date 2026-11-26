#!/usr/bin/env python3
"""Recompute the five output records and compare small random inputs with exact norms."""
import itertools
import json
import random
from pathlib import Path

import sympy as sp

from tower_automaton import Compiler, exact_law, valuation


def check_records():
    records = json.loads(Path(__file__).with_name("dv_examples.json").read_text())
    for record in records:
        compiler = Compiler(record["p"], record["terms"])
        for key, value in exact_law(compiler, trees=1).items():
            assert record[key] == value, (record["example"], key)
        assert compiler.levels(10, trees=1) == record["levels_0_through_10"]


def direct_shell(p, h, dimension, terms):
    x = sp.Symbol("x")
    q = p**h
    phi = sp.cyclotomic_poly(q, x)
    total = 0
    for pivot in range(dimension):
        options = [range(0, q, p) if i < pivot else ([1] if i == pivot else range(q))
                   for i in range(dimension)]
        for direction in itertools.product(*options):
            f = sum(c*x**(sum(a*u for a, u in zip(exp, direction)) % q)
                    for c, exp in terms)
            norm = sp.resultant(phi, f, x)
            if norm:
                total += valuation(norm, p)
    return total


def check_norms():
    rng = random.Random(17)
    checks = 0
    for p in (2, 3, 5):
        for dimension in (1, 2, 3):
            for _ in range(6):
                terms = [(rng.randint(-5, 7), [rng.randint(-4, 4) for _ in range(dimension)])
                         for _ in range(6)]
                h_max = (3 if p == 2 else 2) if dimension < 3 else 1
                levels = Compiler(p, terms, omit_zeros=True).levels(h_max)
                for h in range(1, h_max+1):
                    expected = direct_shell(p, h, dimension, terms)
                    assert levels[h]-levels[h-1] == expected, (p, dimension, h, terms)
                    checks += 1
    print(f"Verified all five output records and {checks} independent resultant comparisons.")


if __name__ == "__main__":
    check_records()
    check_norms()
