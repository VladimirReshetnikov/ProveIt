#!/usr/bin/env python3
"""Reproduce all finite checks and exact exported examples for the article.

These tests do not decide infinite recurrence or establish literature priority.
Run from any directory: python code/verify.py
"""
from __future__ import annotations
from itertools import product
from fractions import Fraction
from pathlib import Path
import csv
import json
import random
import time
from quadratic_dynamics import (Machine, Edge, countdown_machine, prefix_statistics,
                                deadline_feasible, stack_encode, stack_push, stack_pop)

ROOT = Path(__file__).resolve().parent.parent
DATA = ROOT / "data"
DATA.mkdir(exist_ok=True)


def main() -> None:
    if not __debug__:
        raise RuntimeError("Run verification without -O or PYTHONOPTIMIZE")
    started = time.perf_counter()
    rng = random.Random(20260930)
    # Full natural-coordinate box for a machine containing all nontrivial guards.
    small = Machine(1, "q", [Edge("q", "r", "inc", 0), Edge("r", "q", "dec", 0),
                              Edge("r", "h", "zero", 0)], {"r"})
    p2, p4, names = small.compile()
    states = list(product(range(3), repeat=small.dimension))
    tested = 0
    zero_pairs = 0
    for old in states:
        actual = set(small.successors(old))
        for new in states:
            q2 = p2.evaluate(old + new)
            q4 = p4.evaluate(old + new)
            assert q2 >= 0 and q4 >= 0
            expected = new in actual
            assert (q2 == 0) == expected == (q4 == 0)
            zero_pairs += expected
            tested += 1
    # Independent residual-vs-expanded-polynomial checks, including rationals.
    for _ in range(1000):
        old = tuple(Fraction(rng.randrange(9), rng.randrange(1,6)) for _ in range(small.dimension))
        new = tuple(Fraction(rng.randrange(9), rng.randrange(1,6)) for _ in range(small.dimension))
        assert p2.evaluate(old + new) == small.direct_energy(old, new) >= 0
        assert p4.evaluate(old + new) == small.direct_energy(old, new, True) >= 0
    # Quartic is globally nonnegative, including outside the nonnegative orthant.
    for _ in range(1000):
        old = tuple(rng.randrange(-4,5) for _ in range(small.dimension))
        new = tuple(rng.randrange(-4,5) for _ in range(small.dimension))
        assert p4.evaluate(old + new) == small.direct_energy(old, new, True) >= 0
    # Check coefficient height and degree for independent randomly generated machines.
    heights = []
    for _ in range(300):
        d = rng.randrange(1,5)
        labels = [f"q{i}" for i in range(rng.randrange(1,8))]
        edges = []
        for q in labels:
            for _ in range(rng.randrange(3)):
                kind = rng.choice(["inc", "dec", "zero", "nop"])
                edges.append(Edge(q, rng.choice(labels), kind,
                                  None if kind == "nop" else rng.randrange(d)))
        machine = Machine(d, labels[0], edges)
        a, b, _ = machine.compile()
        assert a.degree <= 2 and b.degree <= 4
        assert a.height <= 6 and b.height <= 6
        heights.append(max(a.height, b.height))
    # A syntactic coefficient of 6 really occurs in this encoding.
    tight = Machine(1, "q", [Edge("q", "r", "inc", 0), Edge("q", "s", "inc", 0)])
    a, b, _ = tight.compile()
    assert a.height == b.height == 6
    # Planar stack coding is exact, including all empty-stack boundaries.
    stack_tests = 0
    for length in range(10):
        for word in product((0,1), repeat=length):
            value = stack_encode(word)
            assert 0 <= value < 1
            for symbol in (0,1):
                assert stack_push(value, symbol) == stack_encode((symbol,) + word)
                assert stack_pop(stack_push(value, symbol)) == (symbol, value)
                stack_tests += 1
            if word:
                assert stack_pop(value) == (word[0], stack_encode(word[1:]))
    # The compactness counterexample and simultaneously enforced deadlines.
    M = countdown_machine()
    p2, p4, names = M.compile()
    stats = prefix_statistics(M, 100)
    assert all(stats["maximum_visits_at_exact_horizon"][4*k] >= k for k in range(1,26))
    feasible = [deadline_feasible(M, [4*j for j in range(1,k+1)]) for k in range(1,9)]
    assert feasible == [True] + [False]*7
    export = {"machine": M.description(), "quadratic": p2.as_json(names),
              "quartic": p4.as_json(names)}
    (DATA / "countdown_polynomials.json").write_text(json.dumps(export, indent=2) + "\n")
    with (DATA / "countdown_prefixes.csv").open("w", newline="") as f:
        writer = csv.writer(f)
        writer.writerow(["T", "paths_of_length_T", "maximum_marked_visits"])
        for T in range(101):
            writer.writerow([T, stats["number_of_length_T_paths"][T],
                             stats["maximum_visits_at_exact_horizon"][T]])
    report = {"status": "PASS", "seed": 20260930,
              "exhaustive_state_pairs": tested, "zero_pairs_in_box": zero_pairs,
              "rational_residual_checks": 1000, "signed_quartic_checks": 1000,
              "random_machine_coefficient_checks": len(heights),
              "largest_observed_coefficient_height": max(heights),
              "exact_stack_push_pop_checks": stack_tests,
              "countdown_dimension": M.dimension,
              "countdown_quadratic_terms": len(p2.terms),
              "countdown_quartic_terms": len(p4.terms),
              "countdown_quadratic_height": p2.height,
              "countdown_quartic_height": p4.height,
              "deadlines_4k_feasible_K_1_through_8": feasible,
              "elapsed_seconds": round(time.perf_counter()-started,3),
              "scope": "Finite exact checks only; not a formal proof of infinite-run theorems."}
    (DATA / "verification_results.json").write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps(report, indent=2))

if __name__ == "__main__":
    main()
