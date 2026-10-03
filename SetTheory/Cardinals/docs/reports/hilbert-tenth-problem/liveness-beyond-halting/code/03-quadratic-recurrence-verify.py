#!/usr/bin/env python3
"""Reproducible exact finite checks, not a proof of infinite-run theorems."""
from __future__ import annotations
from itertools import product
from pathlib import Path
import json
import random
import sys
from quadratic_compiler import Edge, Machine, evaluate

ROOT = Path(__file__).resolve().parents[1]
COUNTS = {"local_equivalence_checks": 0, "sparse_vs_factored_checks": 0,
          "valid_transitions_checked": 0, "coefficient_tables_checked": 0,
          "finite_visit_paths_checked": 0, "linear_fiber_examples_checked": 0}


def assert_local(machine: Machine, source: tuple[int, ...],
                 target: tuple[int, ...]) -> None:
    direct = target in machine.successors(source)
    energy = machine.energy(source, target)
    assert energy >= 0
    assert (energy == 0) == direct, (machine, source, target, energy, direct)
    COUNTS["local_equivalence_checks"] += 1


def check_coefficients(machine: Machine) -> None:
    p = machine.compile()
    assert max(map(len, p), default=0) <= 2
    assert max(map(abs, p.values()), default=0) <= 8
    q, r, d = len(machine.controls), machine.counters, machine.dimension
    ignored = set(range(q+r, d))
    assert all(not (set(monomial) & ignored) for monomial in p)
    COUNTS["coefficient_tables_checked"] += 1


def test_exhaustive_small() -> None:
    # Each instruction kind and endpoint tested, including no edges, and
    # every target selector value 0,1,2 in the two-edge machines below.
    for kinds in product(("inc", "dec", "zero", "nop"), repeat=2):
        machine = Machine(("A", "B"), 1,
            tuple(Edge(0, i, kind, None if kind == "nop" else 0)
                  for i, kind in enumerate(kinds)))
        check_coefficients(machine)
        for p in product(range(3), repeat=2):
            for x in range(4):
                source = p + (x, 2, 1)  # arbitrary OLD tags are intentionally ignored
                for pp in product(range(3), repeat=2):
                    for xx in range(5):
                        for ee in product(range(3), repeat=2):
                            assert_local(machine, source, pp + (xx,) + ee)
    empty = Machine(("A",), 1, ())
    check_coefficients(empty)
    for s in product(range(3), repeat=2):
        for t in product(range(3), repeat=2):
            assert_local(empty, s, t)


def test_random(seed: int = 20260930) -> None:
    rng = random.Random(seed)
    for _ in range(150):
        q, r = rng.randint(1, 4), rng.randint(1, 3)
        edges = []
        for control in range(q):
            for _ in range(rng.randint(0, 2)):
                kind = rng.choice(("inc", "dec", "zero", "nop"))
                edges.append(Edge(control, rng.randrange(q), kind,
                                  None if kind == "nop" else rng.randrange(r)))
        machine = Machine(tuple(f"Q{i}" for i in range(q)), r, tuple(edges))
        poly = machine.compile()
        check_coefficients(machine)
        for _ in range(50):
            s = machine.state(rng.randrange(q), (rng.randrange(6) for _ in range(r)))
            # Check every legal successor, not merely random nearly-always-nonzero tuples.
            succ = machine.successors(s)
            assert len(succ) <= 2 and len(succ) == len(set(succ))
            for t in succ:
                assert_local(machine, s, t)
                assert evaluate(poly, s+t) == 0
                COUNTS["valid_transitions_checked"] += 1
                COUNTS["sparse_vs_factored_checks"] += 1
                # Mutate each active target coordinate in turn.
                for j in range(machine.dimension):
                    bad = list(t)
                    bad[j] += 1
                    assert_local(machine, s, tuple(bad))
            for _ in range(3):
                s2 = tuple(rng.randrange(3) for _ in range(machine.dimension))
                t2 = tuple(rng.randrange(3) for _ in range(machine.dimension))
                assert_local(machine, s2, t2)
                assert evaluate(poly, s2+t2) == machine.energy(s2, t2)
                COUNTS["sparse_vs_factored_checks"] += 1


def test_examples() -> dict:
    machine = Machine.from_dict(json.loads((ROOT/"examples/finite_visits.json").read_text()))
    machine8 = Machine.from_dict(json.loads((ROOT/"examples/height_eight.json").read_text()))
    for m in (machine, machine8):
        check_coefficients(m)
    p8 = machine8.compile()
    d = machine8.dimension
    assert p8[(d+2, d+3)] == 8  # target selectors h0_next*h1_next
    # Parallel INC edges lead to different tagged targets.
    assert len(set(machine8.successors(machine8.state(0, (0,))))) == 2
    records = []
    for n in range(41):
        s = machine.state(0, (0,))
        run = [s]
        labels = [0]*n + [1] + [2]*n + [3] + [4]*3
        for a in labels:
            nexts = machine.successors(s)
            t = next(t for t in nexts if t[4+a] == 1)
            assert_local(machine, s, t)
            s = t
            run.append(s)
        visits = sum(machine.marked_state(s) for s in run[1:])
        assert visits == n+1
        assert s[:3] == (0, 0, 1)
        COUNTS["finite_visit_paths_checked"] += 1
        if n in (0, 1, 2, 5):
            records.append({"guessed_n": n, "visits": visits,
                            "states": [list(s) for s in run]})
    (ROOT/"examples/finite_visits_polynomial.json").write_text(
        json.dumps(machine.export(), indent=2)+"\n")
    (ROOT/"examples/height_eight_polynomial.json").write_text(
        json.dumps(machine8.export(), indent=2)+"\n")
    (ROOT/"examples/sample_runs.json").write_text(json.dumps(records, indent=2)+"\n")
    return {"finite_visits": {k: machine.export()[k] for k in
            ("state_dimension", "polynomial_variables", "degree", "coefficient_height", "monomial_count")},
            "height_eight": {k: machine8.export()[k] for k in
            ("state_dimension", "degree", "coefficient_height", "monomial_count")}}


def test_affine_fiber_growth() -> None:
    # Witness the algebraic construction in the affine minimality proof.
    for b1, b2, u in product(range(1, 5), repeat=3):
        for t in range(1, 10):
            targets = {(b2*u*k, b1*u*(t-k)) for k in range(t+1)}
            assert len(targets) == t+1
            assert all(b1*y1+b2*y2 == u*b1*b2*t for y1, y2 in targets)
            COUNTS["linear_fiber_examples_checked"] += 1


def main() -> None:
    test_exhaustive_small()
    test_random()
    examples = test_examples()
    test_affine_fiber_growth()
    report = {"status": "PASS", "python": sys.version.split()[0],
              "random_seed": 20260930, "checks": COUNTS, "examples": examples,
              "scope": "Exact finite compiler, coefficient, mutation, and example checks only.",
              "not_verified_by_tests": ["Infinite recurrence and hierarchy theorems",
                  "Classical recursive-tree normal form", "A numerical universal interpreter",
                  "Any Lean or Rocq formalization"]}
    (ROOT/"verification/report.json").write_text(json.dumps(report, indent=2)+"\n")
    print(json.dumps(report, indent=2))


if __name__ == "__main__":
    main()
