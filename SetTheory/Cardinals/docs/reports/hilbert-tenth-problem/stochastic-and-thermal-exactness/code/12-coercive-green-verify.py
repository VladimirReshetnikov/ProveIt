"""Reproducible exact checks for the companion manuscript (stdlib only).

These checks supplement, and do not replace, the proofs. They never infer
nonhalting from an exhausted simulation horizon.
"""
from __future__ import annotations
from collections import Counter, defaultdict
from dataclasses import FrozenInstanceError
from fractions import Fraction
from itertools import product
from math import gcd
from pathlib import Path
import argparse
import json
import random
import sys

from green_machine import (Config, Program, apply_l, certificate, check_certificate,
    continuants, exact_rational_level, export_example, green_interval,
    polynomial_transport, rational_level_index, rows_value, run, slice_rows)

CHECKS: Counter[str] = Counter()


def check(condition: bool, category: str) -> None:
    CHECKS[category] += 1
    if not condition:
        raise AssertionError(f"check failed: {category}, number {CHECKS[category]}")


def rejects(fn, category: str = "invalid_input_rejection") -> None:
    try:
        fn()
    except (ValueError, TypeError, FrozenInstanceError):
        check(True, category)
    else:
        check(False, category)


def graph_transport(p: Program, v: dict[Config, int], adjoint: bool) -> dict[Config, int]:
    out = defaultdict(int)
    for c, x in v.items():
        dest = p.predecessor(c) if adjoint else p.step(c)
        if dest is not None:
            out[dest] += x
    return {c: x for c, x in out.items() if x}


def gaussian_solve(alpha: int, n: int) -> list[Fraction]:
    """Independent exact elimination; no continuant formula is used here."""
    rows = [[Fraction(alpha if i == j else -1 if abs(i-j) == 1 else 0)
             for j in range(n)] + [Fraction(i == 0)] for i in range(n)]
    for k in range(n):
        pivot = rows[k][k]
        if not pivot:
            raise AssertionError("unexpected zero pivot")
        rows[k] = [v / pivot for v in rows[k]]
        for i in range(n):
            if i != k:
                factor = rows[i][k]
                rows[i] = [x-factor*y for x, y in zip(rows[i], rows[k])]
    return [row[-1] for row in rows]


def check_graphs(rng: random.Random) -> None:
    programs = [Program((("test", 0, 0, 1), ("halt",))),
                Program((("inc", 0, 1), ("test", 1, 0, 2), ("halt",)))]
    for _ in range(28):
        n = rng.randrange(2, 7)
        table = []
        for j in range(n):
            op = rng.choice(("inc", "test", "halt"))
            if op == "halt":
                table.append((op,))
            elif op == "inc":
                table.append((op, rng.randrange(2), rng.randrange(n)))
            else:
                table.append((op, rng.randrange(2), rng.randrange(n), rng.randrange(n)))
        programs.append(Program(tuple(table)))
    for p in programs:
        grid = [Config(s, a, b, h) for s in range(len(p.instructions))
                for a in range(3) for b in range(3) for h in range(9)]
        for c in grid:
            succ, pred = p.step(c), p.predecessor(c)
            check(len(p.neighbors(c)) <= 2, "graph_degree")
            check(pred is None or pred.history < c.history, "backward_history")
            check(succ is None or succ.history > c.history, "forward_history")
            check(succ is None or p.predecessor(succ) == c, "successor_roundtrip")
            check(pred is None or p.step(pred) == c, "predecessor_roundtrip")
            if c.history == 0:
                check(pred is None, "empty_history_is_root")
        for _ in range(60):
            v = {c: rng.randrange(-9, 10) for c in rng.sample(grid, min(11, len(grid)))}
            for adjoint in (False, True):
                check(polynomial_transport(p, v, adjoint) == graph_transport(p, v, adjoint),
                      "independent_polynomial_graph_agreement")
            a = polynomial_transport(p, v)
            b = polynomial_transport(p, v, True)
            keys = set(v) | set(a) | set(b)
            expected = {c: 3*v.get(c, 0)-a.get(c, 0)-b.get(c, 0) for c in keys}
            expected = {c: x for c, x in expected.items() if x}
            check(apply_l(p, 3, v) == expected, "independent_coercive_rows")
        for s in range(len(p.instructions)):
            for a in range(4):
                for b in range(3):
                    source = Config(s, a, b)
                    trace, halted = run(p, source, 20)
                    # No conclusion about nonhalting is made in the other branch.
                    if halted:
                        q, v = certificate(p, source, 3, 20)
                        check(check_certificate(p, source, 3, q, v), "halting_certificate")
                        check(all(x > 0 for x in v.values()), "positive_certificate")
                        check(sum(p.halted(c) for c in v) == 1, "one_terminal")
                        check(gcd(q, v[source]) == 1, "primitive_certificate")
                        check(exact_rational_level(p, source, 3, Fraction(v[source], q)),
                              "rational_level_recovery")
                        check(not check_certificate(p, source, 3, q+1, v), "q_tamper_rejected")
                        bad = dict(v)
                        bad[trace[-1]] += 1
                        check(not check_certificate(p, source, 3, q, bad), "terminal_tamper_rejected")
                        wrong_source = Config(s, a+1, b)
                        check(not check_certificate(p, wrong_source, 3, q, v), "source_tamper_rejected")


def check_continuants() -> None:
    for alpha in range(3, 31):
        ds = continuants(alpha, 100)
        for n in range(1, 101):
            q, p = ds[n], ds[n-1]
            check(q*q + p*p-alpha*p*q == 1, "pell_identity")
            check(gcd(p, q) == 1, "continuant_coprimality")
            check(q > (alpha-1)*p, "continuant_growth")
            check(rational_level_index(alpha, Fraction(p, q)) == n, "pell_descent")
    for alpha in range(3, 9):
        expected = {Fraction(continuants(alpha, n)[n-1], continuants(alpha, n)[n]): n
                    for n in range(1, 15)}
        for q in range(1, 101):
            for p in range(0, q):
                v = Fraction(p, q)
                check(rational_level_index(alpha, v) == expected.get(v), "exhaustive_rational_spectrum")
    for alpha in range(3, 10):
        for n in range(1, 13):
            independent = gaussian_solve(alpha, n)
            ds = continuants(alpha, n)
            for j in range(n):
                check(independent[j] == Fraction(ds[n-1-j], ds[n]), "independent_gaussian_inverse")
    fib = [0, 1]
    for _ in range(204):
        fib.append(fib[-1]+fib[-2])
    for n, d in enumerate(continuants(3, 100)):
        check(d == fib[2*n+2], "fibonacci_specialization")


def check_intervals_and_slices() -> None:
    countdown = Program((("test", 0, 0, 1), ("halt",)))
    infinite = Program((("inc", 0, 0),))
    for alpha in (3, 4, 5, 11, 101):
        for count in range(35):
            source = Config(0, count, 0)
            q, vector = certificate(countdown, source, alpha, count+1)
            exact = Fraction(vector[source], q)
            previous = (Fraction(0), Fraction(1, 2))
            for bits in (0, 1, 2, 3, 7, 12, 27, 70, 110):
                lo, hi = green_interval(countdown, source, alpha, bits)
                check(lo <= exact <= hi, "halting_interval_enclosure")
                check(hi-lo <= Fraction(1, 2**bits), "interval_width")
                check(previous[0] <= lo <= hi <= previous[1], "nested_intervals")
                previous = lo, hi
        for bits in range(90):
            lo, hi = green_interval(infinite, Config(0, 0, 0), alpha, bits)
            check(0 < lo < hi <= Fraction(1, 2), "ray_interval_range")
            # t^2-alpha*t+1 is strictly decreasing on [0,1/2].
            check(lo*lo-alpha*lo+1 > 0 > hi*hi-alpha*hi+1, "exact_irrational_enclosure")
            check(hi-lo <= Fraction(1, 2**bits), "ray_interval_width")
    for count in range(12):
        source = Config(0, count, 0)
        trace, _ = run(countdown, source, count+1)
        q, v = certificate(countdown, source, 3, count+1)
        # Additional disconnected source data must be forced to zero.
        extras = [Config(1, 99, 99, 0)]
        support = trace + extras
        names, rows = slice_rows(countdown, source, 3, support)
        values = {**{f"u{i}": v.get(c, 0) for i, c in enumerate(support)}, "q": q}
        check(rows_value(names, rows, values) == 0, "ordinary_quadratic_zero")
        check(len(rows) <= 3*len(support)+2, "residual_count_bound")
        for name in names:
            changed = dict(values)
            changed[name] += 1
            check(rows_value(names, rows, changed) > 0, "quadratic_tamper_rejected")
    # Reject a formally solved finite truncation of an infinite path, even
    # when an unrelated terminal is added to satisfy the normalization.
    mixed = Program((("inc", 0, 0), ("halt",)))
    source = Config(0, 0, 0)
    for length in range(1, 12):
        trace, _ = run(mixed, source, length-1)
        ds = continuants(3, length)
        fake = {v: ds[length-1-i] for i, v in enumerate(trace)}
        fake[Config(1, 0, 0)] = 1
        names, rows = slice_rows(mixed, source, 3, list(fake))
        assignment = {**{f"u{i}": fake[c] for i, c in enumerate(fake)}, "q": ds[length]}
        check(rows_value(names, rows, assignment) > 0, "exterior_rows_reject_truncation")
        end_successor = mixed.step(trace[-1])
        check(any(row["vertex"] == end_successor.as_list() for row in rows),
              "exterior_neighbor_is_exported")
    # Exhaust all small assignments on a length-two component and a dummy halt.
    simple = Program((("inc", 0, 1), ("halt",)))
    source = Config(0, 0, 0)
    succ = simple.step(source)
    support = [source, succ, Config(1, 7, 9)]
    names, rows = slice_rows(simple, source, 3, support)
    for vals in product(range(-1, 5), range(-1, 3), range(-1, 3), range(-1, 10)):
        value = rows_value(names, rows, dict(zip(names, vals)))
        check((value == 0) == (vals == (3, 1, 0, 8)), "exhaustive_small_unique_zero")


def check_modular_boundary() -> None:
    mixed = Program((("inc", 0, 0), ("test", 0, 1, 2), ("halt",)))
    source = Config(0, 0, 0)
    for alpha in range(3, 9):
        for modulus in range(2, 45):
            # The state (D_n,D_(n-1)) lies in a finite invertible orbit.
            previous, current = 0, 1
            found = None
            for n in range(1, modulus*modulus+2):
                previous, current = current, (alpha*current-previous) % modulus
                if current == 0:
                    found = n
                    break
            check(found is not None, "modular_singular_path_exists")
            if found == 1:
                dummy = Config(2, 0, 0)
            else:
                # Starting counter n-2 yields n-2 decrements, then a zero step.
                dummy = Config(1, found-2, 0)
            q, v = certificate(mixed, dummy, alpha, found-1)
            check(q % modulus == 0, "modular_continuant_zero")
            reduced = {c: x % modulus for c, x in v.items()}
            check(check_certificate(mixed, source, alpha, 0, reduced, modulus),
                  "modular_false_positive")
            check(not check_certificate(mixed, source, alpha, 0, reduced),
                  "same_false_positive_rejected_over_integers")


def check_validation() -> None:
    for args in ((True, 0, 0), (0, 1.0, 0), (0, -1, 0), (0, 0, False), (0, 0, 0, -1)):
        rejects(lambda args=args: Config(*args))
    for table in ((), (("inc", 0),), (("inc", 2, 0),), (("inc", True, 0),),
                  (("inc", 0, False),), (("test", 0, 0, 4),), (("halt", 1),),
                  (("bogus",),), (("inc", 0, 1),)):
        rejects(lambda table=table: Program(table))
    raw = [["test", 0, 0, 1], ["halt"]]
    p = Program(raw)
    raw[0][2] = 99
    raw.append(["halt"])
    check(p.instructions == (("test", 0, 0, 1), ("halt",)), "immutable_input_copy")
    rejects(lambda: setattr(p, "base", 77), "frozen_program")
    source = Config(0, 0, 0)
    for alpha in (2, 3.0, True, -3):
        rejects(lambda alpha=alpha: apply_l(p, alpha, {}))
    rejects(lambda: check_certificate(p, Config(0, 0, 0, 1), 3, 1, {}))
    rejects(lambda: apply_l(p, 3, {source: True}))
    rejects(lambda: apply_l(p, 3, {source: 1.0}))
    rejects(lambda: apply_l(p, 3, {Config(8, 0, 0): 1}))
    rejects(lambda: slice_rows(p, source, 3, [source, source]))
    rejects(lambda: rational_level_index(3, 0.25))
    rejects(lambda: green_interval(p, source, 3, -1))
    try:
        certificate(Program((("inc", 0, 0),)), source, 3, 10)
    except TimeoutError:
        check(True, "horizon_failure_is_not_nonhalting_decision")
    else:
        check(False, "horizon_failure_is_not_nonhalting_decision")


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path,
                        default=Path(__file__).resolve().parents[1]/"validation"/"results.json")
    args = parser.parse_args()
    rng = random.Random(20261002)
    check_graphs(rng)
    check_continuants()
    check_intervals_and_slices()
    check_modular_boundary()
    check_validation()
    root = Path(__file__).resolve().parents[1]
    export_example(root / "examples")
    report = {
        "status": "PASS", "seed": 20261002,
        "python": sys.version.split()[0], "checks": sum(CHECKS.values()),
        "categories": dict(sorted(CHECKS.items())),
        "dependencies": "Python standard library only",
        "scope": "Finite exact validation; not a formal proof or a test of all machines.",
        "independent_checks": ["monomial transport vs graph adjacency",
            "rational Gaussian elimination vs continuants", "exhaustive rational Pell spectrum",
            "exhaustive small quadratic zero set", "integer rejection vs modular acceptance"],
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(report, indent=2)+"\n")
    print(json.dumps(report, indent=2))


if __name__ == "__main__":
    main()
