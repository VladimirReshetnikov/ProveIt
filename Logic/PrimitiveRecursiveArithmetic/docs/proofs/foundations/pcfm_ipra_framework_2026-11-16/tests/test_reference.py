from __future__ import annotations

import random
import sys
import unittest
from fractions import Fraction
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "code"))

from reference import (  # noqa: E402
    And,
    Bot,
    Eq,
    Imp,
    Interval,
    Or,
    backward_viability,
    bounded_all,
    bounded_least,
    check_cubic_trace,
    check_invariant,
    compile_qf,
    complete_bounded_list,
    cubic_bisect,
    cubic_value,
    eval_formula,
    exact_stable_observation,
    run_trace,
    select_viable_path,
)


class BooleanReflectionTests(unittest.TestCase):
    def test_connectives_match_semantics(self) -> None:
        x = lambda e: e[0]
        y = lambda e: e[1]
        zero = lambda e: 0
        one = lambda e: 1

        atoms = [
            Eq(x, y),
            Eq(x, zero),
            Eq(y, one),
            Bot(),
        ]
        formulas = [
            And(atoms[0], Or(atoms[1], atoms[2])),
            Imp(atoms[1], atoms[0]),
            Or(Imp(atoms[0], atoms[1]), And(atoms[2], atoms[0])),
            Imp(And(atoms[0], atoms[1]), Or(atoms[2], Bot())),
        ]

        for env in [(a, b) for a in range(5) for b in range(5)]:
            for phi in formulas:
                bit = compile_qf(phi)(env)
                self.assertIn(bit, (0, 1))
                self.assertEqual(bit == 1, eval_formula(phi, env))

    def test_random_formula_environment(self) -> None:
        rng = random.Random(20261116)
        x = lambda e: e[0]
        y = lambda e: e[1]
        z = lambda e: e[2]
        phi = Imp(
            And(Eq(x, y), Or(Eq(y, z), Eq(x, lambda e: 0))),
            Or(Eq(x, z), Eq(y, lambda e: 0)),
        )
        bit = compile_qf(phi)
        for _ in range(1000):
            env = tuple(rng.randrange(8) for _ in range(3))
            self.assertEqual(bit(env), int(eval_formula(phi, env)))

    def test_bounded_folds_and_least(self) -> None:
        pred = lambda i: int(i != 7)
        self.assertEqual(bounded_all(7, pred), 1)
        self.assertEqual(bounded_all(8, pred), 0)
        witness = lambda i: int((i * i) % 7 == 2)
        expected = next((i for i in range(50) if witness(i)), 50)
        self.assertEqual(bounded_least(50, witness), expected)


class TraceTests(unittest.TestCase):
    def test_ranked_frozen_trace(self) -> None:
        initial = (11, 0)  # rank, halted bit

        def step(_t: int, state: tuple[int, ...]) -> tuple[int, ...]:
            rank, halted = state
            if halted:
                return state
            if rank == 0:
                return (0, 1)
            return (rank - 1, 0)

        trace = run_trace(initial, step, 12)

        def inv(t: int, state: tuple[int, ...]) -> bool:
            rank, halted = state
            return halted == 1 or rank + t <= 11

        self.assertTrue(check_invariant(trace, inv))
        self.assertEqual(trace[-1], (0, 1))


class ViabilityTests(unittest.TestCase):
    def test_selects_least_viable_path(self) -> None:
        bounds = [4, 5, 4, 3]
        good = lambda t, a: (a + t) % 2 == 0 or t == 3
        compatible = lambda _t, a, b: abs(a - b) <= 1
        terminal = lambda a: a == 2
        result = backward_viability(bounds, good, compatible, terminal)
        path = select_viable_path(result)
        self.assertIsNotNone(path)
        assert path is not None
        self.assertEqual(path[-1], 2)
        for t, a in enumerate(path):
            self.assertTrue(good(t, a))
            if t + 1 < len(path):
                self.assertTrue(compatible(t, a, path[t + 1]))

    def test_failure_certificate_shape(self) -> None:
        result = backward_viability(
            [2, 2],
            good=lambda _t, _a: True,
            compatible=lambda _t, _a, _b: False,
            terminal=lambda _a: True,
        )
        self.assertIsNone(select_viable_path(result))
        self.assertEqual(result.viable[0], (False, False))

    def test_exact_stable_observer(self) -> None:
        self.assertEqual(
            exact_stable_observation([7, 3, 11], lambda _w: 42),
            42,
        )
        with self.assertRaises(ValueError):
            exact_stable_observation([1, 2], lambda w: w % 2)


class CubicBisectionTests(unittest.TestCase):
    def test_exact_bracketing_and_width(self) -> None:
        q = Fraction(2)
        trace = cubic_bisect(q, Interval(Fraction(0), Fraction(2)), 40)
        self.assertTrue(check_cubic_trace(q, trace))
        self.assertEqual(trace[-1].width, Fraction(2, 2**40))
        self.assertLessEqual(cubic_value(trace[-1].lo, q), 0)
        self.assertGreaterEqual(cubic_value(trace[-1].hi, q), 0)

    def test_invalid_bracket_rejected(self) -> None:
        with self.assertRaises(ValueError):
            cubic_bisect(Fraction(100), Interval(Fraction(0), Fraction(1)), 2)


class EnumerationTests(unittest.TestCase):
    def test_deduplicated_solution_list(self) -> None:
        candidates = list(range(-10, 11))
        result = complete_bounded_list(
            candidates,
            valid=lambda _x: True,
            equation=lambda x: x * x == 9,
            equivalent=lambda x, y: x == y,
        )
        self.assertEqual(result, (-3, 3))


if __name__ == "__main__":
    unittest.main(verbosity=2)
