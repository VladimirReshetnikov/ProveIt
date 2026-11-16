#!/usr/bin/env python3
from __future__ import annotations

import unittest

from scope_reference import (
    AllLt,
    And,
    Eq,
    ExLt,
    Imp,
    Not,
    backward_viability,
    build_demo,
    check_monotone,
    classify_escape,
    compile_bit,
    demand_closure,
    diameter_bound,
    EscapeMode,
    least_accepted,
    mixed_radix_decode,
    mixed_radix_encode,
    product_capacity,
    solve_forall_exists,
    stable_observation,
    tree_error_bound,
    verify_forall_exists_strategy,
)


class ScopeReferenceTests(unittest.TestCase):
    def test_nested_bounded_formula_true(self) -> None:
        # forall x<6 exists y<4, x+y == 0 mod 3
        formula = AllLt(
            lambda _env: 6,
            ExLt(
                lambda _env: 4,
                Eq(lambda env: (env[0] + env[1]) % 3, lambda _env: 0),
            ),
        )
        self.assertEqual(compile_bit(formula, ()), 1)

    def test_bounded_formula_implication_and_negation(self) -> None:
        formula = AllLt(
            lambda _env: 5,
            Imp(
                Eq(lambda env: env[0] % 2, lambda _env: 0),
                Not(Eq(lambda env: env[0] % 2, lambda _env: 1)),
            ),
        )
        self.assertEqual(compile_bit(formula, ()), 1)

    def test_bounded_formula_false(self) -> None:
        formula = ExLt(
            lambda _env: 4,
            And(
                Eq(lambda env: env[0], lambda _env: 3),
                Eq(lambda env: env[0], lambda _env: 2),
            ),
        )
        self.assertEqual(compile_bit(formula, ()), 0)

    def test_least_accepted_success_and_sentinel(self) -> None:
        self.assertEqual(least_accepted(10, lambda i: i * i >= 17), (5, True))
        self.assertEqual(least_accepted(4, lambda _i: False), (4, False))

    def test_mixed_radix_roundtrip(self) -> None:
        caps = (2, 4, 1, 3)
        self.assertEqual(product_capacity(caps), 3 * 5 * 2 * 4)
        for code in range(product_capacity(caps)):
            digits = mixed_radix_decode(code, caps)
            self.assertEqual(mixed_radix_encode(digits, caps), code)

    def test_cyclic_demand_closure(self) -> None:
        caps = (5, 6, 5)

        def f(d: tuple[int, ...]) -> tuple[int, ...]:
            return (min(5, d[1] + 1), min(6, d[2] + 2), min(5, d[0]))

        self.assertTrue(check_monotone(caps, f))
        result = demand_closure(caps, f)
        self.assertEqual(result["fixed_point"], [5, 6, 5])
        self.assertLessEqual(result["iterations"], sum(caps))
        ranks = [sum(v) for v in result["history"]]
        self.assertEqual(ranks, sorted(ranks))

    def test_demand_closure_is_least_prefixed_point(self) -> None:
        caps = (3, 3)

        def f(d: tuple[int, ...]) -> tuple[int, ...]:
            return (min(3, d[1] + 1), min(3, d[0] + 1))

        result = demand_closure(caps, f)
        fixed = tuple(result["fixed_point"])
        self.assertEqual(fixed, (3, 3))
        # Exhaustive check of leastness for this small product.
        for code in range(product_capacity(caps)):
            candidate = mixed_radix_decode(code, caps)
            image = f(candidate)
            if all(image[i] <= candidate[i] for i in range(2)):
                self.assertTrue(all(fixed[i] <= candidate[i] for i in range(2)))

    def test_viability_avoids_greedy_dead_end(self) -> None:
        levels = ((0, 1), (0, 1), (0,))
        edges = {0: {(0, 0), (1, 1)}, 1: {(1, 0)}}
        result = backward_viability(
            levels,
            lambda _i, _a: True,
            lambda i, a, b: (a, b) in edges[i],
        )
        self.assertIsNotNone(result)
        assert result is not None
        self.assertEqual(result.path, (1, 1, 0))
        self.assertNotIn(0, result.viable_levels[0])

    def test_viability_reports_failure(self) -> None:
        result = backward_viability(
            ((0,), (0,)),
            lambda _i, _a: True,
            lambda _i, _a, _b: False,
        )
        self.assertIsNone(result)

    def test_forall_exists_strategy_and_counterexample(self) -> None:
        yes = solve_forall_exists(6, lambda _x: 4, lambda x, y: (x + y) % 3 == 0)
        self.assertTrue(yes["truth"])
        self.assertTrue(
            verify_forall_exists_strategy(
                yes["strategy"], 6, lambda _x: 4, lambda x, y: (x + y) % 3 == 0
            )
        )
        no = solve_forall_exists(3, lambda _x: 1, lambda x, y: x == y)
        self.assertFalse(no["truth"])
        self.assertEqual(no["counterexample_x"], 1)

    def test_stable_and_metric_observers(self) -> None:
        stable, value = stable_observation(range(8), lambda c: c % 2 == 0, lambda c: c % 2)
        self.assertTrue(stable)
        self.assertEqual(value, 0)
        self.assertEqual(diameter_bound(range(5), lambda _c: True, lambda c: 2 * c), 8)

    def test_tree_error_accumulation_and_cycle_rejection(self) -> None:
        parent = {"r": None, "a": "r", "b": "a", "c": "r"}
        error = {"a": 2, "b": 4, "c": 1}
        self.assertEqual(tree_error_bound("r", parent, error), {"r": 0, "a": 2, "b": 6, "c": 1})
        with self.assertRaises(ValueError):
            tree_error_bound("r", {"r": None, "a": "b", "b": "a"}, {"a": 1, "b": 1})

    def test_escape_classification(self) -> None:
        self.assertEqual(classify_escape(False), EscapeMode.PRIVATE)
        self.assertEqual(classify_escape(True, output_is_existential=True), EscapeMode.EXISTENTIAL)
        self.assertEqual(classify_escape(True, stable_observer_proved=True), EscapeMode.STABLE)
        self.assertEqual(classify_escape(True, bounded_canonical_order=True), EscapeMode.CANONICAL)
        self.assertEqual(classify_escape(True), EscapeMode.RESIDUAL)
        self.assertEqual(classify_escape(False, producer_available=False), EscapeMode.RESIDUAL)

    def test_demo_is_deterministic_and_self_verifying(self) -> None:
        first = build_demo()
        second = build_demo()
        self.assertEqual(first, second)
        self.assertTrue(first["strategy_verified"])
        self.assertEqual(first["viability"]["path"], [1, 1, 0])


if __name__ == "__main__":
    unittest.main(verbosity=2)
