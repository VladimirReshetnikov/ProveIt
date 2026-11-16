from __future__ import annotations

import unittest
from fractions import Fraction

from reference_framework import (
    LayeredRelation,
    all_fold,
    any_fold,
    backward_schedule,
    backward_viability,
    demand_transfer_check,
    enumerate_with_height_bound,
    finite_consumer_window_ok,
    finite_query_envelope,
    forward_reachability,
    full_viable_clouds,
    height_bound_from_complete_list,
    least_true,
    least_viable_path,
    path_ok,
    shrinking_selectors,
    stable_observable_selection,
    verify_pairwise_stability,
    verify_shrinking_bound,
)


class FrameworkTests(unittest.TestCase):
    def test_boolean_folds_and_search(self) -> None:
        values = [True, True, False, True]
        self.assertFalse(all_fold(values))
        self.assertTrue(any_fold(values))
        self.assertEqual(least_true(len(values), lambda i: values[i]), 0)
        self.assertEqual(least_true(7, lambda i: i == 5), 5)
        self.assertEqual(least_true(4, lambda _i: False), 4)

    def test_backward_schedule_equations(self) -> None:
        demand = lambda t, r: r + t + 1
        schedule = backward_schedule(demand, terminal_time=4, terminal_query=3)
        self.assertEqual(schedule[-1], 3)
        for t in range(4):
            self.assertEqual(schedule[t], demand(t, schedule[t + 1]))
        self.assertEqual(schedule, [13, 12, 10, 7, 3])

    def test_demand_transfer(self) -> None:
        # Stage n is valid at precision r exactly when r+n >= 10.
        prop = lambda n, r: r + n >= 10
        demand = lambda _n, r: r + 1
        self.assertTrue(demand_transfer_check(prop, demand, 5, 5))
        self.assertFalse(demand_transfer_check(prop, demand, 5, 4))

    def test_finite_query_envelope(self) -> None:
        count = lambda n, j: j + 1
        query = lambda n, j, r: n + 2 * j + r
        envelope = finite_query_envelope(count, query, stage=3, output_prefix=4)
        expected = max(query(3, j, r) for j in range(5) for r in range(j + 1))
        self.assertEqual(envelope, expected)

    @staticmethod
    def dead_end_relation() -> LayeredRelation:
        return LayeredRelation(
            bound=lambda _p, level: 2 if level < 2 else 2,
            good=lambda _p, level, a: (level < 2 and a in (0, 1))
            or (level == 2 and a == 1),
            compat=lambda _p, level, a, b: (
                (level == 0 and a == b)
                or (level == 1 and a == 1 and b == 1)
            ),
        )

    def test_viability_removes_dead_end(self) -> None:
        relation = self.dead_end_relation()
        viable = backward_viability(relation, parameter=0, horizon=2)
        self.assertEqual(viable[2], {1})
        self.assertEqual(viable[1], {1})
        self.assertEqual(viable[0], {1})
        path = least_viable_path(relation, parameter=0, horizon=2)
        self.assertEqual(path, [1, 1, 1])
        self.assertTrue(path_ok(relation, 0, path))

    def test_full_viability_is_reach_and_viability(self) -> None:
        relation = self.dead_end_relation()
        reach = forward_reachability(relation, 0, 2)
        viable = backward_viability(relation, 0, 2)
        full = full_viable_clouds(relation, 0, 2)
        self.assertEqual(full, [reach[k] & viable[k] for k in range(3)])
        self.assertEqual(full[0], {1})

    def test_independent_square_root_certificates(self) -> None:
        # Each candidate is an interval containing sqrt(2), represented by
        # rational endpoints. Different precisions need not be nested.
        certs = {
            1: [(Fraction(7, 5), Fraction(3, 2)),
                (Fraction(24, 17), Fraction(10, 7))],
            2: [(Fraction(140, 99), Fraction(99, 70)),
                (Fraction(41, 29), Fraction(58, 41))],
        }
        q = Fraction(2)
        bound = lambda n: len(certs[n])
        valid = lambda n, a: (
            certs[n][a][0] >= 0
            and certs[n][a][0] ** 2 <= q <= certs[n][a][1] ** 2
        )
        observe = lambda n, a: sum(certs[n][a], Fraction(0)) / 2
        distance = lambda x, y: abs(x - y)
        # Exhaustive finite error bound from the candidate clouds.
        error = lambda n, m: max(
            distance(observe(n, a), observe(m, b))
            for a in range(bound(n)) if valid(n, a)
            for b in range(bound(m)) if valid(m, b)
        )
        self.assertTrue(
            verify_pairwise_stability(
                bound, valid, observe, distance, error, [1, 2]
            )
        )
        selected = stable_observable_selection(bound, valid, observe, [1, 2])
        self.assertLessEqual(
            distance(selected[1], selected[2]), error(1, 2)
        )

    def test_shrinking_viability_bound(self) -> None:
        # Two candidates around 1 at each level, all adjacent pairs compatible.
        relation = LayeredRelation(
            bound=lambda _p, _k: 2,
            good=lambda _p, _k, a: a in (0, 1),
            compat=lambda _p, _k, _a, _b: True,
        )
        radius = lambda k: Fraction(1, 2 ** (k + 2))
        observe = lambda k, a: Fraction(1) + (-radius(k) if a == 0 else radius(k))
        horizon = lambda k: k + 3
        levels = list(range(5))
        selected = shrinking_selectors(relation, 0, levels, horizon, observe)
        epsilon = lambda k: 2 * radius(k)
        delta = lambda k: radius(k) + radius(k + 1)
        self.assertTrue(verify_shrinking_bound(selected, epsilon, delta))

    def test_metastable_finite_consumer(self) -> None:
        base = 10
        control = lambda n: 3 * n + 20
        queries = [10, 17, 33, 60]
        sequence = lambda n: Fraction(7, 11) if n >= base else Fraction(n, 100)
        self.assertTrue(
            finite_consumer_window_ok(
                sequence, base, control, queries, Fraction(0)
            )
        )
        self.assertFalse(
            finite_consumer_window_ok(
                sequence, base, control, [9, 10], Fraction(1)
            )
        )

    def test_height_list_conversion(self) -> None:
        solutions = {3, 20, 75}
        predicate = lambda x: x in solutions
        height = lambda x: x
        code_bound = lambda H: H + 1
        listing = enumerate_with_height_bound(code_bound, predicate, height, 80)
        self.assertEqual(listing, [3, 20, 75])
        self.assertEqual(height_bound_from_complete_list(listing, height), 75)
        self.assertTrue(all(predicate(x) for x in listing))
        self.assertTrue(all(x in listing for x in solutions))


if __name__ == "__main__":
    unittest.main(verbosity=2)
