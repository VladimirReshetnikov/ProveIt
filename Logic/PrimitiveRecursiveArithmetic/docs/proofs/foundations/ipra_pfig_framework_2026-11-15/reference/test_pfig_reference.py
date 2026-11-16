from __future__ import annotations

import random
import unittest
from fractions import Fraction

from reference.pfig_reference import (
    DemandEdge,
    DemandGraph,
    FiniteRelationTower,
    HeightEnumeration,
    bounded_all,
    bounded_any,
    canonical_observations,
    check_adjacent_coherence,
    guarded_argmin,
    least_bounded,
    run_trace,
    stable_observer,
    symmetric_quadratic_observable,
    tail_budget,
)


class BooleanAndSearchTests(unittest.TestCase):
    def test_boolean_folds_and_least_search(self) -> None:
        self.assertTrue(bounded_all(8, lambda i: i < 8))
        self.assertFalse(bounded_all(8, lambda i: i != 5))
        self.assertTrue(bounded_any(20, lambda i: i * i == 81))
        self.assertFalse(bounded_any(9, lambda i: i * i == 81))

        result = least_bounded(30, lambda i: i >= 2 and 84 % i == 0)
        self.assertTrue(result.found)
        self.assertEqual(result.witness, 2)
        self.assertFalse(least_bounded(5, lambda _: False).found)

    def test_trace_invariant(self) -> None:
        cert = run_trace(
            init=(0, 0),
            step=lambda time, state: (state[0] + 1, state[1] + 2 * time + 1),
            fuel=12,
            invariant=lambda time, state: state == (time, time * time),
            terminal=lambda state: state == (12, 144),
        )
        self.assertTrue(cert.invariant_holds)
        self.assertTrue(cert.terminal_holds)
        self.assertEqual(len(cert.states), 13)


class DemandTests(unittest.TestCase):
    def test_reverse_demand_and_minimality(self) -> None:
        graph = DemandGraph(
            nodes=("input", "square", "inverse", "output"),
            edges=(
                DemandEdge("input", "square", lambda p, _: p + 2),
                DemandEdge("square", "inverse", lambda p, guard: p + 2 * guard + 3),
                DemandEdge("inverse", "output", lambda p, _: p + 1),
            ),
        )
        requests = graph.reverse_demands({"output": 10}, 4)
        self.assertEqual(requests["output"], 10)
        self.assertEqual(requests["inverse"], 11)
        self.assertEqual(requests["square"], 22)
        self.assertEqual(requests["input"], 24)
        self.assertTrue(graph.satisfies(requests, {"output": 10}, 4))

        # Any satisfying vector must dominate the computed one in this chain.
        larger = {name: value + 7 for name, value in requests.items()}
        self.assertTrue(graph.satisfies(larger, {"output": 10}, 4))
        for name in graph.nodes:
            self.assertLessEqual(requests[name], larger[name])


class ViabilityTests(unittest.TestCase):
    def test_dead_ends_and_least_path(self) -> None:
        levels = (
            (0, 1, 2),
            (10, 11, 12),
            (20, 21),
            (30,),
        )
        allowed = {
            (0, 0, 10),
            (0, 1, 11),
            (0, 2, 12),
            (1, 10, 20),
            (1, 11, 21),
            # 12 is a dead end.
            (2, 20, 30),
            # 21 is a later dead end.
        }
        tower = FiniteRelationTower(
            levels=levels,
            edge=lambda i, a, b: (i, a, b) in allowed,
        )
        viable = tower.viable_sets(3)
        self.assertEqual(viable[0], frozenset({0}))
        self.assertEqual(viable[1], frozenset({10}))
        self.assertEqual(tower.least_viable_path(3), (0, 10, 20, 30))
        self.assertTrue(tower.viability_matches_paths(3))

    def test_random_viability_matches_bruteforce(self) -> None:
        rng = random.Random(20261115)
        for _ in range(30):
            levels = tuple(tuple(range(4)) for _ in range(4))
            allowed = {
                (i, a, b)
                for i in range(3)
                for a in range(4)
                for b in range(4)
                if rng.random() < 0.35
            }
            tower = FiniteRelationTower(
                levels=levels,
                edge=lambda i, a, b, allowed=allowed: (i, a, b) in allowed,
            )
            self.assertTrue(tower.viability_matches_paths(3))


class ShrinkingTests(unittest.TestCase):
    def test_shrinking_cloud_coherence(self) -> None:
        # Level p has integer numerators close to 2^p * alpha, with alpha=1/3.
        alpha = Fraction(1, 3)
        levels = []
        for p in range(8):
            scale = 2**p
            center = (scale * alpha.numerator) // alpha.denominator
            levels.append(tuple(sorted({max(0, center - 1), center, center + 1, center + 2})))

        def obs(p: int, a: int) -> Fraction:
            return Fraction(a, 2**p)

        # A generous dyadic edge bound makes every genuinely close refinement
        # compatible while leaving some candidates to be pruned later.
        def edge(p: int, a: int, b: int) -> bool:
            return abs(obs(p, a) - obs(p + 1, b)) <= Fraction(3, 2**p)

        tower = FiniteRelationTower(tuple(levels), edge)
        horizon = lambda p: min(7, p + 2)
        canonical = canonical_observations(tower, 5, horizon, obs)

        # These bounds are verified from the actual finite clouds below.  They
        # are intentionally loose but summable on the tested finite range.
        def diameter(p: int) -> Fraction:
            h = horizon(p)
            viable = tower.viable_sets(h)[p]
            values = [obs(p, a) for a in viable]
            return max(values) - min(values)

        def motion(p: int) -> Fraction:
            pairs = [
                abs(obs(p, a) - obs(p + 1, b))
                for a in tower.levels[p]
                for b in tower.levels[p + 1]
                if edge(p, a, b)
            ]
            return max(pairs, default=Fraction(0))

        self.assertTrue(check_adjacent_coherence(canonical, obs, diameter, motion))
        for p in range(5):
            self.assertLessEqual(
                abs(canonical[p][0] - canonical[p + 1][0]),
                diameter(p) + motion(p),
            )
        self.assertGreaterEqual(tail_budget(diameter, motion, 1, 5), 0)


class StabilityAndGuardTests(unittest.TestCase):
    def test_stable_symmetric_observer(self) -> None:
        a = Fraction(7, 5)
        certificates = ((a, -a), (-a, a))
        observed = stable_observer(
            certificates,
            valid=lambda roots: len(roots) == 2,
            observe=symmetric_quadratic_observable,
        )
        self.assertEqual(observed, (Fraction(0), -a * a))

    def test_guarded_argmin(self) -> None:
        true_scores = (Fraction(0), Fraction(5, 4), Fraction(3, 1))
        error = Fraction(1, 10)
        approximations = (
            true_scores[0] + error,
            true_scores[1] - error,
            true_scores[2],
        )
        index = guarded_argmin(approximations, error, gap=Fraction(1, 1))
        self.assertEqual(index, 0)
        with self.assertRaises(ValueError):
            guarded_argmin(approximations, Fraction(3, 5), gap=Fraction(1, 1))


class HeightTests(unittest.TestCase):
    def test_height_bound_and_complete_list(self) -> None:
        # Integer solutions of x^2 <= 9, represented redundantly by (sign,n).
        def enumerate_box(bound: int):
            for sign in (-1, 1):
                for magnitude in range(bound + 1):
                    yield sign * magnitude

        spec = HeightEnumeration(
            enumerate_box=enumerate_box,
            height=abs,
            predicate=lambda x: x * x <= 9,
            canonical_key=lambda x: x,
        )
        points = spec.list_from_bound(3)
        self.assertEqual(set(points), set(range(-3, 4)))
        self.assertEqual(spec.bound_from_complete_list(points), 3)


if __name__ == "__main__":
    unittest.main()
