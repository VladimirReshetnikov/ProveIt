from __future__ import annotations

import random
import unittest
from fractions import Fraction

from reference.kifcr_reference import (
    CappedDemandEdge,
    CappedDemandSystem,
    CubicBisectionState,
    DemandEdge,
    DemandGraph,
    FiniteRelationTower,
    HeightEnumeration,
    ResidualBoundary,
    ResidualNode,
    adjacent_choice_bound,
    bounded_all,
    bounded_any,
    cubic_bisection,
    cubic_strictly_increasing,
    finite_net_upper_bound,
    guarded_argmin,
    least_bounded,
    least_zero,
    least_zero_spec,
    normalize_residuals,
    observation_diameter,
    run_trace,
    search_invariant,
    stable_observer,
    tail_budget,
)


class BooleanSearchTests(unittest.TestCase):
    def test_folds(self) -> None:
        self.assertTrue(bounded_all(10, lambda i: i < 10))
        self.assertFalse(bounded_all(10, lambda i: i != 7))
        self.assertTrue(bounded_any(20, lambda i: i * i == 81))
        self.assertFalse(bounded_any(9, lambda i: i * i == 81))

    def test_least_search_and_invariant(self) -> None:
        result = least_bounded(50, lambda i: i >= 2 and 84 % i == 0)
        self.assertTrue(result.found)
        self.assertEqual(result.witness, 2)
        self.assertTrue(search_invariant(50, lambda i: i >= 2 and 84 % i == 0))
        self.assertFalse(least_bounded(8, lambda _i: False).found)
        self.assertTrue(search_invariant(8, lambda _i: False))

    def test_current_search_sentinel_convention(self) -> None:
        body = lambda i: 0 if i in {7, 11} else i + 1
        self.assertEqual(least_zero(20, body), 7)
        self.assertTrue(least_zero_spec(20, body))
        self.assertEqual(least_zero(6, lambda i: i + 1), 6)
        self.assertTrue(least_zero_spec(6, lambda i: i + 1))


class TraceTests(unittest.TestCase):
    def test_square_trace(self) -> None:
        certificate = run_trace(
            init=(0, 0),
            step=lambda time, state: (state[0] + 1, state[1] + 2 * time + 1),
            fuel=20,
            invariant=lambda time, state: state == (time, time * time),
            terminal=lambda state: state == (20, 400),
        )
        self.assertTrue(certificate.invariant_holds)
        self.assertTrue(certificate.terminal_holds)
        self.assertEqual(len(certificate.states), 21)


class DemandTests(unittest.TestCase):
    def test_reverse_demand_and_minimality(self) -> None:
        graph = DemandGraph(
            nodes=("input", "square", "inverse", "output"),
            edges=(
                DemandEdge("input", "square", lambda q, _g: q + 2),
                DemandEdge("square", "inverse", lambda q, g: q + 2 * g + 3),
                DemandEdge("inverse", "output", lambda q, _g: q + 1),
            ),
        )
        request = graph.reverse_demands({"output": 10}, 4)
        self.assertEqual(
            request,
            {"input": 24, "square": 22, "inverse": 11, "output": 10},
        )
        self.assertTrue(graph.satisfies(request, {"output": 10}, 4))
        larger = {node: value + 9 for node, value in request.items()}
        self.assertTrue(
            graph.componentwise_least_against(
                request, larger, {"output": 10}, 4
            )
        )


class CyclicDemandTests(unittest.TestCase):
    def test_capped_cycle_stabilizes_and_is_least(self) -> None:
        system = CappedDemandSystem(
            nodes=("coeff", "gap", "mesh"),
            seed={"coeff": 1, "gap": 0, "mesh": 2},
            cap={"coeff": 9, "gap": 8, "mesh": 10},
            edges=(
                CappedDemandEdge("coeff", "gap", lambda q: min(q + 1, 9)),
                CappedDemandEdge("gap", "mesh", lambda q: min(q + 1, 8)),
                CappedDemandEdge("mesh", "coeff", lambda q: min(q + 1, 10)),
            ),
        )
        self.assertTrue(system.monotone_on_box())
        result = system.close()
        self.assertTrue(result.fixed)
        self.assertFalse(result.overflow)
        self.assertEqual(
            result.vector, {"coeff": 9, "gap": 8, "mesh": 10}
        )
        for candidate in system.brute_prefixed_points():
            self.assertTrue(system.least_against(candidate))
        ranks = [system.rank(state) for state in result.states]
        self.assertTrue(all(a <= b for a, b in zip(ranks, ranks[1:])))

    def test_overflow_is_reported(self) -> None:
        system = CappedDemandSystem(
            nodes=("a", "b"),
            seed={"a": 0, "b": 0},
            cap={"a": 2, "b": 2},
            edges=(
                CappedDemandEdge("a", "b", lambda q: q + 3),
                CappedDemandEdge("b", "a", lambda q: q + 3),
            ),
        )
        result = system.close()
        self.assertTrue(result.fixed)
        self.assertTrue(result.overflow)
        self.assertFalse(system.is_raw_closed(result.vector))


class ResidualTests(unittest.TestCase):
    def test_backward_reachability_and_deduplication(self) -> None:
        height = ResidualBoundary("height", "HeightBound(C,H)", "diophantine")
        gap = ResidualBoundary("gap", "Gap(x,g)", "analysis")
        nodes = {
            "input": ResidualNode("input"),
            "enumerate": ResidualNode("enumerate", ("input",), (height,)),
            "verify": ResidualNode("verify", ("enumerate",), (height,)),
            "observer": ResidualNode("observer", ("verify",), (gap,)),
            "unused": ResidualNode(
                "unused", (), (ResidualBoundary("unused", "Unused"),)
            ),
        }
        plan = normalize_residuals(nodes, ("observer",))
        self.assertEqual(
            plan.reachable, ("enumerate", "input", "observer", "verify")
        )
        self.assertEqual([b.key for b in plan.residuals], ["gap", "height"])

    def test_larger_sink_set_is_monotone(self) -> None:
        a = ResidualBoundary("a", "A")
        b = ResidualBoundary("b", "B")
        nodes = {
            "x": ResidualNode("x", boundaries=(a,)),
            "y": ResidualNode("y", boundaries=(b,)),
            "z": ResidualNode("z", ("x",)),
        }
        small = normalize_residuals(nodes, ("z",))
        large = normalize_residuals(nodes, ("z", "y"))
        self.assertLessEqual(
            {r.key for r in small.residuals}, {r.key for r in large.residuals}
        )


class ViabilityTests(unittest.TestCase):
    def test_dead_ends(self) -> None:
        levels = ((0, 1, 2), (10, 11, 12), (20, 21), (30,))
        edges = {
            (0, 0, 10),
            (0, 1, 11),
            (0, 2, 12),
            (1, 10, 20),
            (1, 11, 21),
            (2, 20, 30),
        }
        tower = FiniteRelationTower(
            levels,
            edge=lambda level, a, b: (level, a, b) in edges,
        )
        viable = tower.viable_sets(3)
        self.assertEqual(viable[0], frozenset({0}))
        self.assertEqual(viable[1], frozenset({10}))
        path = tower.least_viable_path(3)
        self.assertEqual(path, (0, 10, 20, 30))
        self.assertTrue(tower.path_is_valid(0, path))
        self.assertTrue(tower.viability_matches_paths(3))

    def test_random_against_bruteforce(self) -> None:
        rng = random.Random(20261115)
        for _ in range(60):
            levels = tuple(tuple(range(4)) for _ in range(4))
            edges = {
                (level, a, b)
                for level in range(3)
                for a in range(4)
                for b in range(4)
                if rng.random() < 0.33
            }
            terminal_set = {a for a in range(4) if rng.random() < 0.75}
            tower = FiniteRelationTower(
                levels,
                edge=lambda level, a, b, edges=edges: (level, a, b) in edges,
                terminal=lambda a, terminal_set=terminal_set: a in terminal_set,
            )
            self.assertTrue(tower.viability_matches_paths(3))


class ObserverTests(unittest.TestCase):
    def test_exact_stable_observer(self) -> None:
        a = Fraction(7, 5)
        candidates = ((a, -a), (-a, a))
        value = stable_observer(
            candidates,
            valid=lambda pair: len(pair) == 2,
            observe=lambda pair: (pair[0] + pair[1], pair[0] * pair[1]),
        )
        self.assertEqual(value, (Fraction(0), -a * a))

    def test_diameter_and_adjacent_bound(self) -> None:
        cloud = (Fraction(1, 3), Fraction(2, 5), Fraction(3, 8))
        diameter = observation_diameter(
            cloud, valid=lambda _x: True, observe=lambda x: x
        )
        self.assertEqual(diameter, Fraction(1, 15))
        self.assertTrue(
            adjacent_choice_bound(
                chosen_left=Fraction(1, 3),
                chosen_right=Fraction(3, 8),
                edge_left=Fraction(2, 5),
                edge_right=Fraction(7, 20),
                left_diameter=Fraction(1, 15),
                motion=Fraction(1, 20),
                right_diameter=Fraction(1, 40),
            )
        )

    def test_tail_budget(self) -> None:
        diameter = lambda q: Fraction(1, 2 ** (q + 4))
        motion = lambda q: Fraction(1, 2 ** (q + 3))
        self.assertEqual(
            tail_budget(diameter, motion, 2, 6),
            sum(
                (
                    diameter(q) + motion(q) + diameter(q + 1)
                    for q in range(2, 6)
                ),
                Fraction(0),
            ),
        )


class GuardedSelectionTests(unittest.TestCase):
    def test_guarded_argmin(self) -> None:
        true_scores = (Fraction(0), Fraction(5, 4), Fraction(3))
        error = Fraction(1, 10)
        approximations = (
            true_scores[0] + error,
            true_scores[1] - error,
            true_scores[2],
        )
        self.assertEqual(guarded_argmin(approximations, error, gap=Fraction(1)), 0)
        with self.assertRaises(ValueError):
            guarded_argmin(approximations, Fraction(1, 2), gap=Fraction(1))


class CubicBisectionTests(unittest.TestCase):
    def test_monotonicity_factorization(self) -> None:
        for a, b in [
            (Fraction(-3), Fraction(2)),
            (Fraction(-2, 3), Fraction(5, 7)),
            (Fraction(0), Fraction(1, 100)),
        ]:
            self.assertTrue(cubic_strictly_increasing(a, b))

    def test_bisection_invariant(self) -> None:
        for x in [Fraction(0), Fraction(1), Fraction(-7, 3), Fraction(19, 5)]:
            certificate = cubic_bisection(x, 30)
            self.assertTrue(certificate.invariant_holds)
            self.assertTrue(certificate.terminal_holds)
            final = certificate.states[-1]
            self.assertIsInstance(final, CubicBisectionState)
            self.assertLessEqual(final.lower, final.upper)
            self.assertLessEqual(
                final.upper - final.lower,
                Fraction(2 * (abs(x) + 1), 2**30),
            )


class HeightAndNetTests(unittest.TestCase):
    def test_height_list_conversion(self) -> None:
        spec = HeightEnumeration(
            enumerate_box=lambda bound: (
                sign * magnitude
                for sign in (-1, 1)
                for magnitude in range(bound + 1)
            ),
            height=abs,
            predicate=lambda x: x * x <= 9,
            canonical_key=lambda x: x,
        )
        points = spec.list_from_bound(3)
        self.assertEqual(set(points), set(range(-3, 4)))
        self.assertEqual(spec.bound_from_complete_list(points), 3)

    def test_finite_net_bound(self) -> None:
        bound = finite_net_upper_bound(
            (Fraction(1, 3), Fraction(2, 5), Fraction(7, 20)),
            evaluation_error=Fraction(1, 100),
            transport_error=Fraction(1, 50),
        )
        self.assertEqual(bound, Fraction(43, 100))


if __name__ == "__main__":
    unittest.main()
