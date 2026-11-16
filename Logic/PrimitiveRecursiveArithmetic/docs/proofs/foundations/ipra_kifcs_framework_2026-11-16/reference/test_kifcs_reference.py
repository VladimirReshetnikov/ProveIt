from __future__ import annotations

import random
import unittest
from fractions import Fraction

from reference.kifcs_reference import (
    And,
    Atom,
    Boundary,
    CappedDemandSystem,
    DemandEdge,
    Exists,
    FalseCert,
    Forall,
    Or,
    ProofNode,
    RelationTower,
    TruthCert,
    backward_reachable,
    check_false,
    check_truth,
    compile_query_plan,
    cubic,
    cubic_bisection,
    eval_formula,
    false_certificate,
    observation_diameter,
    reachability_is_least,
    stable_observation,
    stable_unique,
    tail_sum,
    topological_order,
    truth_certificate,
)


class StableUniqueTests(unittest.TestCase):
    def test_first_occurrence_is_retained(self) -> None:
        self.assertEqual(stable_unique(["b", "a", "b", "c", "a"]), ("b", "a", "c"))


class QueryCompilerTests(unittest.TestCase):
    def setUp(self) -> None:
        height = Boundary("height", "HeightBound(x,H)", "enumerate")
        gap = Boundary("gap", "Gap(x,g)", "observer")
        self.nodes = {
            "input": ProofNode("input"),
            "enumerate": ProofNode("enumerate", ("input",), (height,)),
            "verify": ProofNode("verify", ("enumerate",), (height,)),
            "observe": ProofNode("observe", ("verify",), (gap,)),
            "unused": ProofNode("unused", boundaries=(Boundary("unused", "Unused"),)),
        }

    def test_backward_slice_and_frontier(self) -> None:
        plan = compile_query_plan(self.nodes, ("observe",))
        self.assertEqual(plan.reachable, ("enumerate", "input", "observe", "verify"))
        self.assertEqual([b.key for b in plan.residuals], ["gap", "height"])
        self.assertNotIn("unused", plan.reachable)
        self.assertEqual(plan.topological[0], "input")
        self.assertEqual(plan.topological[-1], "observe")

    def test_soundness_query_needs_no_gap(self) -> None:
        plan = compile_query_plan(self.nodes, ("verify",))
        self.assertEqual([b.key for b in plan.residuals], ["height"])

    def test_multi_query_union(self) -> None:
        single = backward_reachable(self.nodes, ("observe",))
        combined = backward_reachable(self.nodes, ("observe", "unused"))
        self.assertEqual(combined, single | {"unused"})

    def test_reachability_minimality(self) -> None:
        reachable = backward_reachable(self.nodes, ("observe",))
        self.assertTrue(reachability_is_least(self.nodes, ("observe",), reachable | {"unused"}))
        self.assertFalse(reachability_is_least(self.nodes, ("observe",), {"observe"}))

    def test_cycle_rejected(self) -> None:
        nodes = {
            "a": ProofNode("a", ("b",)),
            "b": ProofNode("b", ("a",)),
        }
        with self.assertRaises(ValueError):
            topological_order(nodes, nodes)

    def test_boundary_key_conflict_rejected(self) -> None:
        nodes = {
            "a": ProofNode("a", boundaries=(Boundary("same", "A"),)),
            "b": ProofNode("b", ("a",), (Boundary("same", "B"),)),
        }
        with self.assertRaises(ValueError):
            compile_query_plan(nodes, ("b",))


class DemandTests(unittest.TestCase):
    def test_capped_cycle_stabilizes(self) -> None:
        system = CappedDemandSystem(
            nodes=("r0", "r1"),
            seed={"r0": 1, "r1": 0},
            cap={"r0": 8, "r1": 8},
            edges=(
                DemandEdge("r0", "r1", lambda q: q + 1),
                DemandEdge("r1", "r0", lambda q: q // 2 + 1),
            ),
        )
        result = system.close()
        self.assertTrue(result.fixed)
        self.assertFalse(result.overflow)
        self.assertTrue(system.closed(result.vector))
        ranks = [system.rank(vector) for vector in result.states]
        self.assertTrue(all(left < right for left, right in zip(ranks, ranks[1:])))

    def test_overflow_is_explicit(self) -> None:
        system = CappedDemandSystem(
            nodes=("a", "b"),
            seed={"a": 0, "b": 0},
            cap={"a": 2, "b": 2},
            edges=(
                DemandEdge("a", "b", lambda q: q + 3),
                DemandEdge("b", "a", lambda q: q + 3),
            ),
        )
        result = system.close()
        self.assertTrue(result.overflow)
        self.assertTrue(result.overflow_edges)
        self.assertFalse(system.closed(result.vector))

    def test_least_against_larger_closed_point(self) -> None:
        system = CappedDemandSystem(
            nodes=("a", "b"),
            seed={"a": 1, "b": 1},
            cap={"a": 10, "b": 10},
            edges=(DemandEdge("a", "b", lambda q: q),),
        )
        self.assertTrue(system.least_against({"a": 7, "b": 6}))


class StrategyTests(unittest.TestCase):
    @staticmethod
    def challenge_formula(limit: int):
        # forall u < limit, exists v < limit, forall w < limit,
        # (v = u) or (w < limit); true with least witness v = 0 as written.
        atom = Atom("A", lambda env: env["v"] == env["u"] or env["w"] < limit)
        return Forall(
            "u",
            lambda _env: limit,
            Exists(
                "v",
                lambda _env: limit,
                Forall("w", lambda _env: limit, atom),
            ),
        )

    def test_truth_certificate_nested_alternation(self) -> None:
        formula = self.challenge_formula(4)
        self.assertTrue(eval_formula(formula, {}))
        cert = truth_certificate(formula, {})
        self.assertTrue(check_truth(formula, {}, cert))

    def test_false_certificate_existential(self) -> None:
        formula = Exists("x", lambda _env: 5, Atom("large", lambda env: env["x"] > 10))
        self.assertFalse(eval_formula(formula, {}))
        cert = false_certificate(formula, {})
        self.assertTrue(check_false(formula, {}, cert))

    def test_conjunction_false_tag(self) -> None:
        formula = And(Atom("t", lambda _env: True), Atom("f", lambda _env: False))
        cert = false_certificate(formula, {})
        self.assertEqual(cert.tag, "and-right")
        self.assertTrue(check_false(formula, {}, cert))

    def test_disjunction_truth_tag(self) -> None:
        formula = Or(Atom("f", lambda _env: False), Atom("t", lambda _env: True))
        cert = truth_certificate(formula, {})
        self.assertEqual(cert.tag, "or-right")
        self.assertTrue(check_truth(formula, {}, cert))

    def test_malformed_certificates_fail(self) -> None:
        formula = Atom("t", lambda _env: True)
        self.assertFalse(check_truth(formula, {}, TruthCert("wrong")))
        self.assertFalse(check_false(formula, {}, FalseCert("atom")))

    def test_random_small_formulas_two_sided(self) -> None:
        rng = random.Random(20261116)
        for _ in range(100):
            threshold = rng.randrange(0, 5)
            formula = Forall(
                "x",
                lambda _env: 5,
                Or(
                    Atom("low", lambda env, t=threshold: env["x"] < t),
                    Atom("high", lambda env, t=threshold: env["x"] >= t),
                ),
            )
            value = eval_formula(formula, {})
            self.assertTrue(value)
            self.assertTrue(check_truth(formula, {}, truth_certificate(formula, {})))


class RelationTests(unittest.TestCase):
    def test_dead_end_example(self) -> None:
        levels = ((0, 1), (0, 1, 2), (2,))
        edges = {(0, 0, 0), (0, 1, 1), (0, 1, 2), (1, 2, 2)}
        tower = RelationTower(levels, edge=lambda level, a, b: (level, a, b) in edges)
        rows = tower.viable(2)
        self.assertEqual(rows[0], frozenset({1}))
        self.assertEqual(rows[1], frozenset({2}))
        self.assertEqual(tower.least_path(2), (1, 2, 2))
        self.assertTrue(tower.viability_matches_paths(2))

    def test_random_viability_against_bruteforce(self) -> None:
        rng = random.Random(194)
        for _ in range(60):
            levels = tuple(tuple(range(4)) for _ in range(4))
            edges = {
                (level, left, right)
                for level in range(3)
                for left in range(4)
                for right in range(4)
                if rng.random() < 0.35
            }
            terminal = {value for value in range(4) if rng.random() < 0.7}
            tower = RelationTower(
                levels,
                edge=lambda level, left, right, edges=edges: (level, left, right) in edges,
                terminal=lambda value, terminal=terminal: value in terminal,
            )
            self.assertTrue(tower.viability_matches_paths(3))


class ObserverAndMetricTests(unittest.TestCase):
    def test_exact_stable_symmetric_observation(self) -> None:
        a = Fraction(7, 5)
        candidates = ((a, -a), (-a, a))
        value = stable_observation(candidates, lambda pair: (sum(pair), pair[0] * pair[1]))
        self.assertEqual(value, (Fraction(0), -(a * a)))

    def test_diameter(self) -> None:
        cloud = (Fraction(1, 3), Fraction(2, 5), Fraction(3, 8))
        self.assertEqual(observation_diameter(cloud, lambda value: value), Fraction(1, 15))

    def test_tail_sum(self) -> None:
        terms = [Fraction(1, 2 ** (index + 1)) for index in range(12)]
        self.assertEqual(tail_sum(terms, 3, 8), sum(terms[3:8], Fraction(0)))


class BisectionTests(unittest.TestCase):
    def test_bracketing_and_width(self) -> None:
        for x in [Fraction(0), Fraction(1), Fraction(-7, 3), Fraction(19, 5)]:
            states = cubic_bisection(x, 30)
            final = states[-1]
            self.assertLessEqual(cubic(final.lower), x)
            self.assertLessEqual(x, cubic(final.upper))
            initial_width = states[0].upper - states[0].lower
            self.assertEqual(final.upper - final.lower, initial_width / (2**30))


if __name__ == "__main__":
    unittest.main()
