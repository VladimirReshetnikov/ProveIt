from __future__ import annotations

import copy
import unittest

from darc_reference import (
    Atom,
    DARCError,
    DemandNetwork,
    ExistsBounded,
    ForallBounded,
    QAnd,
    QOr,
    ResourceShape,
    ThresholdRule,
    backward_viability,
    bounded_least,
    build_strategy,
    check_strategy,
    check_trace,
    closure_report,
    run_trace,
)


class DemandTests(unittest.TestCase):
    def make_network(self) -> tuple[DemandNetwork, object]:
        shape = ResourceShape(
            (
                "query:observable",
                "cert:branch",
                "cert:local_trace",
                "precision:x",
                "precision:y",
                "guard:denominator",
                "residual:tail_modulus",
            ),
            (1, 1, 1, 5, 5, 1, 1),
        )
        rules = [
            ThresholdRule.make(
                {"query:observable": 1},
                {"precision:y": 3},
                "public query requests output precision",
            ),
            ThresholdRule.make(
                {"precision:y": 1},
                {"precision:x": 2, "guard:denominator": 1},
                "division transfers precision and apartness",
            ),
            ThresholdRule.make(
                {"precision:x": 2},
                {"precision:y": 4},
                "cyclic local modulus",
            ),
            ThresholdRule.make(
                {"precision:y": 4},
                {"precision:x": 5, "residual:tail_modulus": 1},
                "high precision exposes tail producer",
            ),
            ThresholdRule.make(
                {"cert:branch": 1},
                {"guard:denominator": 1},
                "named branch requires guard",
            ),
        ]
        network = DemandNetwork(shape, rules)
        seed = shape.demand({"query:observable": 1})
        return network, seed

    def test_cyclic_closure_and_leastness(self) -> None:
        network, seed = self.make_network()
        closure = network.closure(seed)
        self.assertTrue(network.is_prefixed(closure.fixed_point))
        self.assertTrue(network.check_least(closure))
        self.assertTrue(network.check_monotone_exhaustively())
        self.assertEqual(closure.fixed_point["precision:x"], 5)
        self.assertEqual(closure.fixed_point["precision:y"], 4)
        self.assertEqual(closure.fixed_point["guard:denominator"], 1)
        self.assertEqual(closure.fixed_point["residual:tail_modulus"], 1)
        self.assertEqual(closure.fixed_point["cert:branch"], 0)
        self.assertEqual(closure.fixed_point["cert:local_trace"], 0)
        self.assertLessEqual(closure.strict_steps, network.shape.max_rank)

    def test_query_specific_liveness(self) -> None:
        network, _ = self.make_network()
        seed = network.shape.demand({"query:observable": 1, "cert:branch": 1})
        closure = network.closure(seed)
        self.assertEqual(closure.fixed_point["cert:branch"], 1)
        self.assertEqual(closure.fixed_point["cert:local_trace"], 0)

    def test_report_identifies_residuals(self) -> None:
        network, seed = self.make_network()
        report = closure_report(network, seed)
        self.assertIn("residual:tail_modulus", report["residuals"])
        self.assertIn("guard:denominator", report["required_guards"])
        self.assertEqual(report["live_certificates"], [])
        self.assertTrue(report["least_prefixed_point_checked"])

    def test_bad_rule_rejected(self) -> None:
        shape = ResourceShape(("x",), (1,))
        with self.assertRaises(DARCError):
            DemandNetwork(shape, [ThresholdRule.make({"x": 2}, {}, "bad")])


class SearchAndStrategyTests(unittest.TestCase):
    def formula(self):
        # forall i<4 exists j<5: i+j is even, together with a harmless disjunction.
        parity = Atom("even-sum", lambda e: (e["i"] + e["j"]) % 2 == 0)
        core = ForallBounded("i", 4, ExistsBounded("j", 5, parity))
        tag = QOr(Atom("left-false", lambda e: False), Atom("right-true", lambda e: True))
        return QAnd(core, tag)

    def test_bounded_least(self) -> None:
        self.assertEqual(bounded_least(10, lambda i: i * i >= 20), 5)
        self.assertEqual(bounded_least(4, lambda i: False), 4)

    def test_strategy_sound(self) -> None:
        formula = self.formula()
        cert = build_strategy(formula)
        self.assertTrue(formula.evaluate({}))
        self.assertTrue(check_strategy(formula, cert))
        witnesses = cert["left"]["branches"]
        self.assertEqual([row["witness"] for row in witnesses], [0, 1, 0, 1])

    def test_strategy_tamper_rejected(self) -> None:
        formula = self.formula()
        cert = build_strategy(formula)
        bad = copy.deepcopy(cert)
        bad["left"]["branches"][1]["witness"] = 0
        self.assertFalse(check_strategy(formula, bad))

    def test_false_formula_has_no_strategy(self) -> None:
        formula = ExistsBounded("x", 3, Atom("impossible", lambda e: e["x"] > 7))
        with self.assertRaises(DARCError):
            build_strategy(formula)


class TraceAndRelationTests(unittest.TestCase):
    def test_trace(self) -> None:
        step = lambda state: (state[0] + 1, state[1] + state[0] + 1)
        trace = run_trace((0, 0), step, 6)
        self.assertTrue(check_trace(trace, step, lambda s: s[0] >= 0 and s[1] >= 0))
        bad = list(trace)
        bad[3] = (999, 999)
        self.assertFalse(check_trace(bad, step))

    def test_backward_viability(self) -> None:
        layers = [range(3), range(5), range(7), range(9)]
        edge = lambda i, x, y: y in (x, x + 1)
        result = backward_viability(layers, edge, start=1)
        self.assertIsNotNone(result.least_path)
        self.assertEqual(result.least_path, (1, 1, 1, 1))
        for i in range(len(result.least_path) - 1):
            self.assertTrue(edge(i, result.least_path[i], result.least_path[i + 1]))

    def test_no_viable_start(self) -> None:
        layers = [[0], [1], [2]]
        edge = lambda i, x, y: y == x
        result = backward_viability(layers, edge, start=0)
        self.assertIsNone(result.least_path)
        self.assertEqual(result.viable_layers[0], ())


if __name__ == "__main__":
    unittest.main()
