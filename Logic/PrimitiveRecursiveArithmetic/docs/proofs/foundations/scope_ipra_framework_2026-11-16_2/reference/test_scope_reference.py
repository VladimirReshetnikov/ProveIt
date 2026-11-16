#!/usr/bin/env python3
from __future__ import annotations

import unittest

from reference.scope_reference import (
    And,
    Eq,
    ExistsLt,
    ForallLt,
    Imp,
    Lt,
    Not,
    Or,
    ScopeNode,
    add,
    check_scope_graph,
    const,
    demand_closure,
    exact_observer_independent,
    least_witness,
    metric_observer_diameter,
    var,
    witness_certificate,
)


class ReflectionTests(unittest.TestCase):
    def test_boolean_connectives(self) -> None:
        a = Eq(const(2), const(2))
        b = Lt(const(5), const(3))
        self.assertEqual(And(a, b).bit(()), 0)
        self.assertEqual(Or(a, b).bit(()), 1)
        self.assertEqual(Imp(b, a).bit(()), 1)
        self.assertEqual(Imp(a, b).bit(()), 0)
        self.assertEqual(Not(b).bit(()), 1)

    def test_nested_bounded_quantifiers(self) -> None:
        formula = ForallLt(
            const(8),
            ExistsLt(const(10), Eq(var(0), add(var(1), const(1)))),
        )
        self.assertTrue(formula.eval(()))
        self.assertEqual(formula.bit(()), 1)

    def test_false_bounded_universal(self) -> None:
        formula = ForallLt(const(5), Lt(var(0), const(4)))
        self.assertFalse(formula.eval(()))
        self.assertEqual(formula.bit(()), 0)

    def test_parameter_substitution_semantics(self) -> None:
        # Outer environment contains N. Body sees (i, N).
        formula = ExistsLt(var(0), Eq(var(0), add(var(1), const(2))))
        for n in range(8):
            expected = any(i == n + 2 for i in range(n))
            self.assertEqual(formula.eval((n,)), expected)


class SearchTests(unittest.TestCase):
    def test_least_witness(self) -> None:
        self.assertEqual(least_witness(20, lambda x: x * x >= 50), 8)

    def test_no_witness_returns_bound(self) -> None:
        self.assertEqual(least_witness(7, lambda _x: False), 7)

    def test_witness_certificate(self) -> None:
        cert = witness_certificate(10, lambda x: x >= 4 and x % 2 == 0)
        self.assertEqual(cert["witness"], 4)
        self.assertTrue(cert["accepted"])
        self.assertTrue(cert["minimal"])


class DemandTests(unittest.TestCase):
    def test_cyclic_closure(self) -> None:
        def transformer(d: tuple[int, ...]) -> tuple[int, ...]:
            a, b, c = d
            return min(4, b + 1), min(5, c + 1), min(3, a)

        result = demand_closure(transformer, (4, 5, 3))
        self.assertEqual(result["closure"], [4, 4, 3])
        self.assertTrue(result["prefixed"])
        self.assertLessEqual(result["steps"], 12)

    def test_already_fixed(self) -> None:
        result = demand_closure(lambda d: d, (2, 2), (1, 1))
        self.assertEqual(result["steps"], 0)
        self.assertTrue(result["fixed"])


class ScopeTests(unittest.TestCase):
    def test_sealed_boundary_is_explicit(self) -> None:
        graph = [
            ScopeNode(
                "height",
                kind="certificate",
                escape="sealed",
                has_producer=False,
                residual="ExistsHeightBound",
            ),
            ScopeNode("goal", deps=("height",)),
        ]
        result = check_scope_graph(graph)
        self.assertTrue(result["ok"])
        self.assertEqual(result["residuals"], ["ExistsHeightBound"])

    def test_unjustified_named_escape_is_rejected(self) -> None:
        result = check_scope_graph(
            [ScopeNode("label", kind="public_name", escape="named", has_producer=False)]
        )
        self.assertFalse(result["ok"])
        self.assertIn("unjustified_name", {issue["code"] for issue in result["issues"]})

    def test_relational_observer_needs_coherence(self) -> None:
        bad = check_scope_graph([ScopeNode("obs", escape="relational")])
        self.assertFalse(bad["ok"])
        good = check_scope_graph(
            [ScopeNode("obs", escape="relational", observer_coherent=True)]
        )
        self.assertTrue(good["ok"])

    def test_named_bounded_selector_is_allowed(self) -> None:
        result = check_scope_graph(
            [
                ScopeNode(
                    "least",
                    kind="public_name",
                    escape="named",
                    has_producer=False,
                    has_bound=True,
                    residual="ExistsAcceptedBelowBound",
                )
            ]
        )
        self.assertTrue(result["ok"])

    def test_cycle_is_rejected_in_scope_graph(self) -> None:
        with self.assertRaises(ValueError):
            check_scope_graph(
                [ScopeNode("a", deps=("b",)), ScopeNode("b", deps=("a",))]
            )


class ObserverTests(unittest.TestCase):
    def test_exact_observer(self) -> None:
        result = exact_observer_independent([2, 4, 8], lambda c: c % 2)
        self.assertTrue(result["independent"])

    def test_metric_observer(self) -> None:
        result = metric_observer_diameter([3, 4, 5], lambda c: 10 * c, 20)
        self.assertTrue(result["stable"])
        self.assertEqual(result["diameter"], 20)


if __name__ == "__main__":
    unittest.main(verbosity=2)
