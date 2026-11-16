from __future__ import annotations

import json
import unittest

from tapir_reference import (
    CertificateUse,
    EscapeMode,
    GraphError,
    Node,
    backward_slice,
    classify_escape,
    compile_graph,
    least_accepted,
    mixed_radix_decode,
    mixed_radix_encode,
    monotone_demand_closure,
    observer_diameter,
    run_decreasing_until_done,
    run_trace,
    spanning_tree_error,
    synthesize_strategy,
    topological_order,
    verify_strategy,
)


class TapirReferenceTests(unittest.TestCase):
    def sample_nodes(self) -> list[Node]:
        return [
            Node("unused", "U", residuals=("UnusedBoundary",)),
            Node("base", "A"),
            Node(
                "local_cert",
                "ExistsCert",
                deps=("base",),
                certificate=CertificateUse(),
            ),
            Node(
                "observer",
                "StableObservation",
                deps=("local_cert",),
                certificate=CertificateUse(
                    appears_in_public=True, observer_proved=True
                ),
            ),
            Node(
                "enumerate",
                "CompleteList",
                deps=("base",),
                residuals=("HeightBound", "CodeCoverage"),
            ),
            Node(
                "named",
                "LeastSolution",
                deps=("enumerate",),
                certificate=CertificateUse(explicitly_named=True),
            ),
            Node("root", "Goal", deps=("observer", "named")),
        ]

    def test_escape_modes(self) -> None:
        self.assertEqual(classify_escape(CertificateUse()), EscapeMode.LOCAL)
        self.assertEqual(
            classify_escape(
                CertificateUse(appears_in_public=True, observer_proved=True)
            ),
            EscapeMode.OBSERVED,
        )
        self.assertEqual(
            classify_escape(CertificateUse(appears_in_public=True)),
            EscapeMode.NAMED,
        )
        self.assertEqual(
            classify_escape(CertificateUse(explicitly_named=True)),
            EscapeMode.NAMED,
        )

    def test_backward_slice_removes_dead_nodes(self) -> None:
        reachable = backward_slice(self.sample_nodes(), "root")
        self.assertNotIn("unused", reachable)
        self.assertEqual(
            reachable,
            ("base", "local_cert", "observer", "enumerate", "named", "root"),
        )

    def test_stable_topological_order(self) -> None:
        nodes = self.sample_nodes()
        selected = backward_slice(nodes, "root")
        order = topological_order(nodes, selected)
        self.assertLess(order.index("base"), order.index("enumerate"))
        self.assertLess(order.index("enumerate"), order.index("named"))
        self.assertLess(order.index("observer"), order.index("root"))

    def test_compile_exact_residuals_and_modes(self) -> None:
        compiled = compile_graph(self.sample_nodes(), "root")
        self.assertEqual(compiled.residuals, ("HeightBound", "CodeCoverage"))
        self.assertEqual(
            dict(compiled.escape_modes),
            {
                "local_cert": EscapeMode.LOCAL,
                "observer": EscapeMode.OBSERVED,
                "named": EscapeMode.NAMED,
            },
        )
        json.dumps(compiled.to_json_obj())

    def test_duplicate_id_rejected(self) -> None:
        with self.assertRaisesRegex(GraphError, "duplicate node"):
            compile_graph([Node("x", "A"), Node("x", "B")], "x")

    def test_missing_dependency_rejected(self) -> None:
        with self.assertRaisesRegex(GraphError, "missing node"):
            compile_graph([Node("x", "A", deps=("y",))], "x")

    def test_cycle_rejected(self) -> None:
        nodes = [Node("x", "A", deps=("y",)), Node("y", "B", deps=("x",))]
        with self.assertRaisesRegex(GraphError, "cycle"):
            compile_graph(nodes, "x")

    def test_least_accepted(self) -> None:
        self.assertEqual(least_accepted(20, lambda x: x * x >= 30), 6)
        self.assertIsNone(least_accepted(4, lambda x: x > 9))
        with self.assertRaises(ValueError):
            least_accepted(-1, lambda _: True)

    def test_strategy_synthesis_and_verification(self) -> None:
        strategy = synthesize_strategy(
            6,
            lambda x: x + 3,
            lambda x, y: y >= x and (x + y) % 2 == 0,
        )
        self.assertIsNotNone(strategy)
        assert strategy is not None
        self.assertTrue(
            verify_strategy(
                strategy,
                lambda x: x + 3,
                lambda x, y: y >= x and (x + y) % 2 == 0,
            )
        )
        self.assertEqual(strategy, (0, 1, 2, 3, 4, 5))

    def test_strategy_failure(self) -> None:
        self.assertIsNone(synthesize_strategy(3, lambda _: 2, lambda x, y: x == 0))

    def test_mixed_radix_roundtrip(self) -> None:
        digits = (2, 1, 4, 0)
        radices = (3, 5, 7, 2)
        code = mixed_radix_encode(digits, radices)
        self.assertEqual(mixed_radix_decode(code, radices), digits)
        with self.assertRaises(ValueError):
            mixed_radix_encode((3,), (3,))
        with self.assertRaises(ValueError):
            mixed_radix_decode(100, (2, 2))

    def test_monotone_demand_closure(self) -> None:
        def demand(d: tuple[int, ...]) -> tuple[int, ...]:
            a, b, c = d
            return (min(4, b + 1), min(5, c + 2), min(3, a))

        result = monotone_demand_closure((0, 0, 0), (4, 5, 3), demand)
        self.assertEqual(result, (4, 5, 3))
        proposed = demand(result)
        self.assertTrue(all(p <= r for p, r in zip(proposed, result, strict=True)))

    def test_trace_and_invariant(self) -> None:
        states = run_trace(
            (0, 0),
            lambda t, state: (state[0] + 1, state[1] + 2 * t + 1),
            8,
            invariant=lambda t, state: state == (t, t * t),
        )
        self.assertEqual(states[-1], (8, 64))
        with self.assertRaisesRegex(GraphError, "invariant"):
            run_trace(0, lambda _t, x: x + 1, 2, lambda t, x: x == 2 * t)

    def test_decreasing_termination(self) -> None:
        states = run_decreasing_until_done(
            7,
            done=lambda x: x == 0,
            step=lambda x: x - 1,
            measure=lambda x: x,
        )
        self.assertEqual(states[-1], 0)
        self.assertLessEqual(len(states) - 1, 8)
        with self.assertRaisesRegex(GraphError, "strictly decrease"):
            run_decreasing_until_done(
                3, done=lambda x: x == 0, step=lambda x: x, measure=lambda x: x
            )

    def test_observer_diameter(self) -> None:
        self.assertAlmostEqual(observer_diameter([1.0, 1.25, 0.75], lambda x, y: abs(x - y)), 0.5)
        self.assertEqual(observer_diameter([], lambda x, y: 0.0), 0.0)

    def test_spanning_tree_error(self) -> None:
        parent = {"r": None, "a": "r", "b": "a", "c": "r"}
        errors = {("r", "a"): 0.1, ("a", "b"): 0.2, ("c", "r"): 0.4}
        total = spanning_tree_error("r", parent, errors)
        self.assertAlmostEqual(total["b"], 0.3)
        self.assertAlmostEqual(total["c"], 0.4)
        with self.assertRaisesRegex(GraphError, "cyclic or disconnected"):
            spanning_tree_error("r", {"r": None, "a": "b", "b": "a"}, {})


if __name__ == "__main__":
    unittest.main()
