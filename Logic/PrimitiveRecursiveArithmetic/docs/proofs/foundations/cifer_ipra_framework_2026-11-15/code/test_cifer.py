from __future__ import annotations

import unittest
from fractions import Fraction

from cifer import (
    CiferError,
    Node,
    ProofGraph,
    backward_viability,
    check_cubic_trace,
    cubic_bisect,
    demand_closure,
    diameter,
    finite_height_bound,
    reachable_subgraph,
    residual_boundaries,
    residual_report,
    stable_observation,
)


class GraphTests(unittest.TestCase):
    def graph(self) -> ProofGraph:
        return ProofGraph(
            (
                Node("input-x", kind="input"),
                Node("height-bound", kind="boundary"),
                Node("analytic-constant", kind="boundary"),
                Node("bounded-enumeration", ("input-x", "height-bound")),
                Node("finite-verification", ("bounded-enumeration",)),
                Node("unused-lemma", ("analytic-constant",)),
                Node("goal", ("finite-verification",), kind="final"),
            )
        )

    def test_residual_prunes_irrelevant_boundary(self) -> None:
        g = self.graph()
        self.assertEqual(residual_boundaries(g, "goal"), ("height-bound",))
        self.assertNotIn("unused-lemma", reachable_subgraph(g, "goal"))

    def test_report(self) -> None:
        report = residual_report(self.graph(), "goal")
        self.assertFalse(report["closed"])
        self.assertEqual(report["residual_boundaries"], ["height-bound"])

    def test_closed_graph(self) -> None:
        g = ProofGraph(
            (
                Node("x", kind="input"),
                Node("calc", ("x",)),
                Node("goal", ("calc",), kind="final"),
            )
        )
        self.assertEqual(residual_boundaries(g, "goal"), ())

    def test_forward_dependency_rejected(self) -> None:
        g = ProofGraph(
            (
                Node("goal", ("later",), kind="final"),
                Node("later"),
            )
        )
        with self.assertRaises(CiferError):
            g.validate()


class DemandTests(unittest.TestCase):
    def test_closure_with_feedback(self) -> None:
        def transfer(d: tuple[int, ...]) -> tuple[int, ...]:
            a, b, c = d
            return (max(a, b + 1), max(b, c + 2), c)

        fixed, trace = demand_closure((0, 0, 3), (8, 8, 8), transfer)
        self.assertEqual(fixed, (6, 5, 3))
        self.assertEqual(trace[-1], fixed)
        self.assertLessEqual(len(trace), 17)

    def test_cap_failure_is_explicit(self) -> None:
        with self.assertRaises(CiferError):
            demand_closure((0,), (2,), lambda d: (d[0] + 1,))


class RelationalTests(unittest.TestCase):
    def test_lexicographically_least_viable_path(self) -> None:
        levels = [(0, 1, 2), (2, 3), (4, 5)]
        viable, path = backward_viability(
            levels, lambda k, x, y: abs(y - x) <= 2
        )
        self.assertEqual(path, (0, 2, 4))
        self.assertIn(0, viable[0])

    def test_no_path(self) -> None:
        viable, path = backward_viability([(0,), (10,)], lambda k, x, y: y == x)
        self.assertIsNone(path)
        self.assertFalse(viable[0])

    def test_stable_observer(self) -> None:
        cloud = [(3, "left"), (3, "right"), (3, "collision")]
        self.assertEqual(stable_observation(cloud, lambda x: x[0]), 3)
        with self.assertRaises(CiferError):
            stable_observation(cloud, lambda x: x[1])

    def test_diameter(self) -> None:
        self.assertEqual(
            diameter([Fraction(1, 3), Fraction(2, 5), Fraction(7, 20)]),
            Fraction(1, 15),
        )


class FiniteSearchTests(unittest.TestCase):
    def test_list_gives_height_bound(self) -> None:
        points = [(-1, 2), (5, 1), (3, 7)]
        h = finite_height_bound(points, lambda p: max(abs(p[0]), abs(p[1])))
        self.assertEqual(h, 7)


class CubicTests(unittest.TestCase):
    def test_exact_trace(self) -> None:
        interval, trace = cubic_bisect(Fraction(7, 5), 12)
        self.assertTrue(check_cubic_trace(Fraction(7, 5), trace))
        self.assertEqual(interval.width, trace[0].width / (2**12))
        self.assertLess(interval.width, Fraction(1, 500))

    def test_monotone_root_bracket(self) -> None:
        for x in [Fraction(-4), Fraction(0), Fraction(3, 2), Fraction(17, 3)]:
            _, trace = cubic_bisect(x, 20)
            self.assertTrue(check_cubic_trace(x, trace))


if __name__ == "__main__":
    unittest.main(verbosity=2)
