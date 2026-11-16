from __future__ import annotations

import unittest
from fractions import Fraction
from math import floor

from ocipra import (
    ContractDAG,
    ContractError,
    DeterministicNode,
    FiniteCloudSystem,
    TheoremProfile,
    classify_profile,
    least_bounded,
    monotone_closure,
)


class SearchTests(unittest.TestCase):
    def test_least_witness(self) -> None:
        cert = least_bounded(lambda n: n * n >= 30, 10)
        self.assertTrue(cert.found)
        self.assertEqual(cert.witness, 6)
        self.assertTrue(cert.verify(lambda n: n * n >= 30))

    def test_search_failure_is_total(self) -> None:
        cert = least_bounded(lambda n: n > 100, 7)
        self.assertFalse(cert.found)
        self.assertEqual(cert.witness, 0)
        self.assertTrue(cert.verify(lambda n: n > 100))


class ClosureTests(unittest.TestCase):
    def test_monotone_closure(self) -> None:
        def transform(v: tuple[int, int]) -> tuple[int, int]:
            a, b = v
            return min(10, b + 1), min(10, (a + 1) // 2 + 2)

        cert = monotone_closure((2, 1), (10, 10), transform, check_monotone=True)
        self.assertTrue(cert.verify(transform))
        self.assertEqual(cert.result, (6, 5))
        self.assertLessEqual(len(cert.steps), 1 + (10 - 2) + (10 - 1))

    def test_closure_rejects_insufficient_box(self) -> None:
        with self.assertRaises(ContractError):
            monotone_closure((0,), (2,), lambda v: (v[0] + 1,))


class DAGTests(unittest.TestCase):
    def make_dag(self) -> ContractDAG:
        return ContractDAG(
            [
                DeterministicNode(
                    "sum",
                    ("x", "y"),
                    lambda p: {"x": p + 1, "y": p + 1},
                    lambda d, _p: d["x"] + d["y"],
                    lambda d, _p, out: out == d["x"] + d["y"],
                ),
                DeterministicNode(
                    "square",
                    ("sum",),
                    lambda p: {"sum": p + 2},
                    lambda d, _p: d["sum"] ** 2,
                    lambda d, _p, out: out == d["sum"] ** 2,
                ),
                DeterministicNode(
                    "out",
                    ("square", "x"),
                    lambda p: {"square": p + 1, "x": p + 1},
                    lambda d, _p: d["square"] + d["x"],
                    lambda d, _p, out: out == d["square"] + d["x"],
                ),
            ],
            external_inputs={"x", "y"},
        )

    def test_reverse_demand_and_replay(self) -> None:
        dag = self.make_dag()
        run = dag.run({"x": 3, "y": 4}, "out", 2)
        self.assertEqual(run.output, 52)
        self.assertEqual(run.demand_map(), {"out": 2, "square": 3, "sum": 5, "x": 6, "y": 6})
        self.assertTrue(dag.verify_run({"x": 3, "y": 4}, run))

    def test_bad_topological_order_is_rejected(self) -> None:
        node = DeterministicNode(
            "late", ("missing",), lambda p: {"missing": p}, lambda d, _p: 0,
            lambda _d, _p, out: out == 0,
        )
        with self.assertRaises(ContractError):
            ContractDAG([node])


class CloudTests(unittest.TestCase):
    def make_cloud(self) -> FiniteCloudSystem:
        return FiniteCloudSystem(
            layers=[
                [Fraction(1), Fraction(2)],
                [Fraction(3, 2), Fraction(4, 3)],
                [Fraction(7, 5), Fraction(17, 12)],
                [Fraction(41, 29), Fraction(99, 70)],
            ],
            compatible=lambda i, a, b: abs(a - b) <= Fraction(1, 2 ** (i + 1)),
            terminal_good=lambda q: abs(q * q - 2) <= Fraction(1, 100),
        )

    def test_backward_viability_and_least_path(self) -> None:
        cloud = self.make_cloud()
        path = cloud.least_path()
        self.assertEqual(path[0], Fraction(1))
        self.assertTrue(abs(path[-1] * path[-1] - 2) <= Fraction(1, 100))

    def test_stable_observables(self) -> None:
        cloud = self.make_cloud()
        invariant, value = cloud.observable_invariant(floor)
        self.assertTrue(invariant)
        self.assertEqual(value, 1)
        self.assertLess(cloud.observable_diameter(lambda q: q), Fraction(1, 100))


class ClassificationTests(unittest.TestCase):
    def test_internalizable(self) -> None:
        report = classify_profile(
            TheoremProfile(
                "finite identity", True, True, True, True, True,
            )
        )
        self.assertEqual(report.classification, "object-internalizable")

    def test_collision_reformulation(self) -> None:
        report = classify_profile(
            TheoremProfile(
                "root label", True, True, True, True, True,
                exact_selector_requested=True,
                collisions_possible=True,
                separation_gap_supplied=False,
            )
        )
        self.assertEqual(report.classification, "reformulate-relationally")

    def test_missing_height_is_conditional(self) -> None:
        report = classify_profile(
            TheoremProfile(
                "finite points", True, True, True, True, False,
                finiteness_used=True,
                height_or_complete_list_supplied=False,
            )
        )
        self.assertEqual(report.classification, "conditional-on-producer")


if __name__ == "__main__":
    unittest.main(verbosity=2)
