from __future__ import annotations

import unittest
from fractions import Fraction

from finer_reference import (
    CubicBisectionCertificate,
    DemandClosure,
    TreeEdge,
    backward_viability,
    bounded_complete_list,
    certificate_space_size,
    cubic_bisection,
    cubic_value,
    exact_observer_invariant,
    least_accepted,
    mixed_radix_decode,
    mixed_radix_encode,
    monotone_demand_closure,
    observer_diameter,
    spanning_tree_distances,
    verify_complete_list,
    verify_cubic_bisection,
    verify_demand_closure,
    verify_least_prefixed,
    verify_metric_gluing,
    verify_search_result,
    verify_viability,
)


class FinerReferenceTests(unittest.TestCase):
    def test_mixed_radix_roundtrip(self) -> None:
        radices = [2, 3, 5, 7]
        self.assertEqual(certificate_space_size(radices), 210)
        for code in range(210):
            digits = mixed_radix_decode(code, radices)
            self.assertEqual(mixed_radix_encode(digits, radices), code)

    def test_mixed_radix_rejects_overflow(self) -> None:
        with self.assertRaises(ValueError):
            mixed_radix_decode(12, [2, 2])
        with self.assertRaises(ValueError):
            mixed_radix_encode([2], [2])

    def test_least_accepted_success(self) -> None:
        r = least_accepted(20, lambda c: c >= 7 and c % 7 == 0)
        self.assertTrue(r.found)
        self.assertEqual(r.code, 7)
        self.assertTrue(verify_search_result(r, lambda c: c >= 7 and c % 7 == 0))

    def test_least_accepted_failure(self) -> None:
        r = least_accepted(9, lambda _c: False)
        self.assertFalse(r.found)
        self.assertEqual(r.code, 9)
        self.assertTrue(verify_search_result(r, lambda _c: False))

    def test_cyclic_demand_closure(self) -> None:
        caps = (4, 5, 3)

        def f(x: tuple[int, ...]) -> tuple[int, ...]:
            a, b, c = x
            return min(4, b), min(5, c + 2), min(3, a + 1)

        cert = monotone_demand_closure(caps, f)
        self.assertTrue(verify_demand_closure(cert, f))
        self.assertTrue(verify_least_prefixed(cert.closure, caps, f))
        self.assertLessEqual(cert.stabilized_at, sum(caps))
        self.assertEqual(cert.closure, (4, 5, 3))

    def test_nontrivial_least_prefixed(self) -> None:
        caps = (5, 5)

        def f(x: tuple[int, ...]) -> tuple[int, ...]:
            a, b = x
            return min(5, b + 1), min(5, a)

        cert = monotone_demand_closure(caps, f)
        self.assertTrue(verify_least_prefixed(cert.closure, caps, f))
        self.assertEqual(cert.closure, (5, 5))

    def test_viable_relational_path(self) -> None:
        layers = [[0, 1], [0, 1, 2], [0, 1, 2, 3]]
        edge = lambda i, x, y: y in {x, x + 1}
        accept = lambda x: x == 3
        cert = backward_viability(layers, edge, accept)
        self.assertTrue(verify_viability(cert, edge, accept))
        self.assertEqual(cert.path, (1, 2, 3))

    def test_no_viable_path(self) -> None:
        layers = [[0], [0], [0]]
        edge = lambda i, x, y: x == y
        accept = lambda x: x == 1
        cert = backward_viability(layers, edge, accept)
        self.assertIsNone(cert.path)
        self.assertTrue(verify_viability(cert, edge, accept))

    def test_exact_observer(self) -> None:
        self.assertTrue(exact_observer_invariant([17, 17, 17]))
        self.assertFalse(exact_observer_invariant([17, 18]))

    def test_metric_observer(self) -> None:
        vals = [Fraction(1, 3), Fraction(5, 12), Fraction(3, 8)]
        self.assertEqual(observer_diameter(vals), Fraction(1, 12))

    def test_metric_gluing_tree(self) -> None:
        edges = [
            TreeEdge("A", "B", Fraction(1, 10)),
            TreeEdge("B", "C", Fraction(1, 20)),
            TreeEdge("B", "D", Fraction(1, 8)),
        ]
        values = {
            "A": Fraction(0),
            "B": Fraction(1, 20),
            "C": Fraction(1, 10),
            "D": Fraction(3, 20),
        }
        dist = spanning_tree_distances("A", edges)
        self.assertEqual(dist["D"], Fraction(9, 40))
        self.assertTrue(verify_metric_gluing("A", values, edges))

    def test_height_list(self) -> None:
        pred = lambda n: n * n <= 70 and n % 3 == 1
        values = bounded_complete_list(10, pred)
        self.assertEqual(values, [1, 4, 7])
        self.assertTrue(verify_complete_list(10, values, pred))

    def test_cubic_bisection(self) -> None:
        cert = cubic_bisection(Fraction(2), Fraction(0), Fraction(2), 12)
        self.assertTrue(verify_cubic_bisection(cert))
        self.assertLessEqual(cubic_value(cert.final_lo, cert.x), 0)
        self.assertGreaterEqual(cubic_value(cert.final_hi, cert.x), 0)
        self.assertEqual(cert.final_hi - cert.final_lo, Fraction(1, 2048))

    def test_cubic_tamper_detected(self) -> None:
        cert = cubic_bisection(Fraction(1), Fraction(0), Fraction(1), 5)
        bad = CubicBisectionCertificate(
            cert.x,
            cert.initial_lo,
            cert.initial_hi,
            cert.steps,
            cert.final_lo,
            cert.final_hi + Fraction(1, 100),
        )
        self.assertFalse(verify_cubic_bisection(bad))


if __name__ == "__main__":
    unittest.main(verbosity=2)
