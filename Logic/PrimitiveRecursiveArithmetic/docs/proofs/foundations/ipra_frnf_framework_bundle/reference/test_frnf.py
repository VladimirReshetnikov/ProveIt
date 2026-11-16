from fractions import Fraction
import math
import unittest

from frnf import (
    DemandNode,
    DemandPair,
    DualHorizon,
    EdgeDemand,
    Layer,
    backward_viability,
    bounded_least,
    diameter,
    euclid_majorized,
    exact_label_from_gap,
    finite_net_minimum,
    guarded_reciprocal_error,
    reverse_demand_closure,
    stable_observation,
)


class FRNFTests(unittest.TestCase):
    def test_bounded_least(self):
        self.assertEqual(bounded_least(lambda i: i * i >= 20, 10), 5)
        self.assertEqual(bounded_least(lambda i: False, 7), 7)

    def test_dual_horizon_composition(self):
        inner = DualHorizon(lambda d: d + 1, lambda d: 2 * d + 3, "inner")
        outer = DualHorizon(lambda d: 2 * d, lambda d: 3 * d + 1, "outer")
        composed = inner.then(outer)
        composed.check(20)
        self.assertEqual(composed.read(4), 9)
        self.assertEqual(composed.justify(4), 29)
        self.assertGreater(composed.justify(4), composed.read(4))

    def test_reverse_demand_closure(self):
        raw_to_mid = DualHorizon(lambda d: d + 2, lambda d: d + 5, "raw-to-mid")
        mid_to_root = DualHorizon(lambda d: 2 * d, lambda d: 2 * d + 3, "mid-to-root")
        side_to_root = DualHorizon(lambda d: d, lambda d: d + 7, "side-to-root")
        nodes = [
            DemandNode("raw"),
            DemandNode("side"),
            DemandNode("mid", (EdgeDemand("raw", raw_to_mid),)),
            DemandNode(
                "root",
                (EdgeDemand("mid", mid_to_root), EdgeDemand("side", side_to_root)),
            ),
        ]
        closure = reverse_demand_closure(nodes, "root", 4)
        self.assertEqual(closure["root"], DemandPair(4, 4))
        self.assertEqual(closure["mid"], DemandPair(8, 11))
        self.assertEqual(closure["raw"], DemandPair(10, 16))
        self.assertEqual(closure["side"], DemandPair(4, 11))

    def test_reverse_demand_closure_skips_unreachable(self):
        explosive = DualHorizon(lambda d: d + 100, lambda d: d + 200, "unused")
        nodes = [
            DemandNode("unused_source"),
            DemandNode("used_source"),
            DemandNode("unused", (EdgeDemand("unused_source", explosive),)),
            DemandNode(
                "root",
                (EdgeDemand("used_source", DualHorizon(lambda d: d, lambda d: d)),),
            ),
        ]
        closure = reverse_demand_closure(nodes, "root", 0)
        self.assertEqual(closure["root"], DemandPair(0, 0))
        self.assertEqual(closure["used_source"], DemandPair(0, 0))
        self.assertIsNone(closure["unused"])
        self.assertIsNone(closure["unused_source"])

    def test_backward_viability(self):
        layers = [
            Layer.from_iterable([0, 1, 2]),
            Layer.from_iterable([1, 3]),
            Layer.from_iterable([4]),
        ]
        result = backward_viability(layers, lambda _i, a, b: abs(a - b) <= 2)
        self.assertEqual(result.path, (1, 3, 4))
        self.assertNotIn(0, result.viable[0])

    def test_backward_viability_no_path(self):
        layers = [Layer.from_iterable([0]), Layer.from_iterable([10])]
        with self.assertRaises(ValueError):
            backward_viability(layers, lambda _i, a, b: abs(a - b) <= 1)

    def test_euclid_majorized(self):
        g, trace = euclid_majorized(1071, 462)
        self.assertEqual(g, math.gcd(1071, 462))
        self.assertEqual(trace[-1][1], 0)
        self.assertLessEqual(len(trace), 462 + 2)

    def test_finite_net_minimum(self):
        points = [Fraction(i, 4) for i in range(-4, 5)]
        result = finite_net_minimum(points, lambda x: (x - Fraction(1, 3)) ** 2)
        self.assertEqual(result.point, Fraction(1, 4))

    def test_stable_observation(self):
        values = [Fraction(10, 16), Fraction(11, 16), Fraction(10, 16)]
        self.assertEqual(diameter(values), Fraction(1, 16))
        self.assertEqual(stable_observation(values, Fraction(1, 16)), Fraction(10, 16))
        with self.assertRaises(ValueError):
            stable_observation(values, Fraction(1, 32))

    def test_exact_label_from_gap(self):
        label = exact_label_from_gap(
            [Fraction(100, 1000), Fraction(101, 1000)],
            ["left", "left"],
            separation=Fraction(1, 10),
            error=Fraction(1, 100),
        )
        self.assertEqual(label, "left")

    def test_guarded_reciprocal_bound(self):
        self.assertEqual(
            guarded_reciprocal_error(Fraction(1, 1024), Fraction(1, 4)),
            Fraction(1, 32),
        )
        with self.assertRaises(ValueError):
            guarded_reciprocal_error(Fraction(1, 8), Fraction(0, 1))


if __name__ == "__main__":
    unittest.main()
