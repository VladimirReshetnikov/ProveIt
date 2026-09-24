"""Independent regression tests; run with python -m unittest -v."""
import random
import unittest
from itertools import combinations_with_replacement
from math import prod

from a352969 import (ExpressionBuilder, PairBudgetExceeded, a352969,
                     ceil_log2, check_certificate, counting_bound_parameters,
                     maximum, minimum_depths, next_set, reachable,
                     reachable_cached, triangular_index, uniform_depth_bound)


class Tests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.stages = [reachable_cached(n) for n in range(7)]

    def test_published_terms_through_six(self):
        self.assertEqual([len(s) for s in self.stages],
                         [1, 2, 4, 11, 52, 678, 67144])

    def test_two_iterator_semantics(self):
        # Separate sum/prod comprehensions model the OEIS algorithm's logic.
        previous = {1}
        for n in range(1, 7):
            sums = {sum(pair) for pair in combinations_with_replacement(previous, 2)}
            products = {prod(pair) for pair in combinations_with_replacement(previous, 2)}
            previous = sums | products
            self.assertEqual(previous, self.stages[n])

    def test_ordered_pair_oracle(self):
        # Independent ordered Cartesian-pair enumeration through n=5.
        previous = {1}
        for n in range(1, 6):
            previous = ({x + y for x in previous for y in previous}
                        | {x * y for x in previous for y in previous})
            self.assertEqual(previous, self.stages[n])

    def test_value_indexed_oracle(self):
        heights = minimum_depths(2000)
        for n, values in enumerate(self.stages):
            for m in range(1, 2001):
                self.assertEqual(m in values, heights[m] <= n, (n, m))

    def test_iterative_and_cached_agree(self):
        for n in range(7):
            self.assertEqual(reachable(n), self.stages[n])

    def test_extrema_nesting_and_cardinality_bounds(self):
        for n, s in enumerate(self.stages):
            self.assertEqual(min(s), 1)
            self.assertEqual(max(s), maximum(n))
            if n:
                previous = self.stages[n - 1]
                self.assertTrue(previous <= s)
                self.assertGreaterEqual(len(s), 2 * len(previous))
            if n > 1:
                self.assertLessEqual(len(s), len(self.stages[n - 1]) ** 2)

    def test_unordered_iteration_does_not_require_sorting(self):
        values = [8, 1, 3, 2]
        expected = {x + y for x in values for y in values}
        expected |= {x * y for x in values for y in values}
        self.assertEqual(next_set(values), expected)
        self.assertEqual(next_set(reversed(values)), expected)

    def test_input_validation(self):
        for f in (reachable, reachable_cached, a352969):
            with self.assertRaises(ValueError):
                f(-1)
            for bad in (True, 2.0, "2", None):
                with self.assertRaises(TypeError):
                    f(bad)

    def test_invalid_values_are_checked_before_deduplication(self):
        for values in ([1, True], [1, 1.0], [1, 0], [], [1, -1]):
            with self.assertRaises(ValueError):
                next_set(values)

    def test_immutability(self):
        self.assertIsInstance(reachable_cached(3), frozenset)
        with self.assertRaises(AttributeError):
            reachable_cached(3).add(999)
        self.assertNotIn(999, reachable_cached(3))

    def test_budget_and_no_mutation(self):
        data = {1, 2, 4}
        old = data.copy()
        with self.assertRaises(PairBudgetExceeded):
            next_set(data, pair_budget=5)
        self.assertEqual(data, old)
        self.assertEqual(len(next_set(data, pair_budget=6)), 8)
        self.assertEqual(data, old)

    def test_triangular_parameters(self):
        for t in range(10000):
            r = triangular_index(t)
            self.assertLessEqual(t, r * (r + 1) // 2)
            if r:
                self.assertGreater(t, (r - 1) * r // 2)
        for n in range(16, 10000):
            p = counting_bound_parameters(n)
            self.assertLessEqual(p["k"], n)
            self.assertGreaterEqual(1 << p["t"], 2 * n)
            self.assertLess(1 << p["t"], 4 * n)

    def test_uniform_depth_recurrence(self):
        for t in range(1, 10000):
            r = triangular_index(t)
            q = t - r
            self.assertGreaterEqual(q, 0)
            self.assertLessEqual(q, (r - 1) * r // 2)
            self.assertLessEqual(uniform_depth_bound(q), t + 1)
            self.assertEqual(r + 1 + max(t + 1, uniform_depth_bound(q)),
                             uniform_depth_bound(t))

    def test_constructive_witnesses(self):
        rng = random.Random(352969)
        samples = list(range(1, 513))
        for bits in (16, 31, 64, 127, 256, 1024, 4096, 16384):
            samples += [rng.getrandbits(bits) | (1 << (bits - 1)),
                        (1 << bits) - 1, 1 << (bits - 1)]
        for value in samples:
            builder = ExpressionBuilder()
            root = builder.integer(value)
            actual_value, height = check_certificate(builder.certificate(root))
            self.assertEqual(actual_value, value)
            t = ceil_log2(value.bit_length())
            self.assertLessEqual(height, uniform_depth_bound(t))

    def test_power_depth_is_exact(self):
        builder = ExpressionBuilder()
        for exponent in range(1, 1001):
            root = builder.power_of_two(exponent)
            self.assertEqual(builder.values[root], 1 << exponent)
            self.assertEqual(builder.heights[root], 1 + ceil_log2(exponent))

    def test_certificate_rejects_bad_edges(self):
        with self.assertRaises(ValueError):
            check_certificate({"nodes": [{"op": "add", "left": 0, "right": 0}],
                               "root": 0, "value_hex": "0x2", "height": 1})


if __name__ == "__main__":
    unittest.main(verbosity=2)
