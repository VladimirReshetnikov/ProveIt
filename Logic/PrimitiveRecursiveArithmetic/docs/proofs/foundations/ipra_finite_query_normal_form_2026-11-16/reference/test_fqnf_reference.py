from __future__ import annotations

import unittest
from fractions import Fraction
from itertools import product

from fqnf_reference import (
    FinitePathProblem,
    IntervalCertificate,
    complete_bounded_list,
    cubic_bisection,
    decode_digits,
    decode_mixed_radix,
    encode_digits,
    encode_mixed_radix,
    find_path_by_whole_code,
    greedy_path,
    independent_interval_stability,
    least_certificate,
    reverse_pipeline_demand,
    verify_complete_bounded_list,
    verify_cubic_bisection,
    verify_path,
)


class DigitCodingTests(unittest.TestCase):
    def test_uniform_round_trip_exhaustive(self) -> None:
        for base in range(2, 7):
            for length in range(5):
                for values in product(range(base), repeat=length):
                    code = encode_digits(values, base)
                    self.assertLess(code, base**length)
                    self.assertEqual(decode_digits(code, length, base), values)

    def test_mixed_radix_round_trip_exhaustive(self) -> None:
        radices = (2, 3, 4, 2)
        for values in product(*(range(r) for r in radices)):
            code = encode_mixed_radix(values, radices)
            self.assertLess(code, 2 * 3 * 4 * 2)
            self.assertEqual(decode_mixed_radix(code, radices), values)

    def test_invalid_digit_rejected(self) -> None:
        with self.assertRaises(ValueError):
            encode_digits((0, 3), 3)


class SelectionTests(unittest.TestCase):
    def test_least_certificate(self) -> None:
        selected = least_certificate(100, lambda code: code >= 17 and code % 7 == 3)
        self.assertEqual(selected, 17)

    def test_no_certificate(self) -> None:
        self.assertIsNone(least_certificate(12, lambda code: code > 20))

    def test_height_bound_to_complete_list(self) -> None:
        valid = lambda code: code * code <= 80 and code % 2 == 1
        values = complete_bounded_list(20, valid)
        self.assertEqual(values, (1, 3, 5, 7))
        self.assertTrue(verify_complete_bounded_list(20, valid, values))
        self.assertFalse(verify_complete_bounded_list(20, valid, values[:-1]))


class RelationalPathTests(unittest.TestCase):
    @staticmethod
    def problem() -> FinitePathProblem:
        # The least start 0 has a locally legal first move but no complete path.
        # Start 1 leads to the unique successful path (1,1,0).
        return FinitePathProblem(
            level_sizes=(2, 2, 2),
            start_ok=lambda state: state in (0, 1),
            edge_ok=lambda time, source, target: (
                (time == 0 and (source, target) in {(0, 0), (1, 1)})
                or (time == 1 and (source, target) == (1, 0))
            ),
            final_ok=lambda state: state == 0,
        )

    def test_greedy_can_fail(self) -> None:
        self.assertIsNone(greedy_path(self.problem()))

    def test_whole_path_certificate_succeeds(self) -> None:
        result = find_path_by_whole_code(self.problem())
        self.assertIsNotNone(result)
        assert result is not None
        code, path = result
        self.assertEqual(path, (1, 1, 0))
        self.assertEqual(code, encode_digits(path, self.problem().base))
        self.assertTrue(verify_path(self.problem(), path))


class StableObservationTests(unittest.TestCase):
    def test_independent_certificates(self) -> None:
        target = Fraction(7, 5)
        first = IntervalCertificate(4, Fraction(11, 8), Fraction(23, 16))
        second = IntervalCertificate(5, Fraction(44, 32), Fraction(45, 32))
        self.assertTrue(independent_interval_stability(first, second, target))


class TraceTests(unittest.TestCase):
    def test_exact_cubic_bisection(self) -> None:
        x = Fraction(2, 1)
        precision = 12
        lo, hi, trace = cubic_bisection(x, precision, Fraction(0), Fraction(2))
        self.assertTrue(
            verify_cubic_bisection(
                x,
                precision,
                Fraction(0),
                Fraction(2),
                lo,
                hi,
                trace,
            )
        )
        self.assertEqual(hi - lo, Fraction(2, 2**precision))

    def test_reverse_demand(self) -> None:
        # Last operation needs p+2 input bits; the earlier one doubles demand.
        demands = reverse_pipeline_demand(10, (lambda p: 2 * p, lambda p: p + 2))
        self.assertEqual(demands, (24, 12, 10))


if __name__ == "__main__":
    unittest.main(verbosity=2)
