from fractions import Fraction
import unittest

from certificate_kernel import (
    EdgeDemand,
    all_below,
    any_below,
    bounded_enumerate,
    check_coherent_path,
    coherent_path,
    cubic_bisect,
    cubic_certificate,
    cubic_f,
    cubic_quantitative_unique,
    demands_adequate,
    first_true,
    gap_decide,
    list_is_complete_below,
    pair,
    reverse_demands,
    unpair,
    verify_cubic_interval,
    verify_gap_decision,
)


class CertificateKernelTests(unittest.TestCase):
    def test_pair_roundtrip_grid(self) -> None:
        for a in range(12):
            for b in range(30):
                self.assertEqual(unpair(pair(a, b)), (a, b))

    def test_boolean_folds(self) -> None:
        self.assertTrue(all_below(10, lambda i: i < 10))
        self.assertFalse(all_below(10, lambda i: i != 7))
        self.assertTrue(any_below(10, lambda i: i == 7))
        self.assertFalse(any_below(10, lambda i: i == 12))

    def test_first_true_and_sentinel(self) -> None:
        self.assertEqual(first_true(20, lambda i: i * i >= 50), 8)
        self.assertEqual(first_true(5, lambda i: False), 5)

    def test_reverse_demands(self) -> None:
        # 0 -> 1 needs q+1; 0 -> 2 needs 2q; 1 -> 3 needs q+2;
        # 2 -> 3 needs q+3.
        parents = [
            [],
            [EdgeDemand(0, offset=1)],
            [EdgeDemand(0, scale=2)],
            [EdgeDemand(1, offset=2), EdgeDemand(2, offset=3)],
        ]
        req = reverse_demands(parents, [0, 0, 0, 6])
        self.assertEqual(req, [18, 8, 9, 6])
        self.assertTrue(demands_adequate(parents, req))

    def test_relational_path_skips_dead_end(self) -> None:
        levels = [[0, 1], [10, 11], [20, 21]]
        allowed = {
            (0, 0, 10),  # dead at next level
            (0, 1, 11),
            (1, 11, 21),
        }
        compat = lambda k, c, d: (k, c, d) in allowed
        path = coherent_path(levels, compat)
        self.assertEqual(path, [1, 11, 21])
        self.assertTrue(check_coherent_path(path, levels, compat))

    def test_gap_decision(self) -> None:
        delta = Fraction(1, 2)
        err = Fraction(1, 16)
        self.assertEqual(gap_decide(Fraction(1, 32), err, delta), "zero")
        self.assertEqual(gap_decide(Fraction(23, 32), err, delta), "apart")
        self.assertTrue(verify_gap_decision(Fraction(0), Fraction(1, 32), err, delta))
        self.assertTrue(
            verify_gap_decision(Fraction(3, 4), Fraction(23, 32), err, delta)
        )

    def test_bounded_enumerator(self) -> None:
        pred = lambda n: n * n <= 30 and n % 2 == 1
        values = bounded_enumerate(20, pred)
        self.assertEqual(values, [1, 3, 5])
        self.assertTrue(list_is_complete_below(values, 20, pred))

    def test_cubic_invariant_many_inputs(self) -> None:
        for numerator in range(17):
            x = Fraction(numerator, 16)
            for steps in (0, 1, 2, 5, 10):
                lo, hi = cubic_bisect(x, steps)
                self.assertTrue(verify_cubic_interval(x, steps, lo, hi))
                center = (lo + hi) / 2
                self.assertLessEqual(
                    abs(cubic_f(x, center)), Fraction(4, 1 << steps)
                )

    def test_cubic_regular_centers(self) -> None:
        x = Fraction(7, 13)
        centers = []
        for n in range(1, 13):
            lo, hi = cubic_bisect(x, n)
            centers.append((lo + hi) / 2)
        for i, ci in enumerate(centers):
            n = i + 1
            for cj in centers[i:]:
                self.assertLessEqual(abs(cj - ci), Fraction(1, 1 << n))

    def test_cubic_quantitative_uniqueness(self) -> None:
        x = Fraction(1, 2)
        lo, hi = cubic_bisect(x, 12)
        eps = max(abs(cubic_f(x, lo)), abs(cubic_f(x, hi)))
        self.assertTrue(cubic_quantitative_unique(x, lo, hi, eps))
        self.assertLessEqual(abs(lo - hi), 2 * eps)

    def test_cubic_certificate(self) -> None:
        cert = cubic_certificate(Fraction(1, 2), 14)
        self.assertEqual(cert["width"], str(Fraction(1, 1 << 14)))


if __name__ == "__main__":
    unittest.main(verbosity=2)
