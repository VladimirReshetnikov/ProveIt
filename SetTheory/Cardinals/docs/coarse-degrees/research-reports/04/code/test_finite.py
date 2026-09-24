"""Reproducible finite checks. Run: python -m unittest -v test_finite.py"""
from __future__ import annotations

from fractions import Fraction
from itertools import product
import random
import unittest

from density_coding import (
    approximation_prefix, column, column_count, column_element,
    error_bound, error_count, majority_on_column, power_index,
    replication_prefix, sparse_encode_prefix, tail_count,
)
from finite_split import (
    Lock, TableFunctional, bits_of, find_split, finite_no_split_property,
)


class DensityChecks(unittest.TestCase):
    def test_column_partition_and_counts(self) -> None:
        # 257 prefix lengths, nine column indices: 2,313 exact count checks.
        for n in range(257):
            for k in range(9):
                self.assertEqual(column_count(k, n),
                                 sum(column(x) == k for x in range(n)))
                self.assertEqual(tail_count(k, n),
                                 sum(column(x) >= k for x in range(n)))
            self.assertEqual(sum(column_count(k, n) for k in range(9)), n)

    def test_column_enumeration(self) -> None:
        for k in range(12):
            values = [column_element(k, j) for j in range(100)]
            self.assertEqual(values, sorted(set(values)))
            self.assertTrue(all(column(x) == k for x in values))

    def test_finite_column_error_bound_exhaustive(self) -> None:
        # Exhaust all error sets in all prefixes through length twelve,
        # whenever the stipulated finite-lock hypothesis holds.
        for n in range(1, 13):
            for mask in range(1 << n):
                errors = [x for x in range(n) if mask & (1 << x)]
                for k in range(4):
                    for m in (0, n // 2, n):
                        if all(x < m or column(x) >= k for x in errors):
                            self.assertLessEqual(Fraction(len(errors), n),
                                                 error_bound(n, k, m))

    def test_limit_coding_finite_stabilization(self) -> None:
        oracle = lambda k: (k * k + k // 2 + 1) % 2
        deadline = lambda k: (k + 1) ** 3
        approx = lambda k, s: oracle(k) if s >= deadline(k) else 1 - oracle(k)
        n = 4096
        real = replication_prefix(oracle, n)
        trial = approximation_prefix(approx, n)
        for k in range(1, 8):
            m = max(deadline(j) for j in range(k))
            self.assertTrue(all(trial[x] == real[x]
                                for x in range(m, n) if column(x) < k))
            self.assertLessEqual(Fraction(error_count(real, trial), n),
                                 error_bound(n, k, m))

    def test_majority_after_finitely_many_column_errors(self) -> None:
        oracle = lambda k: k % 2
        def description(x: int) -> int:
            k = column(x)
            return 1 - oracle(k) if x < 80 else oracle(k)
        for k in range(8):
            self.assertEqual(majority_on_column(description, k, 200), oracle(k))

    def test_sparse_recovery(self) -> None:
        base = lambda n: (n // 3) % 2
        extra = lambda n: (n.bit_count() + 1) % 2
        n = 4097
        encoded = sparse_encode_prefix(base, extra, n)
        for x, value in enumerate(encoded):
            j = power_index(x)
            self.assertEqual(value, base(x) if j is None else extra(j))
        for j in range(13):
            self.assertEqual(encoded[1 << j], extra(j))
        self.assertLessEqual(sum(encoded[x] != base(x) for x in range(n)), 13)

    def test_invalid_arithmetic_arguments(self) -> None:
        for value in (-1, 1.5, True):
            with self.assertRaises(ValueError):
                column(value)
        with self.assertRaises(ValueError):
            error_bound(0, 1, 1)
        with self.assertRaises(ValueError):
            replication_prefix(lambda k: 2, 10)


class SplittingChecks(unittest.TestCase):
    def test_lock_extensions_and_refinements(self) -> None:
        for k in range(4):
            for values in product((0, 1), repeat=k):
                for stem_length in range(3):
                    for stem in product((0, 1), repeat=stem_length):
                        lock = Lock(stem, values)
                        extensions = tuple(lock.extensions(7))
                        self.assertTrue(extensions)
                        self.assertTrue(all(lock.admits(t) for t in extensions))
                        for tau in extensions[:3]:
                            for mu in lock.refine(tau).extensions(9):
                                self.assertTrue(lock.admits(mu))
                            for bit in (0, 1):
                                for mu in lock.refine(tau).add_column(bit).extensions(9):
                                    self.assertTrue(lock.admits(mu))

    def test_exhaustive_partial_tables(self) -> None:
        # All 81 one-input partial Boolean tables on two oracle bits,
        # paired against one another: 6,561 exact finite splitting problems.
        tables = [TableFunctional(2, (tuple(row),))
                  for row in product((None, 0, 1), repeat=4)]
        empty = Lock((), ())
        no_split = 0
        for phi in tables:
            for psi in tables:
                witness = find_split(empty, empty, phi, psi)
                if witness is None:
                    no_split += 1
                    self.assertTrue(finite_no_split_property(empty, empty, phi, psi))
                else:
                    self.assertNotEqual(witness.left_output, witness.right_output)
                    self.assertEqual(phi.value(witness.left, witness.input),
                                     witness.left_output)
                    self.assertEqual(psi.value(witness.right, witness.input),
                                     witness.right_output)
        self.assertEqual(no_split, 611)

    def test_random_locked_finite_tables(self) -> None:
        # Fixed seed and explicit finite tables; no probabilistic theorem is claimed.
        rng = random.Random(20260918)
        for _ in range(400):
            width = 4
            left = Lock(tuple(rng.randrange(2) for _ in range(rng.randrange(3))),
                        tuple(rng.randrange(2) for _ in range(rng.randrange(3))))
            right = Lock(tuple(rng.randrange(2) for _ in range(rng.randrange(3))),
                         tuple(rng.randrange(2) for _ in range(rng.randrange(3))))
            rows1 = tuple(tuple(rng.choice((None, 0, 1, 2))
                                for _ in range(1 << width)) for _ in range(3))
            rows2 = tuple(tuple(rng.choice((None, 0, 1, 2))
                                for _ in range(1 << width)) for _ in range(3))
            phi, psi = TableFunctional(width, rows1), TableFunctional(width, rows2)
            witness = find_split(left, right, phi, psi)
            if witness is None:
                self.assertTrue(finite_no_split_property(left, right, phi, psi))
            else:
                self.assertTrue(left.admits(witness.left))
                self.assertTrue(right.admits(witness.right))
                self.assertNotEqual(witness.left_output, witness.right_output)
                for tau in left.refine(witness.left).extensions(width + 2):
                    self.assertEqual(phi.value(tau, witness.input), witness.left_output)

    def test_total_common_output_in_no_split_case(self) -> None:
        left = Lock((0,), (0,))
        right = Lock((1,), (0,))
        const = TableFunctional(3, ((7,) * 8, (11,) * 8))
        self.assertIsNone(find_split(left, right, const, const))
        self.assertTrue(finite_no_split_property(left, right, const, const))

    def test_finite_model_rejects_missing_support(self) -> None:
        phi = TableFunctional(2, ((0, 1, 0, 1),))
        with self.assertRaises(ValueError):
            phi.value((0,), 0)
        with self.assertRaises(ValueError):
            Lock((0,), ()).refine((1,))
        for n in (-1, 1, True):
            with self.assertRaises(ValueError):
                phi.value((0, 0), n)
        for n, width in ((-1, 2), (4, 2), (0, -1)):
            with self.assertRaises(ValueError):
                bits_of(n, width)


if __name__ == "__main__":
    unittest.main(verbosity=2)
