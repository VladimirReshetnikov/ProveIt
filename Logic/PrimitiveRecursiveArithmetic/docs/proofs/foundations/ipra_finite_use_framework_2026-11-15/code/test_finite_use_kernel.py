#!/usr/bin/env python3
from fractions import Fraction
import unittest

from finite_use_kernel import (
    ErrorNode,
    check_transcript,
    enumerate_integer_points,
    find_metastable_window,
    first_true,
    height_of_points,
    propagate_error_dag,
    select_sqrt_chain,
    select_transcript,
    sqrt_chain_machine,
    sqrt_candidates,
    viability_solver,
    window_stable,
)


class FiniteUseKernelTests(unittest.TestCase):
    def test_first_true(self) -> None:
        self.assertEqual(first_true(10, lambda i: i * i >= 20), 5)
        self.assertIsNone(first_true(4, lambda i: i > 9))

    def test_sqrt_candidate_nonempty(self) -> None:
        for level in range(10):
            candidates = sqrt_candidates(Fraction(2), level)
            self.assertTrue(candidates)
            self.assertTrue(
                all(abs(q * q - 2) <= Fraction(4, 1 << level) for q in candidates)
            )

    def test_sqrt_chain(self) -> None:
        chain = select_sqrt_chain(Fraction(2), 10)
        self.assertEqual(len(chain), 10)
        for level, q in enumerate(chain):
            self.assertLessEqual(abs(q * q - 2), Fraction(4, 1 << level))
            if level:
                self.assertLessEqual(abs(q - chain[level - 1]), Fraction(2, 1 << (level - 1)))

    def test_transcript_replay(self) -> None:
        machine, _ = sqrt_chain_machine(Fraction(2), 7)
        transcript = select_transcript(machine, 7, (0, None))
        self.assertTrue(check_transcript(machine, 7, transcript))

    def test_viability_rejects_short_resource(self) -> None:
        machine, _ = sqrt_chain_machine(Fraction(2), 5)
        viable, _ = viability_solver(machine)
        self.assertFalse(viable(4, (0, None)))
        self.assertTrue(viable(5, (0, None)))

    def test_error_dag(self) -> None:
        nodes = (
            ErrorNode(Fraction(1, 16)),
            ErrorNode(Fraction(1, 32), ((0, Fraction(2)),)),
            ErrorNode(Fraction(0), ((0, Fraction(1, 2)), (1, Fraction(3)))),
        )
        budgets = propagate_error_dag(nodes)
        self.assertEqual(budgets[0], Fraction(1, 16))
        self.assertEqual(budgets[1], Fraction(5, 32))
        self.assertEqual(budgets[2], Fraction(1, 2))

    def test_metastable_window(self) -> None:
        sequence = lambda n: Fraction(n, n + 8)
        challenge = lambda n: 4
        start, _ = find_metastable_window(
            sequence, challenge, Fraction(1, 20), rank_bound=40
        )
        self.assertTrue(window_stable(sequence, start, challenge(start), Fraction(1, 20)))

    def test_height_enumeration(self) -> None:
        points = enumerate_integer_points(3, lambda x, y: x * x + y * y == 5)
        expected = {
            (-2, -1), (-2, 1), (-1, -2), (-1, 2),
            (1, -2), (1, 2), (2, -1), (2, 1),
        }
        self.assertEqual(set(points), expected)
        self.assertEqual(height_of_points(points), 2)


if __name__ == "__main__":
    unittest.main(verbosity=2)
