"""Independent and same-kernel validation of exact one-run extrapolation."""
from __future__ import annotations

import unittest
from random import Random

from fastunknot.twist.core import (
    Budget, ResourceLimit, Run, components, homology,
)
from fastunknot.twist.reference import cube_homology
from fastunknot.twist.tail import (
    expand_profile, profile_dimension, profile_rank, tail_homology,
    tail_recognize,
)


def expand_word(runs):
    return [r.generator * (1 if r.exponent > 0 else -1)
            for r in runs for _ in range(abs(r.exponent))]


class ExactRecurrence(unittest.TestCase):
    def compare_macro(self, strands, runs, index=None):
        answer = tail_homology(strands, runs, run_index=index, check_d2=True)
        reference = homology(strands, runs, check_d2=True)
        self.assertEqual(expand_profile(answer['degree_profile']),
                         reference['by_degree'])
        self.assertEqual(answer['reduced_rank'], reference['reduced_rank'])
        self.assertEqual(answer['components'], reference['components'])
        self.assertEqual(profile_rank(answer['degree_profile']),
                         reference['reduced_rank'])
        return answer

    def test_both_signs_at_and_after_threshold(self):
        for sign in (-1, 1):
            for m in range(1, 11):
                with self.subTest(sign=sign, magnitude=m):
                    self.compare_macro(2, [Run(1, sign*m)])

    def test_arbitrary_run_positions_and_signs(self):
        others = [Run(1, 2), Run(2, -1), Run(3, 1)]
        for index in range(len(others) + 1):
            for sign in (-1, 1):
                for delta in (0, 1, 2, 5):
                    runs = others[:index] + [Run(2, sign*(6+delta))] + others[index:]
                    with self.subTest(index=index, sign=sign, delta=delta):
                        self.compare_macro(4, runs, index)

    def test_seeded_400_macro_comparisons(self):
        rng = Random(0x7A112026)
        for case in range(400):
            strands = rng.randrange(2, 5)
            others = [Run(rng.randrange(1, strands), rng.choice((-2, -1, 1, 2)))
                      for _ in range(rng.randrange(4))]
            index = rng.randrange(len(others) + 1)
            w = sum(abs(r.exponent) for r in others)
            magnitude = w + 2 + rng.randrange(1, 8)
            run = Run(rng.randrange(1, strands), rng.choice((-1, 1))*magnitude)
            runs = others[:index] + [run] + others[index:]
            with self.subTest(case=case, strands=strands, runs=runs):
                self.compare_macro(strands, runs, index)

    def test_seeded_80_independent_cube_comparisons(self):
        rng = Random(0xC0BE2026)
        for case in range(80):
            strands = rng.randrange(2, 5)
            others = [Run(rng.randrange(1, strands), rng.choice((-1, 1)))
                      for _ in range(rng.randrange(3))]
            index = rng.randrange(len(others) + 1)
            magnitude = len(others) + rng.randrange(3, 5)
            run = Run(rng.randrange(1, strands), rng.choice((-1, 1))*magnitude)
            runs = others[:index] + [run] + others[index:]
            answer = tail_homology(strands, runs, run_index=index, check_d2=True)
            independent = cube_homology(strands, expand_word(runs),
                                       max_crossings=8, check_d2=True)
            with self.subTest(case=case, strands=strands, runs=runs):
                self.assertEqual(expand_profile(answer['degree_profile']),
                                 independent['by_degree'])
                self.assertEqual(answer['reduced_rank'], independent['reduced_rank'])

    def test_central_slope_equals_first_inserted_homology(self):
        for sign in (-1, 1):
            for others in ([Run(2, -1)], [Run(1, 1), Run(2, -2)],
                           [Run(1, 2), Run(3, -1), Run(2, -1)]):
                w = sum(abs(r.exponent) for r in others)
                runs = [Run(1, sign*(w+3))] + others
                answer = self.compare_macro(4, runs, 0)
                certificate = answer['tail_certificate']
                degree = certificate['plateau_start']
                self.assertEqual(degree, certificate['plateau_end'])
                self.assertEqual(profile_dimension(answer['degree_profile'], degree),
                                 certificate['plateau_dimension'])

    def test_huge_binary_exponents_and_bounded_reference(self):
        magnitude = (1 << 100_000) + 1
        for sign in (-1, 1):
            answer = tail_homology(2, [Run(1, sign*magnitude)], check_d2=True)
            self.assertEqual(answer['reduced_rank'], magnitude)
            self.assertEqual(answer['reference']['stats']['basis'], 4)
            self.assertEqual(answer['reference']['stats']['macro_states'], 3)
            self.assertEqual(len(answer['degree_profile']['points']), 2)
            self.assertEqual(len(answer['degree_profile']['intervals']), 1)
            self.assertEqual(profile_dimension(answer['degree_profile'], 0), 1)
            self.assertEqual(profile_dimension(answer['degree_profile'], sign*magnitude), 1)
            self.assertEqual(profile_dimension(answer['degree_profile'], sign), 0)
            self.assertEqual(profile_dimension(answer['degree_profile'], sign*(magnitude+1)), 0)
            with self.assertRaises(ResourceLimit):
                expand_profile(answer['degree_profile'], max_terms=1000)

    def test_huge_context_rank_not_just_two_strands(self):
        magnitude = 10**100 + 1
        runs = [Run(1, 3), Run(2, -3), Run(3, magnitude)]
        answer = tail_homology(4, runs, check_d2=True)
        self.assertEqual(answer['reduced_rank'], 9*magnitude)
        self.assertEqual(answer['tail_certificate']['plateau_dimension'], 9)
        self.assertEqual(answer['components'], 1)
        self.assertLess(answer['reference']['stats']['basis'], 1000)

    def test_parity_uses_original_not_shorter_closure(self):
        answer = tail_recognize(2, [Run(1, 101)], check_d2=True)
        self.assertEqual(answer['status'], 'KNOTTED')
        self.assertEqual(answer['homology']['components'], 1)
        self.assertEqual(answer['homology']['reference']['components'], 2)
        with self.assertRaises(ValueError):
            tail_recognize(2, [Run(1, 100)])

    def test_direct_empty_and_nondominating_inputs(self):
        for strands, runs in ((1, []), (4, []),
                              (3, [Run(1, 2), Run(2, -2)])):
            answer = self.compare_macro(strands, runs)
            self.assertEqual(answer['method'], 'direct-macro')
            self.assertIsNone(answer['tail_certificate'])

    def test_resource_failures_remain_unknown(self):
        runs = [Run(1, 101)]
        for budget in (Budget(max_states=2), Budget(max_basis=3),
                       Budget(max_matrix_bits=0), Budget(seconds=0)):
            with self.subTest(budget=budget):
                answer = tail_recognize(2, runs, budget=budget, check_d2=True)
                self.assertEqual(answer['status'], 'UNKNOWN')

    def test_budget_and_index_validation(self):
        for index in (-1, 1, True, 0.0):
            with self.subTest(index=index), self.assertRaises(ValueError):
                tail_homology(2, [Run(1, 3)], run_index=index)
        with self.assertRaises(ValueError):
            tail_homology(2, [Run(1, 3)], budget={})
        bad = Budget()
        bad.max_states = -1
        with self.assertRaises(ValueError):
            tail_homology(2, [Run(1, 3)], budget=bad)


if __name__ == '__main__':
    unittest.main(verbosity=2)
