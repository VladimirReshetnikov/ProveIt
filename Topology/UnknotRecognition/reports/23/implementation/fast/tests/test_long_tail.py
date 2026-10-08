"""Finite-cap correctness, threshold, interface, and resource regressions."""
import copy
import random
import unittest

from fastunknot.twist.core import (
    Budget, ResourceLimit, Run, build_complex, homology,
)
from fastunknot.twist.reference import cube_homology
from fastunknot.twist.long_tail import (
    degree_dimension, dominant_run_obstruction, materialize_profile,
    profile_rank, tail_homology, tail_recognize,
    verify_dominant_run_certificate,
)


def _word(runs):
    return [run.generator * (1 if run.exponent > 0 else -1)
            for run in runs for _ in range(abs(run.exponent))]


class FiniteCapTests(unittest.TestCase):
    def test_complete_profiles_random_contexts(self):
        """240 full-degree comparisons, including cap-1 and both endpoints."""
        rng = random.Random(1082026)
        comparisons = 0
        for _ in range(60):
            b = rng.randrange(2, 6)
            t = rng.randrange(1, 6)
            selected = rng.randrange(t)
            runs = [Run(rng.randrange(1, b), rng.choice((-2, -1, 1, 2)))
                    for _ in range(t)]
            sign = rng.choice((-1, 1))
            length = sum(abs(r.exponent) for j, r in enumerate(runs) if j != selected)
            for magnitude in (length + 1, length + 2, length + 3, length + 6):
                runs[selected] = Run(runs[selected].generator, sign * magnitude)
                exact = homology(b, runs, check_d2=True)
                capped = tail_homology(b, runs, selected=selected, check_d2=True)
                self.assertEqual(materialize_profile(capped['compact_by_degree']),
                                 exact['by_degree'])
                self.assertEqual(capped['reduced_rank'], exact['reduced_rank'])
                self.assertEqual(capped['components'], exact['components'])
                for h in range(-sum(abs(r.exponent) for r in runs) - 1,
                               sum(abs(r.exponent) for r in runs) + 2):
                    self.assertEqual(degree_dimension(capped['compact_by_degree'], h),
                                     exact['by_degree'].get(h, 0))
                comparisons += 1
        self.assertEqual(comparisons, 240)

    def test_single_full_slice_rank_threshold(self):
        """The total-rank affine law starts one step before the profile cap."""
        rng = random.Random(11082026)
        for _ in range(80):
            b = rng.randrange(2, 6)
            t = rng.randrange(1, 6)
            selected = rng.randrange(t)
            runs = [Run(rng.randrange(1, b), rng.choice((-2, -1, 1, 2)))
                    for _ in range(t)]
            sign = rng.choice((-1, 1))
            length = sum(abs(r.exponent) for j, r in enumerate(runs) if j != selected)
            runs[selected] = Run(runs[selected].generator, sign * (length + 2))
            cap = tail_homology(b, runs, selected=selected, check_d2=True)
            runs[selected] = Run(runs[selected].generator, sign * (length + 1))
            one = homology(b, runs, check_d2=True)
            self.assertEqual(cap['reduced_rank'], one['reduced_rank'] +
                             cap['calibration']['interior_betti'])

    def test_exact_interior_matrix_identification(self):
        rng = random.Random(12082026)
        for _ in range(32):
            b = rng.randrange(2, 6)
            t = rng.randrange(1, 6)
            selected = rng.randrange(t)
            runs = [Run(rng.randrange(1, b), rng.choice((-2, -1, 1, 2)))
                    for _ in range(t)]
            sign = rng.choice((-1, 1))
            length = sum(abs(r.exponent) for j, r in enumerate(runs) if j != selected)
            beta = sum(max(0, sign * r.exponent)
                       for j, r in enumerate(runs) if j != selected)
            runs[selected] = Run(runs[selected].generator, sign * (length + 2))
            cap = build_complex(b, runs)
            source = beta + 1 if sign > 0 else -(beta + 2)
            runs[selected] = Run(runs[selected].generator, sign * (length + 3))
            extended = build_complex(b, runs)
            self.assertEqual(cap.columns[source], extended.columns[source])
            self.assertEqual(cap.columns[source], extended.columns[source + sign])

    def test_independent_crossing_cube(self):
        rng = random.Random(13082026)
        for _ in range(24):
            b = rng.randrange(2, 5)
            t = rng.randrange(1, 5)
            selected = rng.randrange(t)
            runs = [Run(rng.randrange(1, b), rng.choice((-1, 1))) for _ in range(t)]
            length = t - 1
            sign = rng.choice((-1, 1))
            runs[selected] = Run(runs[selected].generator, sign * (length + 3))
            capped = tail_homology(b, runs, selected=selected, check_d2=True)
            cube = cube_homology(b, _word(runs), max_crossings=9, check_d2=True)
            self.assertEqual(materialize_profile(capped['compact_by_degree']),
                             cube['by_degree'])

    def test_huge_signed_input_no_materialization(self):
        magnitude = (1 << 20000) + 1
        for sign in (-1, 1):
            result = tail_homology(2, [Run(1, sign * magnitude)], check_d2=True)
            self.assertEqual(result['reduced_rank'], magnitude)
            self.assertEqual(result['stats']['built_crossings'], 2)
            self.assertEqual(result['stats']['basis'], 4)
            profile = result['compact_by_degree']
            self.assertEqual(degree_dimension(profile, 0), 1)
            self.assertEqual(degree_dimension(profile, sign), 0)
            self.assertEqual(degree_dimension(profile, sign * 2), 1)
            self.assertEqual(degree_dimension(profile, sign * magnitude), 1)
            self.assertEqual(degree_dimension(profile, sign * (magnitude + 1)), 0)
            with self.assertRaises(ResourceLimit):
                materialize_profile(profile, max_degrees=100)

    def test_automatic_selection_and_short_fallback(self):
        runs = [Run(1, 1), Run(2, -11), Run(3, 1)]
        result = tail_homology(4, runs)
        self.assertEqual(result['calibration']['selected_run'], 1)
        self.assertTrue(result['tail_compressed'])
        short = tail_homology(4, runs, selected=0)
        self.assertFalse(short['tail_eligible'])
        self.assertEqual(short['reduced_rank'], result['reduced_rank'])
        self.assertEqual(materialize_profile(short['compact_by_degree']),
                         materialize_profile(result['compact_by_degree']))

    def test_empty_unknot(self):
        result = tail_homology(1, [])
        self.assertEqual(result['reduced_rank'], 1)
        self.assertEqual(materialize_profile(result['compact_by_degree']), {0: 1})

    def test_original_components_not_cap_components(self):
        result = tail_homology(2, [Run(1, 101)])
        self.assertEqual(result['components'], 1)
        self.assertEqual(result['calibration']['cap_magnitude'], 2)
        self.assertEqual(tail_recognize(2, [Run(1, 101)])['status'], 'KNOTTED')
        with self.assertRaises(ValueError):
            tail_recognize(2, [Run(1, 100)])

    def test_budgets_and_invalid_parameters(self):
        with self.assertRaises(ResourceLimit):
            tail_homology(2, [Run(1, 101)], budget=Budget(max_basis=0))
        with self.assertRaises(ResourceLimit):
            tail_homology(2, [Run(1, 101)], budget=Budget(seconds=0))
        self.assertEqual(tail_recognize(2, [Run(1, 101)],
                                      budget=Budget(max_states=0))['status'], 'UNKNOWN')
        for selected in (-1, 1, False, 0.0, '0'):
            with self.assertRaises(ValueError):
                tail_homology(2, [Run(1, 3)], selected=selected)
        with self.assertRaises(ValueError):
            materialize_profile({'points': [], 'constant_intervals': []}, max_degrees=-1)
        with self.assertRaises(ValueError):
            degree_dimension({'points': [], 'constant_intervals': []}, True)


class DominanceTests(unittest.TestCase):
    def test_sharp_unknot_threshold(self):
        for length in (1, 2, 3, 5):
            for sign in (-1, 1):
                runs = [Run(1, sign * (length + 1)), Run(1, -sign * length)]
                self.assertIsNone(dominant_run_obstruction(2, runs, selected=0))
                self.assertEqual(homology(2, runs)['reduced_rank'], 1)

    def test_knot_certificates_and_rank_lower_bounds(self):
        rng = random.Random(14082026)
        certified = 0
        for _ in range(120):
            b = rng.randrange(2, 6)
            t = rng.randrange(1, 6)
            selected = rng.randrange(t)
            runs = [Run(rng.randrange(1, b), rng.choice((-2, -1, 1, 2)))
                    for _ in range(t)]
            length = sum(abs(r.exponent) for j, r in enumerate(runs) if j != selected)
            runs[selected] = Run(runs[selected].generator,
                                 rng.choice((-1, 1)) * (length + rng.randrange(2, 7)))
            result = tail_homology(b, runs, selected=selected)
            witness = dominant_run_obstruction(b, runs, selected=selected)
            if result['components'] != 1:
                self.assertIsNone(witness)
                continue
            certified += 1
            self.assertIsNotNone(witness)
            cert = witness['certificate']
            self.assertEqual(witness['status'], 'KNOTTED')
            self.assertTrue(verify_dominant_run_certificate(b, runs, cert))
            self.assertGreaterEqual(result['reduced_rank'], cert['reduced_F2_rank_lower_bound'])
            self.assertGreaterEqual(cert['reduced_F2_rank_lower_bound'], 3)
            self.assertEqual(result['calibration']['interior_betti'] % 2, 1)
        self.assertGreater(certified, 10)

    def test_replay_rejects_tampering_and_boolean_integers(self):
        runs = [Run(1, 11)]
        certificate = dominant_run_obstruction(2, runs)['certificate']
        for key in certificate:
            altered = copy.deepcopy(certificate)
            value = altered[key]
            if type(value) is int:
                altered[key] += 1
            elif type(value) is bool:
                altered[key] = False
            else:
                altered[key] = 'invalid'
            with self.assertRaises(ValueError):
                verify_dominant_run_certificate(2, runs, altered)
        altered = dict(certificate, generator=True)
        with self.assertRaises(ValueError):
            verify_dominant_run_certificate(2, runs, altered)


if __name__ == '__main__':
    unittest.main(verbosity=2)
