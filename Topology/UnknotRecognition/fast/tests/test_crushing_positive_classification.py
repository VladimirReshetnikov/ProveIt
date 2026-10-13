"""Classify repairable positive points without hiding invalid crushing inputs."""
from copy import deepcopy
import unittest
from unittest.mock import patch

from fastunknot import normal_crushing as crushing
from fastunknot.integer_codec import json_safe
from fastunknot.normal_crushing_verify import verify_normal_crushing
from fastunknot.normal_sector import SearchLimit
from fastunknot.normal_surface_geometry import NormalOrbitError
from fastunknot.positive_ray import extract_positive_ray
from normal_orbit_research.fixtures import layered_torus, boundary_cap


class CallerBaseException(BaseException):
    pass


class NormalCrushingClassificationTests(unittest.TestCase):
    def setUp(self):
        self.source, self.ray = layered_torus(1)
        self.capped, _ = boundary_cap(self.source, self.ray)
        self.mixture = [[1, 1, 2, 2, 1, 0, 0], [1, 1, 0, 0, 3, 0, 0]]

    def test_nonprimitive_positive_points_are_classified_before_rank_or_quotient(self):
        for source, rows in ((self.source, self.ray), (self.capped, self.mixture)):
            for scale in (2, 1 << 20000):
                scaled = json_safe([[scale*x for x in row] for row in rows])
                with self.subTest(tetrahedra=len(rows), scale_bits=scale.bit_length()), \
                     patch.object(crushing, '_rref', side_effect=AssertionError('rank entered')), \
                     patch.object(crushing, '_trace_quotient', side_effect=AssertionError('quotient entered')):
                    with self.assertRaises(crushing._NonPrimitiveNormalPoint) as caught:
                        crushing.crush_normal_ray(source, scaled)
                self.assertIsInstance(caught.exception, NormalOrbitError)

    def test_genuine_primitive_nonextreme_point_is_classified_before_quotient(self):
        with patch.object(crushing, '_trace_quotient', side_effect=AssertionError('quotient entered')):
            with self.assertRaises(crushing._NonExtremeNormalPoint) as caught:
                crushing.crush_normal_ray(self.capped, self.mixture)
        self.assertIsInstance(caught.exception, NormalOrbitError)
        repaired = extract_positive_ray(self.capped, self.mixture)
        self.assertEqual(repaired['stats']['descent_steps'], 1)
        result = crushing.crush_normal_ray(self.capped, repaired['coordinates'])
        self.assertTrue(verify_normal_crushing(self.capped, result['certificate']))

    def test_original_validation_failures_are_not_recovery_signals(self):
        points = [[[0]*7], [[1]*4+[0]*3]]
        for bad in (True, 1.0, -1, '1'):
            point = deepcopy(self.ray)
            point[0][0] = bad
            points.append(point)
        incompatible = deepcopy(self.ray)
        incompatible[0][4:7] = [1, 1, 0]
        points.append(incompatible)
        mismatch = deepcopy(self.ray)
        mismatch[0][0] += 1
        points.append(mismatch)
        recovery = (crushing._NonPrimitiveNormalPoint, crushing._NonExtremeNormalPoint)
        for point in points:
            with self.subTest(point=point), self.assertRaises(NormalOrbitError) as caught:
                crushing.crush_normal_ray(self.source, point)
            self.assertNotIsInstance(caught.exception, recovery)
        with self.assertRaises(NormalOrbitError) as caught:
            crushing.crush_normal_ray({'tetrahedra': []}, self.ray)
        self.assertNotIsInstance(caught.exception, recovery)

    def test_noncanonical_points_retain_extraction_rejection(self):
        # This is valid positive matching data with a vertex-link summand.
        point = [[x+1 if j < 4 else x for j, x in enumerate(row)] for row in self.mixture]
        with self.assertRaises(crushing._NonExtremeNormalPoint):
            crushing.crush_normal_ray(self.capped, point)
        with self.assertRaisesRegex(NormalOrbitError, 'canonical'):
            extract_positive_ray(self.capped, point)

    def test_impossible_full_support_rank_is_an_internal_error(self):
        def impossible_rank(equations, width, check):
            check()
            return [], tuple(range(width))
        with patch.object(crushing, '_rref', side_effect=impossible_rank), \
             patch.object(crushing, '_trace_quotient', side_effect=AssertionError('quotient entered')):
            with self.assertRaisesRegex(ArithmeticError, 'impossible support rank'):
                crushing.crush_normal_ray(self.source, self.ray)

    def test_existing_extreme_ray_uses_original_validation_and_replays(self):
        with patch('fastunknot.positive_ray.extract_positive_ray', side_effect=AssertionError('extraction entered')):
            result = crushing.crush_normal_ray(self.source, self.ray)
        self.assertEqual(result['certificate']['coordinates'], self.ray)
        self.assertTrue(verify_normal_crushing(self.source, result['certificate']))

    def test_callback_identity_including_recovery_classes_survives(self):
        calls = [0]
        def count():
            calls[0] += 1
        crushing.crush_normal_ray(self.source, self.ray, check=count)
        for kind in (ValueError, NormalOrbitError, SearchLimit, ArithmeticError,
                     crushing._NonPrimitiveNormalPoint, crushing._NonExtremeNormalPoint,
                     KeyboardInterrupt, SystemExit, CallerBaseException):
            for stop in (1, max(1, calls[0]//2), calls[0]):
                error = kind('caller interruption')
                current = [0]
                def cancel():
                    current[0] += 1
                    if current[0] == stop:
                        raise error
                with self.subTest(kind=kind, stop=stop), self.assertRaises(kind) as caught:
                    crushing.crush_normal_ray(self.source, self.ray, check=cancel)
                self.assertIs(caught.exception, error)


if __name__ == '__main__':
    unittest.main()
