"""Full-source support extraction from nonextreme canonical positive points."""
from copy import deepcopy
from math import gcd
import unittest
from unittest.mock import patch

from fastunknot.integer_codec import json_safe
from fastunknot.normal_crushing import crush_normal_ray
from fastunknot.normal_crushing_verify import verify_normal_crushing
from fastunknot.normal_euler import decide_sector_euler
from fastunknot.normal_sector import SearchLimit
from fastunknot.normal_surface_geometry import NormalOrbitError
from fastunknot.positive_ray import extract_positive_ray
from normal_orbit_research.fixtures import layered_torus, boundary_cap


class PositiveRayExtractionTests(unittest.TestCase):
    def setUp(self):
        source, meridian = layered_torus(1)
        self.source, _ = boundary_cap(source, meridian)
        # Sum of a canonical annulus ray and a canonical disc ray; shared
        # triangle-zero anchors survive, but the input has support nullity 2.
        self.mixture = [[1, 1, 2, 2, 1, 0, 0], [1, 1, 0, 0, 3, 0, 0]]

    def assert_crushable(self, source, original, output):
        rows = output['coordinates']
        for before, after in zip(original, rows):
            for x, y in zip(before, after):
                self.assertGreaterEqual(y, 0)
                if not x:
                    self.assertEqual(y, 0)
        common = 0
        for row in rows:
            for value in row:
                common = gcd(common, value)
        self.assertEqual(common, 1)
        packet = crush_normal_ray(source, rows)['certificate']
        self.assertTrue(verify_normal_crushing(source, packet))

    def test_actual_nonextreme_positive_mixture_descends_on_original_support(self):
        original = deepcopy(self.mixture)
        with self.assertRaisesRegex(ValueError, 'extreme'):
            crush_normal_ray(self.source, self.mixture)
        with patch('fastunknot.normal_sector.sector_rays', side_effect=AssertionError), \
             patch('fastunknot.exact_lp.solve_nonnegative_kernel', side_effect=AssertionError):
            output = extract_positive_ray(self.source, self.mixture)
        self.assertEqual(output['stats']['matching_nullity'], 2)
        self.assertEqual(output['stats']['descent_steps'], 1)
        self.assertEqual(output['stats']['input_euler_characteristic'], 1)
        self.assertLess(output['stats']['output_positive_coordinates'],
                        output['stats']['input_positive_coordinates'])
        self.assert_crushable(self.source, self.mixture, output)
        self.assertEqual(self.mixture, original)

    def test_lp_witnesses_and_huge_multiplicities_give_primitive_crushable_rays(self):
        for n in range(1, 5):
            source, _ = layered_torus(n)
            positive = decide_sector_euler(source, [(t, 2) for t in range(n)])
            self.assertEqual(positive['status'], 'POSITIVE_EULER')
            rows = positive['coordinates']
            output = extract_positive_ray(source, rows)
            self.assert_crushable(source, rows, output)
        huge = [[x*(1 << 20000) for x in row] for row in self.mixture]
        output = extract_positive_ray(self.source, json_safe(huge))
        self.assertEqual(output['coordinates'],
                         extract_positive_ray(self.source, self.mixture)['coordinates'])
        self.assert_crushable(self.source, self.mixture, output)

    def test_noncanonical_nonpositive_inadmissible_and_malformed_inputs_rejected(self):
        # Adding the sum of every vertex link leaves matching valid and Euler
        # positive, but would permit descent into a pure-link component.
        noncanonical = [[x+1 if j < 4 else x for j, x in enumerate(row)]
                        for row in self.mixture]
        with self.assertRaisesRegex(ValueError, 'canonical'):
            extract_positive_ray(self.source, noncanonical)
        for rows in ([[0]*7 for _ in range(2)], [[1]*4+[0]*3 for _ in range(2)],
                     [[0, 0, 1, 1, 1, 0, 0], [0, 0, 0, 0, 2, 0, 0]]):
            with self.assertRaises(ValueError):
                extract_positive_ray(self.source, rows)
        for bad in (True, 1.0, -1, '1'):
            rows = deepcopy(self.mixture)
            rows[0][0] = bad
            with self.assertRaises(ValueError):
                extract_positive_ray(self.source, rows)
        rows = deepcopy(self.mixture)
        rows[0][5] = 1
        with self.assertRaises(ValueError):
            extract_positive_ray(self.source, rows)

    def test_callback_exception_identity_survives_preparation_descent_and_validation(self):
        calls = [0]
        def count():
            calls[0] += 1
        extract_positive_ray(self.source, self.mixture, check=count)
        for error_type in (ValueError, NormalOrbitError, SearchLimit):
            for stop in (1, calls[0]//2, calls[0]):
                current = [0]
                error = error_type('caller cancellation')
                def cancel():
                    current[0] += 1
                    if current[0] == stop:
                        raise error
                with self.assertRaises(error_type) as raised:
                    extract_positive_ray(self.source, self.mixture, check=cancel)
                self.assertIs(raised.exception, error)


if __name__ == '__main__':
    unittest.main()
