"""Adversarial schema, completeness, geometry and interruption replay tests."""

from copy import deepcopy
from pathlib import Path
import sys
import unittest
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from fastunknot.sector_planar import certify_planar_sector, sector_planar_rays
from fastunknot.sector_planar_verify import verify_planar_sector_certificate
from fastunknot.sector_sparse import PreparedSectorSource
from normal_orbit_research.fixtures import boundary_cap, layered_torus


class FalseCallback:
    def __init__(self, stop=None, exception=ValueError):
        self.calls = 0
        self.stop = stop
        self.exception = exception

    def __bool__(self):
        return False

    def __call__(self):
        self.calls += 1
        if self.calls == self.stop:
            raise self.exception('adversarial cooperative interruption')


class PlanarAdversarialTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.point_raw, vector = layered_torus(1)
        cls.point = certify_planar_sector(cls.point_raw, [(0, 2)])['certificate']
        cls.empty = certify_planar_sector(cls.point_raw, [])['certificate']
        cls.line_raw, vector = boundary_cap(cls.point_raw, vector)
        cls.line = certify_planar_sector(cls.line_raw, [(0, 0), (1, 0)])['certificate']
        cls.plane_raw, vector = boundary_cap(cls.line_raw, vector)
        cls.plane = certify_planar_sector(cls.plane_raw, [(0, 0), (1, 0), (2, 0)])[
            'certificate']

    def test_valid_strata_and_independence_from_producer(self):
        cases = [(self.point_raw, self.empty), (self.point_raw, self.point),
                 (self.line_raw, self.line), (self.plane_raw, self.plane)]
        self.assertEqual([proof['section_dimension'] for _, proof in cases], [-1, 0, 1, 2])
        with patch('fastunknot.sector_planar._clip_polygon', side_effect=AssertionError), \
             patch('fastunknot.sector_planar.sector_planar_plan', side_effect=AssertionError), \
             patch('fastunknot.sector_sparse.PreparedSectorSource', side_effect=AssertionError), \
             patch('fastunknot.normal_sector._nullspace', side_effect=AssertionError):
            for raw, proof in cases:
                self.assertTrue(verify_planar_sector_certificate(raw, proof))

    def test_wrong_source_dimensions_and_boolean_integer_fields(self):
        mutations = [('source_sha256', '0'*64), ('matching_dimension', True),
                     ('section_dimension', False), ('allowed_types', [(0, True)])]
        for field, value in mutations:
            proof = deepcopy(self.point)
            proof[field] = value
            with self.subTest(field=field):
                self.assertFalse(verify_planar_sector_certificate(self.point_raw, proof))
        proof = deepcopy(self.point)
        proof['chart']['forms'][0][0][0] = True
        self.assertFalse(verify_planar_sector_certificate(self.point_raw, proof))
        proof = deepcopy(self.line)
        proof['chart']['coordinates'][0] = True
        self.assertFalse(verify_planar_sector_certificate(self.line_raw, proof))
        proof = deepcopy(self.point)
        proof['rays'][0][0][0] = True
        self.assertFalse(verify_planar_sector_certificate(self.point_raw, proof))

    def test_point_group_inventory_requires_an_actual_list(self):
        for value in (False, None, {}, (), '', 0):
            proof = deepcopy(self.point)
            proof['groups'] = value
            with self.subTest(value=value):
                self.assertFalse(verify_planar_sector_certificate(self.point_raw, proof))

    def test_incomplete_or_duplicated_ray_sets_are_rejected(self):
        for alteration in ('missing', 'duplicate', 'reversed'):
            proof = deepcopy(self.plane)
            if alteration == 'missing':
                proof['rays'].pop()
            elif alteration == 'duplicate':
                proof['rays'].append(deepcopy(proof['rays'][0]))
            else:
                proof['rays'].reverse()
            with self.subTest(alteration=alteration):
                self.assertFalse(verify_planar_sector_certificate(self.plane_raw, proof))

    def test_group_cell_coverage_and_distinct_label_checks(self):
        self.assertGreater(len(self.plane['groups'][0]['cells']), 1)
        for alteration in ('no_group', 'no_cell', 'duplicate_cell', 'reverse_cell',
                           'boolean_vertex', 'boolean_corner', 'nonminimizer'):
            proof = deepcopy(self.plane)
            group = proof['groups'][0]
            if alteration == 'no_group':
                proof['groups'].pop()
            elif alteration == 'no_cell':
                group['cells'].pop()
            elif alteration == 'duplicate_cell':
                group['cells'].append(deepcopy(group['cells'][0]))
            elif alteration == 'reverse_cell':
                group['cells'][0]['vertices'].reverse()
            elif alteration == 'boolean_vertex':
                group['vertex'] = False
            elif alteration == 'boolean_corner':
                group['cells'][0]['corner'] = False
            else:
                group['cells'][0]['corner'] = group['cells'][1]['corner']
            with self.subTest(alteration=alteration):
                self.assertFalse(verify_planar_sector_certificate(self.plane_raw, proof))

    def test_chart_and_section_coverage_cannot_be_shrunk(self):
        for alteration in ('chart_normalization', 'coordinate_claim', 'polygon_missing',
                           'point_in_place_of_polygon', 'noncanonical_fraction'):
            proof = deepcopy(self.plane)
            if alteration == 'chart_normalization':
                proof['chart']['forms'][0][0] = [7, 1]
            elif alteration == 'coordinate_claim':
                proof['chart']['coordinates'].reverse()
            elif alteration == 'polygon_missing':
                proof['polygon'].pop()
            elif alteration == 'point_in_place_of_polygon':
                proof['polygon'] = proof['polygon'][:1]
                proof['section_dimension'] = 0
                proof['groups'] = []
            else:
                proof['chart']['forms'][0][0] = [2, 2]
            with self.subTest(alteration=alteration):
                self.assertFalse(verify_planar_sector_certificate(self.plane_raw, proof))

    def test_native_hex_integer_transport_is_accepted(self):
        proof = deepcopy(self.plane)
        def fractions(value):
            return [[hex(numerator), hex(denominator)] for numerator, denominator in value]
        proof['chart']['forms'] = [fractions(form) for form in proof['chart']['forms']]
        proof['polygon'] = [fractions(point) for point in proof['polygon']]
        for group in proof['groups']:
            for cell in group['cells']:
                cell['vertices'] = [fractions(point) for point in cell['vertices']]
        proof['rays'] = [[[hex(value) for value in row] for row in ray]
                         for ray in proof['rays']]
        self.assertTrue(verify_planar_sector_certificate(self.plane_raw, proof))

    def test_callback_exceptions_propagate_from_all_replay_stages(self):
        count = FalseCallback()
        self.assertTrue(verify_planar_sector_certificate(self.plane_raw, self.plane,
                                                       check=count))
        for exception in (ValueError, TypeError, KeyError, RuntimeError):
            for stop in (1, 3, count.calls//2, count.calls-1):
                with self.subTest(exception=exception.__name__, stop=stop):
                    callback = FalseCallback(stop, exception)
                    with self.assertRaisesRegex(exception, 'adversarial cooperative interruption'):
                        verify_planar_sector_certificate(self.plane_raw, self.plane,
                                                         check=callback)

    def test_producer_caps_and_source_binding(self):
        source = PreparedSectorSource(self.plane_raw)
        with self.assertRaises(ValueError):
            certify_planar_sector(self.point_raw, [(0, 2)], source=source)
        limited = certify_planar_sector(self.plane_raw, [(0, 0), (1, 0), (2, 0)],
                                        source=source, max_rays=0)
        self.assertEqual(limited['status'], 'INCONCLUSIVE')
        self.assertNotIn('certificate', limited)
        with self.assertRaises(ValueError):
            certify_planar_sector(self.point_raw, [(0, 2)], max_rays=True)
        for run in (lambda callback: certify_planar_sector(
                        self.point_raw, [(0, 2)], check=callback),
                    lambda callback: list(sector_planar_rays(
                        source.build([(0, 0), (1, 0), (2, 0)]), check=callback))):
            with self.assertRaisesRegex(ValueError, 'adversarial cooperative interruption'):
                run(FalseCallback(3))


if __name__ == '__main__':
    unittest.main()
