"""Component-local Euler/homology weights and canonical essential-disc counts."""
from copy import deepcopy
import importlib.util
from itertools import product
import json
from math import gcd
from pathlib import Path
import random
import unittest
from unittest.mock import patch

from fastunknot.integer_codec import json_safe
from fastunknot.normal_surface_geometry import _prepare, _coordinates, NormalOrbitError
from fastunknot.normal_component_geometry import boundary_homology_basis, valid_boundary_basis
from fastunknot.normal_surface_components import normal_component_census
from fastunknot.normal_component_verify import verify_normal_component_certificate
from fastunknot.normal_disk_kernel import (
    canonical_disk_core, normal_compressing_disk_count, verify_normal_disk_count_certificate,
)
from fastunknot.normal_surface_orbits import normal_surface_topology
from fastunknot.normal_surface_verify import verify_normal_surface_certificate
from normal_orbit_research.fixtures import (
    layered_torus, interior_vertex_torus, boundary_cap, export_surface,
    regina_triangulation, regina_surface,
)


ROOT = Path(__file__).resolve().parents[1]


def combination(basis, coefficients):
    return [[sum(coefficient * vector[t][j] for coefficient, vector in zip(coefficients, basis))
             for j in range(7)] for t in range(len(basis[0]))]


def projected_histogram(answer):
    result = {}
    for record in answer['component_histogram']:
        key = record['euler_characteristic'], tuple(record['boundary_homology_mod2'])
        result[key] = result.get(key, 0) + record['multiplicity']
    return result


def relabel(raw, coordinates, rng):
    size = len(coordinates)
    order = list(range(size))
    rng.shuffle(order)
    maps = [rng.sample(range(4), 4) for _ in range(size)]
    faces = [[None] * 4 for _ in range(size)]
    result = [[0] * 7 for _ in range(size)]
    for t, row in enumerate(raw['tetrahedra']):
        mapping = maps[t]
        for f, record in enumerate(row):
            if record is not None:
                u, permutation = record['tetrahedron'], record['permutation']
                transformed = [0] * 4
                for v in range(4):
                    transformed[mapping[v]] = maps[u][permutation[v]]
                faces[order[t]][mapping[f]] = dict(tetrahedron=order[u],
                                                  permutation=transformed)
        for v in range(4):
            result[order[t]][mapping[v]] = coordinates[t][v]
        for q in range(3):
            pair = {mapping[0], mapping[q + 1]}
            if 0 not in pair:
                pair = set(range(4)) - pair
            target = next(v for v in pair if v) - 1
            result[order[t]][4 + target] = coordinates[t][4 + q]
    return dict(tetrahedra=faces), result


class NormalComponentTests(unittest.TestCase):
    def test_three_modes_match_and_extract_actual_meridians(self):
        for tetrahedra in (1, 2, 4, 8, 16):
            raw, meridian = layered_torus(tetrahedra)
            results = []
            for mode, dimension in (('disk', 3), ('summary', 5),
                                     ('coordinates', 7 * tetrahedra)):
                answer = normal_component_census(raw, meridian, mode=mode,
                                                 record_certificate=True)
                self.assertEqual(answer['weight_dimension'], dimension)
                self.assertEqual(answer['compressing_disk_components'], 1)
                self.assertEqual(answer['components'], 1)
                self.assertTrue(verify_normal_component_certificate(raw, meridian,
                                                                     answer['certificate']))
                results.append(answer)
            self.assertEqual(projected_histogram(results[0]), projected_histogram(results[1]))
            self.assertEqual(projected_histogram(results[0]), projected_histogram(results[2]))
            self.assertEqual(results[2]['component_histogram'][0]['coordinates'], meridian)

    def test_total_boundary_parity_cancels_for_two_essential_discs(self):
        raw, meridian = layered_torus(3)
        vector = [[2 * value for value in row] for row in meridian]
        old = normal_surface_topology(raw, vector, record_certificate=True)
        self.assertFalse(old['certificate']['boundary_homology']['nonzero'])
        self.assertFalse(old['compressing_disk'])
        answer = normal_component_census(raw, vector, record_certificate=True)
        self.assertEqual(answer['components'], 2)
        self.assertEqual(answer['compressing_disk_components'], 2)
        self.assertTrue(answer['contains_compressing_disk'])
        self.assertEqual(len(answer['component_histogram']), 1)
        self.assertTrue(any(answer['component_histogram'][0]['boundary_homology_mod2']))
        self.assertTrue(verify_normal_component_certificate(raw, vector, answer['certificate']))

    def test_total_chi_and_total_homology_can_suggest_a_nonexistent_disc(self):
        raw, _ = layered_torus(1)
        vector = [[1, 1, 1, 1, 0, 1, 0]]  # Inessential vertex disc plus Mobius band.
        old = normal_surface_topology(raw, vector, record_certificate=True)
        self.assertEqual(old['euler_characteristic'], 1)
        self.assertTrue(old['certificate']['boundary_homology']['nonzero'])
        for mode in ('disk', 'summary', 'coordinates'):
            answer = normal_component_census(raw, vector, mode=mode, record_certificate=True)
            self.assertEqual(answer['components'], 2)
            self.assertEqual(answer['compressing_disk_components'], 0)
            self.assertEqual(sorted(row['euler_characteristic']
                                    for row in answer['component_histogram']), [0, 1])
            for row in answer['component_histogram']:
                if row['euler_characteristic'] == 1:
                    self.assertEqual(row['boundary_homology_mod2'], [0, 0])
            self.assertTrue(verify_normal_component_certificate(raw, vector,
                                                                 answer['certificate']))

    def test_sphere_vertex_disc_and_mobius_mixtures(self):
        raw, basis = interior_vertex_torus()
        for a, b, c in product(range(3), repeat=3):
            vector = combination(list(basis.values()), (a, b, c))
            answer = normal_component_census(raw, vector, mode='summary',
                                             record_certificate=True)
            self.assertEqual(answer['components'], a + b + (c + 1) // 2)
            self.assertEqual(answer['compressing_disk_components'], 0)
            self.assertEqual(sum(row['normal_disks'] * row['multiplicity']
                                 for row in answer['component_histogram']), sum(map(sum, vector)))
            self.assertTrue(verify_normal_component_certificate(raw, vector,
                                                                 answer['certificate']))

    def test_closed_projective_plane_with_chi_one_is_not_a_disc(self):
        fixture = json.loads((ROOT / 'normal_orbit_research/data/projective_plane_torus.json').read_text())
        raw, plane = fixture['triangulation'], fixture['coordinates']
        for multiplier in (1, 2, 3):
            vector = [[multiplier * value for value in row] for row in plane]
            answer = normal_component_census(raw, vector, mode='summary',
                                             record_certificate=True)
            self.assertEqual(answer['compressing_disk_components'], 0)
            self.assertTrue(all(row['boundary_points'] == 0
                                and row['boundary_homology_mod2'] == [0, 0]
                                for row in answer['component_histogram']))
            self.assertTrue(verify_normal_component_certificate(raw, vector,
                                                                 answer['certificate']))

    def test_boundary_basis_generalized_loops_and_relabeling(self):
        rng = random.Random(2610092017)
        raw, meridian = layered_torus(5)
        cases = [(raw, meridian), boundary_cap(raw, meridian)]
        for source, vector in cases:
            for _ in range(8):
                changed, coords = relabel(source, vector, rng)
                prepared = _prepare(changed, lambda: None)
                basis = boundary_homology_basis(prepared)
                self.assertTrue(valid_boundary_basis(prepared, basis))
                self.assertFalse(valid_boundary_basis(prepared, [basis[0], basis[0]]))
                self.assertFalse(valid_boundary_basis(prepared, [[], basis[1]]))
                self.assertFalse(valid_boundary_basis(prepared, [basis[0] * 2, basis[1]]))
                self.assertFalse(valid_boundary_basis(prepared, [[True], basis[1]]))
                answer = normal_component_census(changed, coords, record_certificate=True)
                self.assertEqual(answer['compressing_disk_components'], 1)
                self.assertTrue(verify_normal_component_certificate(changed, coords,
                                                                     answer['certificate']))

    def test_foreign_source_basis_histogram_and_schema_mutations(self):
        raw, meridian = layered_torus(4)
        proof = normal_component_census(raw, meridian, record_certificate=True)['certificate']
        bad = deepcopy(proof)
        bad['boundary_homology_basis'][1] = bad['boundary_homology_basis'][0]
        self.assertFalse(verify_normal_component_certificate(raw, meridian, bad))
        for field, value in (('components', True), ('components', 2),
                             ('compressing_disk_components', 0),
                             ('contains_compressing_disk', 1)):
            bad = deepcopy(proof)
            bad['summary'][field] = value
            self.assertFalse(verify_normal_component_certificate(raw, meridian, bad))
        for mode in ('summary', 'coordinates', 'unknown'):
            bad = deepcopy(proof)
            bad['mode'] = mode
            self.assertFalse(verify_normal_component_certificate(raw, meridian, bad))
        for field in ('boundary_homology_basis', 'weighted_orbits', 'input_sha256', 'summary'):
            bad = deepcopy(proof)
            del bad[field]
            self.assertFalse(verify_normal_component_certificate(raw, meridian, bad))
        other = [[2 * value for value in row] for row in meridian]
        self.assertFalse(verify_normal_component_certificate(raw, other, proof))

    def test_malformed_sources_never_yield_verified_components(self):
        raw, meridian = layered_torus(1)
        proof = normal_component_census(raw, meridian, record_certificate=True)['certificate']
        for bad in ([[1, 1, 0, 0, 0, 0, True]], [[1, 1, 0, 0, 0, 0, 1.0]],
                    [[1, 1, 0, 0, 0, 0, -1]], [[2, 1, 0, 0, 0, 0, 1]],
                    [[1, 1, 0, 0, 1, 0, 1]], [[1] * 6]):
            with self.assertRaises(NormalOrbitError):
                normal_component_census(raw, bad)
            self.assertFalse(verify_normal_component_certificate(raw, bad, proof))
        for broken in ({}, {'tetrahedra': [[None] * 4]}):
            self.assertFalse(verify_normal_component_certificate(broken, meridian, proof))

    def test_cycle_exhaustion_and_reuse_of_source_bound_orbit_proof(self):
        raw, meridian = layered_torus(6)
        full = normal_component_census(raw, meridian, record_certificate=True)
        cycles = full['stats']['orbit_cycles']
        for cap in (0, cycles - 1):
            partial = normal_component_census(raw, meridian, max_cycles=cap,
                                               record_certificate=True)
            self.assertEqual(partial['status'], 'INCONCLUSIVE')
            for field in ('components', 'compressing_disk_components',
                          'contains_compressing_disk', 'certificate'):
                self.assertNotIn(field, partial)
        self.assertEqual(normal_component_census(raw, meridian, max_cycles=cycles,
                                                 record_certificate=True), full)
        orbit = full['certificate']['weighted_orbits']['orbit_proof']
        with patch('fastunknot.weighted_orbits.count_orbits', side_effect=AssertionError):
            reused = normal_component_census(raw, meridian, mode='summary',
                                              orbit_certificate=orbit, record_certificate=True)
        self.assertEqual(reused['compressing_disk_components'], 1)
        self.assertTrue(verify_normal_component_certificate(raw, meridian, reused['certificate']))
        with self.assertRaises(ValueError):
            normal_component_census(raw, meridian, orbit_certificate=orbit, max_cycles=0)

    def test_replay_independence_cancellation_and_old_apis(self):
        raw, meridian = layered_torus(6)
        old = normal_surface_topology(raw, meridian, record_certificate=True)
        answer = normal_component_census(raw, meridian, record_certificate=True)
        proof = answer['certificate']
        with patch('fastunknot.normal_component_geometry.boundary_homology_basis',
                   side_effect=AssertionError), \
             patch('fastunknot.normal_surface_components._component_summary',
                   side_effect=AssertionError), \
             patch('fastunknot.weighted_orbits._replay', side_effect=AssertionError), \
             patch('fastunknot.weighted_orbits.count_orbits', side_effect=AssertionError):
            self.assertTrue(verify_normal_component_certificate(raw, meridian, proof))
        self.assertEqual(normal_surface_topology(raw, meridian, record_certificate=True), old)
        self.assertTrue(verify_normal_surface_certificate(raw, meridian, old['certificate']))

        class Cancelled(Exception):
            pass

        for threshold in (1, 150, 600):
            for operation in (lambda check: normal_component_census(raw, meridian, check=check),
                              lambda check: verify_normal_component_certificate(
                                  raw, meridian, proof, check=check)):
                calls = 0

                def check():
                    nonlocal calls
                    calls += 1
                    if calls == threshold:
                        raise Cancelled()

                with self.assertRaises(Cancelled):
                    operation(check)

    def test_large_binary_component_multiplicity_is_not_expanded(self):
        raw, meridian = layered_torus(2)
        count = 2 ** 5000 + 1
        vector = [[count * value for value in row] for row in meridian]
        answer = normal_component_census(raw, vector, record_certificate=True)
        self.assertEqual(answer['compressing_disk_components'], count)
        self.assertEqual(len(answer['component_histogram']), 1)
        transported = json.loads(json.dumps(json_safe(answer['certificate'])))
        self.assertTrue(verify_normal_component_certificate(raw, vector, transported))

    def test_vertex_link_and_quad_content_kernel_with_input_gcd_one(self):
        raw, meridian = layered_torus(5)
        factor, links = 2 ** 5000, 2 ** 5000 + 1
        vector = [[factor * value + (links if j < 4 else 0)
                   for j, value in enumerate(row)] for row in meridian]
        self.assertEqual(gcd(*(value for row in vector for value in row)), 1)
        baseline = normal_compressing_disk_count(raw, meridian, record_certificate=True)
        answer = normal_compressing_disk_count(raw, vector, record_certificate=True)
        self.assertEqual(answer['compressing_disk_components'], factor)
        self.assertEqual(answer['coordinate_divisor'], factor)
        self.assertEqual(answer['stats'], baseline['stats'])
        self.assertLess(answer['core_coordinate_bits'], 10)
        self.assertNotIn('components', answer)
        encoded = json.loads(json.dumps(json_safe(answer['certificate'])))
        self.assertTrue(verify_normal_disk_count_certificate(raw, vector, encoded))

    def test_triangle_only_kernel_needs_no_orbit_query(self):
        raw, basis = interior_vertex_torus()
        vector = combination([basis['sphere'], basis['boundary_disk']], (2 ** 1000, 2 ** 1000 + 1))
        with patch('fastunknot.normal_disk_kernel.normal_component_census',
                   side_effect=AssertionError):
            answer = normal_compressing_disk_count(raw, vector, max_cycles=0,
                                                   record_certificate=True)
        self.assertEqual(answer['compressing_disk_components'], 0)
        self.assertEqual(answer['coordinate_divisor'], 0)
        self.assertEqual(answer['stats']['orbit_cycles'], 0)
        self.assertIsNone(answer['certificate']['core_certificate'])
        self.assertTrue(verify_normal_disk_count_certificate(raw, vector, answer['certificate']))

    def test_one_sided_scaling_never_creates_disc_components(self):
        raw, _ = layered_torus(1)
        for factor in (1, 2, 3, 8, 2 ** 5000 + 1):
            vector = [[factor + 1] * 4 + [0, factor, 0]]
            answer = normal_compressing_disk_count(raw, vector, record_certificate=True)
            self.assertEqual(answer['compressing_disk_components'], 0)
            self.assertTrue(verify_normal_disk_count_certificate(raw, vector,
                                                                  answer['certificate']))

    def test_kernel_coefficient_bound_and_independent_replay(self):
        raw, meridian = boundary_cap(*layered_torus(4))
        prepared = _prepare(raw, lambda: None)
        roots = sorted(set(prepared['vertex_roots']))
        shifts = {root: 12345 * (index + 1) for index, root in enumerate(roots)}
        factor = 143
        vector = [[factor * value + (shifts[prepared['vertex_roots'][4*t+j]] if j < 4 else 0)
                   for j, value in enumerate(row)] for t, row in enumerate(meridian)]
        analysed = _coordinates(prepared, vector, lambda: None)
        divisor, core, _ = canonical_disk_core(prepared, analysed)
        self.assertEqual(divisor, factor)
        largest_quad = max(value for row in core for value in row[4:])
        for t, row in enumerate(core):
            for v in range(4):
                corners = prepared['vertex_roots'].count(prepared['vertex_roots'][4*t+v])
                self.assertLessEqual(row[v], (corners - 1) * largest_quad)
        proof = normal_compressing_disk_count(raw, vector, record_certificate=True)['certificate']
        with patch('fastunknot.normal_disk_kernel.canonical_disk_core', side_effect=AssertionError), \
             patch('fastunknot.normal_disk_kernel.normal_component_census', side_effect=AssertionError):
            self.assertTrue(verify_normal_disk_count_certificate(raw, vector, proof))
        for field in ('coordinate_divisor', 'compressing_disk_components'):
            for bad_value in (True, 1.0, proof[field] + 1):
                bad = deepcopy(proof)
                bad[field] = bad_value
                self.assertFalse(verify_normal_disk_count_certificate(raw, vector, bad))
        bad = deepcopy(proof)
        bad['core_coordinates'][0][0] += 1
        self.assertFalse(verify_normal_disk_count_certificate(raw, vector, bad))
        bad = deepcopy(proof)
        bad['vertex_links'][0]['multiplicity'] += 1
        self.assertFalse(verify_normal_disk_count_certificate(raw, vector, bad))

    def test_empty_component_census_and_invalid_options(self):
        raw, meridian = layered_torus(2)
        empty = [[0] * 7 for _ in meridian]
        for mode in ('disk', 'summary', 'coordinates'):
            answer = normal_component_census(raw, empty, mode=mode, max_cycles=0,
                                             record_certificate=True)
            self.assertEqual(answer['components'], 0)
            self.assertEqual(answer['component_histogram'], [])
            self.assertTrue(verify_normal_component_certificate(raw, empty, answer['certificate']))
        for options in (dict(mode='unknown'), dict(record_certificate=1), dict(max_cycles=-1)):
            with self.assertRaises(ValueError):
                normal_component_census(raw, meridian, **options)

    @unittest.skipUnless(importlib.util.find_spec('regina'), 'optional Regina oracle absent')
    def test_native_component_coordinate_multisets(self):
        import regina
        cases = 0
        for tetrahedra in (1, 3, 5):
            raw, _ = layered_torus(tetrahedra)
            native = regina_triangulation(raw)
            vectors = [export_surface(surface)
                       for surface in regina.NormalSurfaces(native, regina.NS_STANDARD)]
            for vector in vectors:
                answer = normal_component_census(raw, vector, mode='coordinates',
                                                 record_certificate=True)
                expected = {}
                expected_discs = 0
                for component in regina_surface(native, vector).components():
                    key = tuple(value for row in export_surface(component) for value in row)
                    expected[key] = expected.get(key, 0) + 1
                    expected_discs += int(component.isCompressingDisc())
                actual = {tuple(value for row in entry['coordinates'] for value in row):
                          entry['multiplicity'] for entry in answer['component_histogram']}
                self.assertEqual(actual, expected)
                self.assertEqual(answer['compressing_disk_components'], expected_discs)
                self.assertTrue(verify_normal_component_certificate(raw, vector,
                                                                     answer['certificate']))
                cases += 1
        self.assertGreater(cases, 10)


if __name__ == '__main__':
    unittest.main()
