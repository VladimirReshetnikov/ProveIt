"""Ray-block disc counts: geometry, one-sided guards and independent replay."""

from copy import deepcopy
from itertools import product
import json
from pathlib import Path
import unittest
from unittest.mock import patch

from fastunknot.integer_codec import json_safe
from fastunknot.normal_ray_blocks import normal_ray_block_disk_count
from fastunknot.normal_ray_blocks_verify import verify_normal_ray_block_disk_certificate
from fastunknot.normal_surface_components import normal_component_census
from fastunknot.normal_surface_geometry import _prepare, _coordinates, NormalOrbitError
from fastunknot.normal_support import compile_support
from normal_orbit_research.fixtures import layered_torus, interior_vertex_torus, boundary_cap


ROOT = Path(__file__).resolve().parents[1]


def mixture(basis, coefficients):
    vectors = list(basis.values())
    return [[sum(c*x[t][j] for c, x in zip(coefficients, vectors)) for j in range(7)]
            for t in range(len(vectors[0]))]


class NormalRayBlockTests(unittest.TestCase):
    def test_dense_fibonacci_rays_need_no_orbit_discovery(self):
        for tetrahedra in (1, 2, 4, 8, 16, 24):
            raw, meridian = layered_torus(tetrahedra)
            for multiplier in (1, 2, 2**4097+7):
                vector = [[multiplier*value for value in row] for row in meridian]
                with patch('fastunknot.normal_ray_blocks.normal_compressing_disk_count',
                           side_effect=AssertionError('rank-one source used fallback')), \
                     patch('fastunknot.normal_ray_blocks.compile_support',
                           side_effect=AssertionError('peelable ray used dense rank compilation')), \
                     patch('fastunknot.normal_ray_blocks.gcd',
                           side_effect=AssertionError('unit ray used a producer gcd scan')), \
                     patch('fastunknot.normal_ray_blocks_verify.gcd',
                           side_effect=AssertionError('unit ray used a verifier gcd scan')), \
                     patch('fastunknot.normal_ray_blocks.divmod', create=True,
                           side_effect=AssertionError('unit ray divided by the source scale')), \
                     patch('fastunknot.normal_ray_blocks_verify.divmod', create=True,
                           side_effect=AssertionError('unit replay divided by the source scale')):
                    answer = normal_ray_block_disk_count(raw, vector, max_cycles=0,
                                                         record_certificate=True)
                self.assertEqual(answer['status'], 'COMPLETE')
                self.assertEqual(answer['compressing_disk_components'], multiplier)
                self.assertEqual(answer['stats']['support_dimensions'], [1])
                self.assertEqual(answer['stats']['ray_blocks'], 1)
                self.assertEqual(answer['stats']['peeling_ray_blocks'], 1)
                self.assertEqual(answer['stats']['compiled_ray_blocks'], 0)
                self.assertEqual(answer['stats']['orbit_cycles'], 0)
                self.assertEqual(len(answer['certificate']['blocks'][0]['support']), 3*tetrahedra)
                self.assertTrue(verify_normal_ray_block_disk_certificate(
                    raw, vector, answer['certificate']))
                self.assertNotIn('components', answer)

    def test_exact_general_rank_certificate_remains_a_valid_fallback(self):
        raw, vector = layered_torus(7)
        with patch('fastunknot.normal_ray_blocks.peel_support_ray', return_value=None):
            answer = normal_ray_block_disk_count(raw, vector, max_cycles=0,
                                                 record_certificate=True)
        self.assertEqual(answer['compressing_disk_components'], 1)
        self.assertEqual(answer['stats']['peeling_ray_blocks'], 0)
        self.assertEqual(answer['stats']['compiled_ray_blocks'], 1)
        proof = answer['certificate']
        self.assertEqual(proof['blocks'][0]['support_certificate']['schema'],
                         'normal-support-kernel-v1')
        self.assertTrue(verify_normal_ray_block_disk_certificate(raw, vector, proof))

    def test_empty_source_and_independent_triangle_link_blocks(self):
        raw, basis = interior_vertex_torus()
        for coefficients in ((0, 0, 0), (2**2000, 2**2000+1, 0)):
            vector = mixture(basis, coefficients)
            with patch('fastunknot.normal_ray_blocks.normal_compressing_disk_count',
                       side_effect=AssertionError('link ray used fallback')):
                answer = normal_ray_block_disk_count(raw, vector, max_cycles=0,
                                                     record_certificate=True)
            self.assertEqual(answer['compressing_disk_components'], 0)
            self.assertFalse(answer['contains_compressing_disk'])
            self.assertEqual(answer['stats']['blocks'], 0 if not any(coefficients) else 2)
            self.assertEqual(answer['stats']['fallback_blocks'], 0)
            self.assertEqual(answer['stats']['orbit_cycles'], 0)
            self.assertTrue(verify_normal_ray_block_disk_certificate(
                raw, vector, answer['certificate']))

    def test_one_sided_mobius_ray_never_claims_disc_or_linear_component_count(self):
        raw, _ = layered_torus(1)
        for multiplier in (1, 2, 3, 10, 2**4099+1):
            vector = [[0, 0, 0, 0, 0, multiplier, 0]]
            answer = normal_ray_block_disk_count(raw, vector, max_cycles=0,
                                                 record_certificate=True)
            self.assertEqual(answer['stats']['ray_blocks'], 1)
            self.assertEqual(answer['compressing_disk_components'], 0)
            self.assertEqual(answer['certificate']['blocks'][0]['coordinate_divisor'], multiplier)
            self.assertEqual(answer['certificate']['blocks'][0]['primitive_euler_characteristic'], 0)
            self.assertNotIn('components', answer)
            self.assertTrue(verify_normal_ray_block_disk_certificate(
                raw, vector, answer['certificate']))
            if multiplier < 20:
                census = normal_component_census(raw, vector)
                self.assertEqual(census['components'], (multiplier+1)//2)

    def test_closed_projective_plane_chi_one_is_not_an_essential_disc(self):
        fixture = json.loads((ROOT / 'normal_orbit_research/data/projective_plane_torus.json').read_text())
        raw, plane = fixture['triangulation'], fixture['coordinates']
        for multiplier in (1, 2, 7):
            vector = [[multiplier*value for value in row] for row in plane]
            answer = normal_ray_block_disk_count(raw, vector, record_certificate=True)
            self.assertEqual(answer['compressing_disk_components'], 0)
            self.assertTrue(verify_normal_ray_block_disk_certificate(
                raw, vector, answer['certificate']))
            for block in answer['certificate']['blocks']:
                if block['method'] == 'ray' and block['primitive_euler_characteristic'] == 1:
                    self.assertEqual(block['primitive_boundary_homology_mod2'], [0, 0])

    def test_mixed_nullity_blocks_match_complete_component_query(self):
        raw, basis = interior_vertex_torus()
        for coefficients in product(range(3), repeat=3):
            vector = mixture(basis, coefficients)
            answer = normal_ray_block_disk_count(raw, vector, record_certificate=True)
            reference = normal_component_census(raw, vector)
            self.assertEqual(answer['compressing_disk_components'],
                             reference['compressing_disk_components'])
            self.assertTrue(verify_normal_ray_block_disk_certificate(
                raw, vector, answer['certificate']))

    def test_actual_support_inventory_bound_and_sharp_one_sided_controls(self):
        raw, _ = layered_torus(1)
        cases = [([[0, 0, 0, 0, 0, 3, 0]], 1, 0, 2),
                 ([[1, 1, 1, 1, 0, 3, 0]], 2, 1, 3),
                 ([[1, 1, 1, 1, 0, 2, 0]], 2, 1, 2)]
        for vector, expected_dimension, expected_links, expected_types in cases:
            prepared = _prepare(raw, lambda: None)
            analysed = _coordinates(prepared, vector, lambda: None)
            dimension = compile_support(prepared, analysed)['nullity']
            minima = {}
            for t, row in enumerate(vector):
                for vertex in range(4):
                    root = prepared['vertex_roots'][4*t+vertex]
                    minima[root] = min(minima.get(root, row[vertex]), row[vertex])
            links = sum(value > 0 for value in minima.values())
            census = normal_component_census(raw, vector, mode='coordinates')
            types = len(census['component_histogram'])
            self.assertEqual((dimension, links, types),
                             (expected_dimension, expected_links, expected_types))
            self.assertLessEqual(types, 2*dimension-links)
        # The last source is a two-sided vertex disc plus the annular double.
        self.assertEqual(types, dimension)

    def test_vertex_link_plus_meridians_uses_exact_fallback_and_shared_cap(self):
        raw, meridian = layered_torus(5)
        factor, links = 2**1000, 2**1000+1
        vector = [[factor*value+(links if j < 4 else 0) for j, value in enumerate(row)]
                  for row in meridian]
        answer = normal_ray_block_disk_count(raw, vector, record_certificate=True)
        self.assertEqual(answer['compressing_disk_components'], factor)
        self.assertEqual(answer['stats']['fallback_blocks'], 1)
        cycles = answer['stats']['orbit_cycles']
        self.assertGreater(cycles, 0)
        for cap in (0, cycles-1):
            partial = normal_ray_block_disk_count(raw, vector, max_cycles=cap,
                                                  record_certificate=True)
            self.assertEqual(partial['status'], 'INCONCLUSIVE')
            for field in ('certificate', 'compressing_disk_components', 'contains_compressing_disk'):
                self.assertNotIn(field, partial)
        self.assertEqual(normal_ray_block_disk_count(raw, vector, max_cycles=cycles,
                                                     record_certificate=True), answer)
        self.assertTrue(verify_normal_ray_block_disk_certificate(raw, vector, answer['certificate']))

    def test_boundary_cap_preserves_meridian_count(self):
        raw, meridian = layered_torus(4)
        for _ in range(3):
            raw, meridian = boundary_cap(raw, meridian)
            answer = normal_ray_block_disk_count(raw, meridian, record_certificate=True)
            self.assertEqual(answer['compressing_disk_components'], 1)
            self.assertTrue(verify_normal_ray_block_disk_certificate(raw, meridian,
                                                                    answer['certificate']))

    def test_hex_transport_source_binding_and_input_immutability(self):
        raw, meridian = layered_torus(5)
        vector = [[(2**20000+1)*value for value in row] for row in meridian]
        old_raw, old_vector = deepcopy(raw), deepcopy(vector)
        with patch('fastunknot.normal_ray_blocks.divmod', create=True,
                   side_effect=AssertionError('large shared scalar was divided')), \
             patch('fastunknot.normal_ray_blocks_verify.divmod', create=True,
                   side_effect=AssertionError('large shared scalar was divided in replay')), \
             patch('fastunknot.normal_ray_blocks.gcd', side_effect=AssertionError), \
             patch('fastunknot.normal_ray_blocks_verify.gcd', side_effect=AssertionError):
            answer = normal_ray_block_disk_count(raw, vector, record_certificate=True)
            proof = json.loads(json.dumps(json_safe(answer['certificate'])))
            encoded_vector = json.loads(json.dumps(json_safe(vector)))
            self.assertTrue(verify_normal_ray_block_disk_certificate(raw, encoded_vector, proof))
        self.assertEqual(raw, old_raw)
        self.assertEqual(vector, old_vector)
        changed = [[2*value for value in row] for row in vector]
        self.assertFalse(verify_normal_ray_block_disk_certificate(raw, changed, proof))

    def test_ray_replay_imports_no_discovery_or_producer_helpers(self):
        raw, vector = layered_torus(6)
        proof = normal_ray_block_disk_count(raw, vector, record_certificate=True)['certificate']
        with patch('fastunknot.normal_ray_blocks._support_blocks', side_effect=AssertionError), \
             patch('fastunknot.normal_ray_blocks.compile_support', side_effect=AssertionError), \
             patch('fastunknot.normal_ray_blocks.peel_support_ray', side_effect=AssertionError), \
             patch('fastunknot.normal_ray_blocks._primitive_peeling_rows',
                   side_effect=AssertionError), \
             patch('fastunknot.normal_component_geometry.boundary_homology_basis',
                   side_effect=AssertionError), \
             patch('fastunknot.normal_disk_kernel.normal_component_census',
                   side_effect=AssertionError), \
             patch('fastunknot.weighted_orbits.count_orbits', side_effect=AssertionError):
            self.assertTrue(verify_normal_ray_block_disk_certificate(raw, vector, proof))

    def test_ray_count_rank_partition_and_basis_mutations_are_rejected(self):
        raw, vector = layered_torus(4)
        proof = normal_ray_block_disk_count(raw, vector, record_certificate=True)['certificate']
        for field, value in (('compressing_disk_components', 0),
                             ('coordinate_divisor', 2),
                             ('coordinate_divisor', True),
                             ('primitive_euler_characteristic', 0),
                             ('primitive_boundary_homology_mod2', [0, 0]),
                             ('support', proof['blocks'][0]['support'][:-1]),
                             ('method', 'unknown')):
            bad = deepcopy(proof)
            bad['blocks'][0][field] = value
            self.assertFalse(verify_normal_ray_block_disk_certificate(raw, vector, bad), field)
        for field, value in (('rank', 0), ('nullity', 2), ('nullity', True),
                             ('modulus', 1), ('denominator', 0)):
            bad = deepcopy(proof)
            bad['blocks'][0]['support_certificate'][field] = value
            self.assertFalse(verify_normal_ray_block_disk_certificate(raw, vector, bad), field)
        for field, value in (('blocks', []), ('compressing_disk_components', True),
                             ('compressing_disk_components', 0), ('extra', 0)):
            bad = deepcopy(proof)
            bad[field] = value
            self.assertFalse(verify_normal_ray_block_disk_certificate(raw, vector, bad), field)
        bad = deepcopy(proof)
        bad['boundary_homology_basis'][1] = bad['boundary_homology_basis'][0]
        self.assertFalse(verify_normal_ray_block_disk_certificate(raw, vector, bad))
        for value in (None, [], {}, True):
            bad = deepcopy(proof)
            bad['blocks'][0]['support_certificate'] = value
            self.assertFalse(verify_normal_ray_block_disk_certificate(raw, vector, bad))

    def test_fallback_certificate_mutation_is_rejected(self):
        raw, _ = layered_torus(1)
        vector = [[1, 1, 1, 1, 0, 1, 0]]
        proof = normal_ray_block_disk_count(raw, vector, record_certificate=True)['certificate']
        self.assertEqual(proof['blocks'][0]['method'], 'component_census')
        bad = deepcopy(proof)
        bad['blocks'][0]['certificate']['compressing_disk_components'] = 1
        self.assertFalse(verify_normal_ray_block_disk_certificate(raw, vector, bad))
        bad = deepcopy(proof)
        bad['blocks'][0]['compressing_disk_components'] = 1
        self.assertFalse(verify_normal_ray_block_disk_certificate(raw, vector, bad))

    def test_malformed_sources_options_and_cancellation(self):
        raw, vector = layered_torus(2)
        proof = normal_ray_block_disk_count(raw, vector, record_certificate=True)['certificate']
        for option in ({'max_cycles': True}, {'max_cycles': -1}, {'max_cycles': 1.5},
                       {'periodic_rule': 'unknown'}, {'record_certificate': 1}):
            with self.assertRaises(ValueError):
                normal_ray_block_disk_count(raw, vector, **option)
        for coordinates in ([[0]*7], [[-1]*7]*2, [[True]*7]*2, [[1]*7]*2):
            with self.assertRaises(NormalOrbitError):
                normal_ray_block_disk_count(raw, coordinates)
            self.assertFalse(verify_normal_ray_block_disk_certificate(raw, coordinates, proof))
        self.assertFalse(verify_normal_ray_block_disk_certificate({}, vector, proof))

        class Cancelled(Exception):
            pass

        operations = [lambda check: normal_ray_block_disk_count(raw, vector,
                        record_certificate=True, check=check),
                      lambda check: verify_normal_ray_block_disk_certificate(raw, vector,
                        proof, check=check)]
        for operation in operations:
            calls = [0]

            def count():
                calls[0] += 1

            operation(count)
            for threshold in (1, max(1, calls[0]//2), calls[0]):
                used = [0]

                def cancel():
                    used[0] += 1
                    if used[0] == threshold:
                        raise Cancelled()

                with self.assertRaises(Cancelled):
                    operation(cancel)


if __name__ == '__main__':
    unittest.main()
