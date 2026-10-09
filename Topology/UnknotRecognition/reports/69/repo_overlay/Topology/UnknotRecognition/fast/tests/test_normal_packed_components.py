"""Cross-check packed component coordinates, transport invariants and replay."""

from copy import deepcopy
from itertools import product
import json
from pathlib import Path
import random
import unittest

from fastunknot.integer_codec import json_safe
from fastunknot.normal_packed_components import normal_packed_component_census
from fastunknot.normal_packed_verify import verify_normal_packed_certificate
from fastunknot.normal_support import compile_normal_support
from fastunknot.normal_surface_components import normal_component_census
from normal_orbit_research.fixtures import layered_torus, interior_vertex_torus, boundary_cap


def combine(basis, coefficients):
    return [[sum(c*v[t][j] for c, v in zip(coefficients, basis))
             for j in range(7)] for t in range(len(basis[0]))]


def semantic(answer):
    return {key: answer[key] for key in ('components', 'compressing_disk_components',
             'contains_compressing_disk', 'component_histogram')}


class PackedNormalComponentsTests(unittest.TestCase):
    def compare(self, raw, vector):
        old = normal_component_census(raw, vector, mode='coordinates')
        answers = []
        for encoding in ('vector', 'packed'):
            result = normal_packed_component_census(raw, vector, encoding=encoding,
                                                    record_certificate=True)
            self.assertEqual(result['status'], 'COMPLETE')
            self.assertEqual(semantic(result), semantic(old))
            self.assertTrue(verify_normal_packed_certificate(raw, vector, result['certificate']))
            answers.append(result)
        # Packing is injective on every live fibre, so the exact run partition
        # and geometric trace agree, not merely the final number of components.
        for key in ('input_weight_runs', 'maximum_weight_runs', 'translation_pushes',
                    'reflection_pushes', 'emitted_weight_runs', 'replay_events'):
            self.assertEqual(answers[0]['stats'][key], answers[1]['stats'][key])
        return answers

    def test_dense_fibonacci_support(self):
        for t in (1, 2, 4, 8, 16, 24):
            raw, meridian = layered_torus(t)
            result = self.compare(raw, meridian)[1]
            self.assertEqual(result['projection_dimension'], 1)
            self.assertEqual(result['packed_bits'], 1)
            self.assertEqual(result['compressing_disk_components'], 1)

    def test_boundary_caps(self):
        raw, vector = layered_torus(3)
        for _ in range(4):
            raw, vector = boundary_cap(raw, vector)
            self.compare(raw, vector)

    def test_all_small_compatible_mixtures(self):
        raw, basis = interior_vertex_torus()
        for coefficients in product(range(3), repeat=3):
            with self.subTest(coefficients=coefficients):
                self.compare(raw, combine(list(basis.values()), coefficients))

    def test_one_sided_double_and_no_false_disk(self):
        raw, _ = layered_torus(1)
        for m in (1, 2, 3, 4, 10, 101):
            answer = self.compare(raw, [[0, 0, 0, 0, 0, m, 0]])[1]
            self.assertEqual(answer['components'], (m+1)//2)
            self.assertFalse(answer['contains_compressing_disk'])

    def test_large_unequal_component_multiplicities(self):
        raw, basis = interior_vertex_torus()
        vector = combine(list(basis.values()), (2**137+3, 2**71+1, 2**83+5))
        answer = self.compare(raw, vector)[1]
        self.assertGreater(answer['packed_bits'], 100)
        self.assertFalse(answer['contains_compressing_disk'])

    def test_reuse_kernel_and_orbit_trace(self):
        raw, meridian = layered_torus(8)
        kernel = compile_normal_support(raw, meridian)
        twice = [[2*v for v in row] for row in meridian]
        first = normal_packed_component_census(raw, twice, record_certificate=True,
                                               support_certificate=kernel)
        trace = first['certificate']['weighted_orbits']['orbit_proof']
        again = normal_packed_component_census(raw, twice, encoding='vector',
            support_certificate=kernel, orbit_certificate=trace, record_certificate=True)
        self.assertEqual(semantic(first), semantic(again))
        self.assertFalse(first['freshly_optimized_projection'])
        self.assertTrue(verify_normal_packed_certificate(raw, twice, again['certificate']))
        with self.assertRaises(ValueError):
            normal_packed_component_census(raw, [[0]*7 for _ in twice],
                                           support_certificate=kernel)

    def test_hexadecimal_roundtrip(self):
        raw, meridian = layered_torus(1)
        coordinates = [[value * (2**5001+1) for value in row] for row in meridian]
        result = normal_packed_component_census(raw, coordinates, record_certificate=True)
        serialized = json.loads(json.dumps(json_safe(result['certificate'])))
        self.assertTrue(verify_normal_packed_certificate(raw, coordinates, serialized))

    def test_reject_mutated_claims(self):
        raw, vector = layered_torus(3)
        proof = normal_packed_component_census(raw, vector, record_certificate=True)['certificate']
        mutations = []
        bad = deepcopy(proof); bad['input_sha256'] = '0'*64; mutations.append(bad)
        bad = deepcopy(proof); bad['encoding'] = 'lossy'; mutations.append(bad)
        bad = deepcopy(proof); bad['summary']['components'] += 1; mutations.append(bad)
        bad = deepcopy(proof); bad['summary']['compressing_disk_components'] = 0; mutations.append(bad)
        bad = deepcopy(proof); bad['support_kernel']['denominator'] = 0; mutations.append(bad)
        bad = deepcopy(proof); bad['support_kernel']['nullity'] += 1; mutations.append(bad)
        bad = deepcopy(proof); bad['support_kernel']['numerators'][0][0] += 1; mutations.append(bad)
        bad = deepcopy(proof); bad['weighted_orbits']['histogram'][0]['weight'][0] += 1; mutations.append(bad)
        bad = deepcopy(proof); bad['boundary_homology_basis'][1] = bad['boundary_homology_basis'][0]; mutations.append(bad)
        bad = deepcopy(proof); bad['unexpected'] = True; mutations.append(bad)
        for bad in mutations:
            self.assertFalse(verify_normal_packed_certificate(raw, vector, bad))

    def test_empty_and_cycle_cap(self):
        raw, meridian = layered_torus(4)
        zero = [[0]*7 for _ in meridian]
        answer = self.compare(raw, zero)[1]
        self.assertEqual(answer['components'], 0)
        self.assertEqual(answer['projection_dimension'], 0)
        capped = normal_packed_component_census(raw, meridian, max_cycles=0,
                                                record_certificate=True)
        self.assertEqual(capped['status'], 'INCONCLUSIVE')
        self.assertNotIn('certificate', capped)

    def test_cancellation_propagates(self):
        class Cancelled(RuntimeError):
            pass
        def cancel():
            raise Cancelled()
        raw, vector = layered_torus(2)
        proof = normal_packed_component_census(raw, vector, record_certificate=True)['certificate']
        with self.assertRaises(Cancelled):
            normal_packed_component_census(raw, vector, check=cancel)
        with self.assertRaises(Cancelled):
            verify_normal_packed_certificate(raw, vector, proof, check=cancel)


if __name__ == '__main__':
    unittest.main()
