"""Geometric integration, source binding and resource semantics for spectra."""

from copy import deepcopy
from itertools import product
import json
from pathlib import Path
import unittest
from unittest.mock import patch

from fastunknot.integer_codec import json_safe
from fastunknot.normal_surface_geometry import NormalOrbitError
from fastunknot.normal_topology import normal_topology_spectrum
from fastunknot.normal_topology_verify import verify_normal_topology_spectrum
from fastunknot.normal_topology_geometry import embed_boundary_intervals
from fastunknot.normal_surface_geometry import _prepare, _coordinates
from normal_orbit_research.fixtures import (
    layered_torus, interior_vertex_torus, boundary_cap,
)


ROOT = Path(__file__).resolve().parents[1]


def signatures(answer):
    return {(row['chi'], row['boundary_components'], row['orientable']):
            row['multiplicity'] for row in answer['topology_spectrum']}


def mixture(basis, coefficients):
    return [[sum(a * x[t][j] for a, x in zip(coefficients, basis))
             for j in range(7)] for t in range(len(basis[0]))]


class NormalTopologySpectrumTests(unittest.TestCase):
    def check_source(self, raw, vector, expected):
        for reduced in (False, True):
            answer = normal_topology_spectrum(raw, vector, reduce_core=reduced,
                                              record_certificate=True)
            self.assertEqual(signatures(answer), {k: v for k, v in expected.items() if v})
            self.assertTrue(verify_normal_topology_spectrum(raw, vector,
                                                           answer['certificate']))
        return answer

    def test_layered_meridians_and_multiple_boundary_vertices(self):
        for t in (1, 3, 8):
            raw, vector = layered_torus(t)
            self.check_source(raw, vector, {(1, 1, True): 1})
            raw, vector = boundary_cap(raw, vector)
            self.check_source(raw, vector, {(1, 1, True): 1})

    def test_disconnected_spheres_disks_and_one_sided_components(self):
        raw, basis = interior_vertex_torus()
        for a, b, c in product(range(3), repeat=3):
            vector = mixture(list(basis.values()), (a, b, c))
            self.check_source(raw, vector, {(2, 0, True): a, (1, 1, True): b,
                (0, 2, True): c // 2, (0, 1, False): c % 2})

    def test_zero_signature_torus_and_klein_bottle(self):
        fixture = json.loads((ROOT / 'topology_research/data/klein_torus.json').read_text())
        raw, klein = fixture['triangulation'], fixture['coordinates']
        for scale in (1, 2, 3, 4, 5, 8):
            vector = [[scale * value for value in row] for row in klein]
            self.check_source(raw, vector,
                              {(0, 0, True): scale // 2, (0, 0, False): scale % 2})

    def test_projective_plane_and_sphere_double(self):
        fixture = json.loads((ROOT /
            'normal_orbit_research/data/projective_plane_torus.json').read_text())
        raw, plane = fixture['triangulation'], fixture['coordinates']
        for scale in (1, 2, 3):
            vector = [[scale * value for value in row] for row in plane]
            self.check_source(raw, vector,
                              {(2, 0, True): scale // 2, (1, 0, False): scale % 2})

    def test_coprime_multiplicity_kernel_has_constant_query_size(self):
        raw, basis = interior_vertex_torus()
        query_stats = []
        for bits in (8, 128, 12000):
            g = (1 << bits) + 1
            vector = mixture(list(basis.values()), (g + 2, g + 1, g))
            answer = normal_topology_spectrum(raw, vector, record_certificate=True)
            self.assertEqual(signatures(answer), {(2, 0, True): g + 2,
                (1, 1, True): g + 1, (0, 2, True): g // 2, (0, 1, False): 1})
            self.assertEqual(answer['certificate']['coordinate_divisor'], g)
            query_stats.append((answer['stats']['orbit_cycles'],
                                answer['stats']['query_coordinate_bits']))
            transported = json.loads(json.dumps(json_safe(answer['certificate'])))
            self.assertTrue(verify_normal_topology_spectrum(raw, vector, transported))
        self.assertEqual(len(set(query_stats)), 1)

    def test_pure_vertex_links_need_no_orbit_query(self):
        raw, basis = interior_vertex_torus()
        vector = mixture(list(basis.values()), (17, 23, 0))
        with patch('fastunknot.normal_topology.orbit_transversal', side_effect=AssertionError), \
             patch('fastunknot.normal_topology.weighted_orbit_histogram',
                   side_effect=AssertionError):
            answer = normal_topology_spectrum(raw, vector, max_cycles=0,
                                              record_certificate=True)
        self.assertEqual(answer['stats']['queries'], 0)
        self.assertTrue(verify_normal_topology_spectrum(raw, vector, answer['certificate']))

    def test_one_budget_across_three_discoveries(self):
        raw, vector = layered_torus(4)
        answer = normal_topology_spectrum(raw, vector, record_certificate=True)
        used = answer['stats']['orbit_cycles']
        for cap in (0, 1, used - 1):
            result = normal_topology_spectrum(raw, vector, max_cycles=cap,
                                              record_certificate=True)
            self.assertEqual(result['status'], 'INCONCLUSIVE')
            for field in ('topology_spectrum', 'components', 'certificate'):
                self.assertNotIn(field, result)
            self.assertLessEqual(result['stats']['orbit_cycles'], cap)
        exact = normal_topology_spectrum(raw, vector, max_cycles=used,
                                         record_certificate=True)
        self.assertEqual(answer, exact)

    def test_both_periodic_rules_produce_the_same_spectrum(self):
        raw, vector = layered_torus(9)
        fine = normal_topology_spectrum(raw, vector, periodic_rule='fine_wilf')
        classic = normal_topology_spectrum(raw, vector, periodic_rule='aht',
                                            record_certificate=True)
        self.assertEqual(signatures(fine), signatures(classic))
        self.assertTrue(verify_normal_topology_spectrum(raw, vector, classic['certificate']))

    def test_original_source_reduction_and_summary_mutations_rejected(self):
        raw, basis = interior_vertex_torus()
        vector = mixture(list(basis.values()), (3, 4, 5))
        proof = normal_topology_spectrum(raw, vector, record_certificate=True)['certificate']
        wrong = mixture(list(basis.values()), (4, 4, 5))
        self.assertFalse(verify_normal_topology_spectrum(raw, wrong, proof))
        for key in list(proof):
            changed = deepcopy(proof)
            del changed[key]
            self.assertFalse(verify_normal_topology_spectrum(raw, vector, changed))
        for key, value in [('schema', 'unknown'), ('reduced_core', 1),
                           ('coordinate_divisor', True), ('coordinate_divisor', 10),
                           ('core_coordinates', []), ('vertex_links', [])]:
            changed = deepcopy(proof)
            changed[key] = value
            self.assertFalse(verify_normal_topology_spectrum(raw, vector, changed))
        for field in ('components', 'orientable_components', 'nonorientable_components',
                      'boundary_components', 'euler_characteristic'):
            changed = deepcopy(proof)
            changed['summary'][field] += 1
            self.assertFalse(verify_normal_topology_spectrum(raw, vector, changed))
        changed = deepcopy(proof)
        changed['query']['topology_spectrum'][0]['orientable'] = True
        self.assertFalse(verify_normal_topology_spectrum(raw, vector, changed))
        changed = deepcopy(proof)
        changed['query']['double']['histogram'][0]['orbits'] += 1
        self.assertFalse(verify_normal_topology_spectrum(raw, vector, changed))
        changed = deepcopy(proof)
        changed['query']['boundary_transversal']['representative_intervals'] = []
        self.assertFalse(verify_normal_topology_spectrum(raw, vector, changed))

    def test_replay_without_producer_algorithms(self):
        raw, basis = interior_vertex_torus()
        vector = mixture(list(basis.values()), (7, 11, 9))
        proof = normal_topology_spectrum(raw, vector, record_certificate=True)['certificate']
        disabled = ['normal_topology.normal_topology_spectrum',
                    'normal_topology.canonical_disk_core',
                    'normal_topology.orbit_transversal',
                    'orbit_transversal._forward_selector',
                    'weighted_orbits.count_orbits', 'weighted_orbits._replay',
                    'topology_spectrum.recover_topology_spectrum',
                    'topology_spectrum.scale_core_spectrum']
        from contextlib import ExitStack
        with ExitStack() as stack:
            for name in disabled:
                stack.enter_context(patch('fastunknot.' + name, side_effect=AssertionError))
            self.assertTrue(verify_normal_topology_spectrum(raw, vector, proof))

    def test_boundary_embedding_matches_literal_small_edge_inclusion(self):
        raw, vector = boundary_cap(*layered_torus(3))
        prepared = _prepare(raw, lambda: None)
        analysed = _coordinates(prepared, vector, lambda: None)
        embedding, full = [], 0
        for edge in sorted(analysed['weights']):
            size = analysed['weights'][edge]
            if edge in prepared['boundary_incidence']:
                embedding.extend(range(full, full + size))
            full += size
        for lo in range(len(embedding)):
            hi = min(lo + 4, len(embedding))
            intervals = embed_boundary_intervals(prepared, analysed, [(lo, hi)])
            self.assertEqual([point for a, b in intervals for point in range(a, b)],
                             embedding[lo:hi])

    def test_invalid_sources_and_options(self):
        raw, vector = layered_torus(1)
        for kwargs in ({'reduce_core': 1}, {'record_certificate': 0},
                       {'max_cycles': True}, {'max_cycles': -1},
                       {'periodic_rule': 'unknown'}):
            with self.assertRaises(ValueError):
                normal_topology_spectrum(raw, vector, **kwargs)
        for bad in ([[True] * 7], [[-1] * 7], [[1] * 6]):
            with self.assertRaises(NormalOrbitError):
                normal_topology_spectrum(raw, bad)

    def test_late_cancellation_and_false_valued_callbacks(self):
        class Stop(RuntimeError):
            pass

        class Check:
            def __init__(self, stop=None):
                self.calls, self.stop = 0, stop

            def __bool__(self):
                return False

            def __call__(self):
                self.calls += 1
                if self.calls == self.stop:
                    raise Stop

        raw, vector = layered_torus(4)
        count = Check()
        answer = normal_topology_spectrum(raw, vector, check=count, record_certificate=True)
        for where in (1, count.calls // 2, count.calls):
            with self.assertRaises(Stop):
                normal_topology_spectrum(raw, vector, check=Check(where), record_certificate=True)
        count = Check()
        self.assertTrue(verify_normal_topology_spectrum(raw, vector,
                                                       answer['certificate'], check=count))
        for where in (1, count.calls // 2, count.calls):
            with self.assertRaises(Stop):
                verify_normal_topology_spectrum(raw, vector, answer['certificate'],
                                                check=Check(where))


if __name__ == '__main__':
    unittest.main()
