"""Source-bound normal topology proofs, malformed evidence and search isolation."""
from copy import deepcopy
import json
import random
import unittest
from unittest.mock import patch

from fastunknot.integer_codec import json_safe
from fastunknot.normal_surface_orbits import normal_surface_topology, NormalOrbitError
from fastunknot.normal_surface_verify import verify_normal_surface_certificate
from fastunknot.normal_surface_geometry import _prepare, _coordinates, _fingerprint
from normal_orbit_research.fixtures import layered_torus
from test_normal_surface_orbits import relabel


class NormalSurfaceCertificateTests(unittest.TestCase):
    def setUp(self):
        self.tri, self.coords = layered_torus(4)
        # Keep the local-reduction mutation tests on the legacy three-query
        # format; derived double proofs have separate schema/mutation tests.
        self.result = normal_surface_topology(self.tri, self.coords, record_certificate=True,coorientation=False)
        self.proof = self.result['certificate']

    def verify(self, proof):
        return verify_normal_surface_certificate(self.tri, self.coords, proof)

    def test_replay_calls_neither_orbit_nor_topology_nor_cohomology_search(self):
        with patch('fastunknot.interval_orbits.count_orbits', side_effect=AssertionError), \
             patch('fastunknot.normal_surface_orbits.count_orbits', side_effect=AssertionError), \
             patch('fastunknot.normal_surface_orbits.normal_surface_topology', side_effect=AssertionError), \
             patch('fastunknot.normal_surface_parity._parity_certificate', side_effect=AssertionError):
            self.assertTrue(self.verify(self.proof))

    def test_opt_in_preserves_result_and_cycle_accounting(self):
        for rule in ('fine_wilf', 'aht'):
            old = normal_surface_topology(self.tri, self.coords, periodic_rule=rule)
            new = normal_surface_topology(self.tri, self.coords, periodic_rule=rule,
                                          record_certificate=True)
            certificate = new.pop('certificate')
            self.assertEqual(old, new)
            self.assertTrue(self.verify(certificate))
            for budget in (0, old['cycles'] - 1):
                partial = normal_surface_topology(self.tri, self.coords,
                    max_cycles=budget, periodic_rule=rule, record_certificate=True)
                self.assertEqual(partial['status'], 'INCONCLUSIVE')
                self.assertNotIn('certificate', partial)
                self.assertNotIn('compressing_disk', partial)
            full = normal_surface_topology(self.tri, self.coords,
                max_cycles=old['cycles'], periodic_rule=rule, record_certificate=True)
            self.assertTrue(self.verify(full['certificate']))
        with self.assertRaises(ValueError):
            normal_surface_topology(self.tri, self.coords, record_certificate=1)

    def test_empty_linking_one_sided_and_arbitrary_binary_multiplicity(self):
        tri, meridian = layered_torus(1)
        cases = [meridian, [[1, 1, 1, 1, 0, 0, 0]], [[0, 0, 0, 0, 0, 1, 0]]]
        for base in cases:
            for scale in (0, 1, 2, 7, 2 ** 20000 + 1):
                vector = [[value * scale for value in row] for row in base]
                result = normal_surface_topology(tri, vector, record_certificate=True)
                transport = json.loads(json.dumps(json_safe(result['certificate'])))
                self.assertTrue(verify_normal_surface_certificate(tri, vector, transport))
                encoded = [[hex(value) for value in row] for row in vector]
                self.assertTrue(verify_normal_surface_certificate(tri, encoded, transport))
                if base == cases[1]:
                    self.assertFalse(result['compressing_disk'])
                    self.assertFalse(result['certificate']['boundary_homology']['nonzero'])

    def test_source_and_query_binding_survives_digest_rewrite(self):
        other = [[2 * v for v in row] for row in self.coords]
        self.assertFalse(verify_normal_surface_certificate(self.tri, other, self.proof))
        forged = deepcopy(self.proof)
        analysed = _coordinates(_prepare(self.tri, lambda: None), other, lambda: None)
        forged['input_sha256'] = _fingerprint(self.tri, analysed, lambda: None)
        self.assertFalse(verify_normal_surface_certificate(self.tri, other, forged))
        # A fresh valid orbit proof for another supplied vector cannot be substituted.
        foreign = normal_surface_topology(self.tri, other, record_certificate=True,
                                         reduce_multiplicity=False)['certificate']
        forged = deepcopy(self.proof)
        forged['queries']['surface'] = foreign['queries']['surface']
        self.assertFalse(self.verify(forged))
        tri, vector = relabel(self.tri, self.coords, random.Random(12349))
        self.assertFalse(verify_normal_surface_certificate(tri, vector, self.proof))
        self.assertTrue(verify_normal_surface_certificate(tri, vector,
            normal_surface_topology(tri, vector, record_certificate=True)['certificate']))

    def test_every_topology_claim_is_checked_with_strict_types(self):
        for key, value in self.proof['topology'].items():
            forged = deepcopy(self.proof)
            forged['topology'][key] = not value if type(value) is bool else value + 1
            self.assertFalse(self.verify(forged), key)
            forged['topology'][key] = 1 if type(value) is bool else True
            self.assertFalse(self.verify(forged), key)
        for key in self.proof['topology']:
            forged = deepcopy(self.proof)
            del forged['topology'][key]
            self.assertFalse(self.verify(forged))
        forged = deepcopy(self.proof)
        forged['topology']['knot_is_unknot'] = True
        self.assertFalse(self.verify(forged))

    def test_malformed_schemas_and_reduction_witnesses(self):
        for bad in (None, [], {}, True, 1):
            self.assertFalse(self.verify(bad))
        for key in self.proof:
            forged = deepcopy(self.proof)
            del forged[key]
            self.assertFalse(self.verify(forged))
        for field in ('topology', 'queries', 'boundary_homology'):
            for value in ([], 4, None, True):
                forged = deepcopy(self.proof)
                forged[field] = value
                self.assertFalse(self.verify(forged))
        for label in self.proof['queries']:
            for mutation in ('count', 'trace', 'size', 'pairs'):
                forged = deepcopy(self.proof)
                query = forged['queries'][label]
                if mutation == 'count': query['orbit_count'] += 1
                elif mutation == 'trace': query['operations'] = []
                elif mutation == 'size': query['size'] += 1
                else: query['pairings'] = []
                self.assertFalse(self.verify(forged), (label, mutation))

    def test_odd_cycle_and_exact_potential_witnesses(self):
        from fastunknot.normal_surface_parity import _parity_certificate, _verify_parity
        # Exercise an odd cycle with three distinct vertices, not just torus loops.
        graph = [(0, 1, 1), (1, 2, 0), (2, 0, 0)]
        cycle = _parity_certificate(graph, lambda: None)
        self.assertEqual(cycle, dict(nonzero=True, cycle_edges=[0, 1, 2]))
        self.assertTrue(_verify_parity(graph, cycle, lambda: None))
        self.assertFalse(_verify_parity(graph, dict(nonzero=True, cycle_edges=[0]), lambda: None))
        exact = [(0, 1, 1), (1, 2, 0), (2, 0, 1)]
        potentials = _parity_certificate(exact, lambda: None)
        self.assertFalse(potentials['nonzero'])
        self.assertTrue(_verify_parity(exact, potentials, lambda: None))
        potentials['vertex_values'][1][1] ^= 1
        self.assertFalse(_verify_parity(exact, potentials, lambda: None))
        self.assertTrue(self.proof['boundary_homology']['nonzero'])
        for cycle in ([], [True], [100000], [0, 0]):
            forged = deepcopy(self.proof)
            forged['boundary_homology']['cycle_edges'] = cycle
            self.assertFalse(self.verify(forged))
        tri, _ = layered_torus(1)
        vector = [[1, 1, 1, 1, 0, 0, 0]]
        proof = normal_surface_topology(tri, vector, record_certificate=True)['certificate']
        self.assertTrue(verify_normal_surface_certificate(tri, vector, proof))
        self.assertFalse(proof['boundary_homology']['nonzero'])
        for pairs in ([], [[0, True]], [[0, 0], [0, 0]], None):
            forged = deepcopy(proof)
            forged['boundary_homology']['vertex_values'] = pairs
            self.assertFalse(verify_normal_surface_certificate(tri, vector, forged))

    def test_shared_replay_limit_and_callback_exceptions(self):
        total = sum(len(p['operations']) for p in self.proof['queries'].values())
        self.assertTrue(verify_normal_surface_certificate(self.tri, self.coords,
            self.proof, max_operations=total))
        self.assertFalse(verify_normal_surface_certificate(self.tri, self.coords,
            self.proof, max_operations=total - 1))
        for bad in (-1, True, 1.5):
            with self.assertRaises(ValueError):
                verify_normal_surface_certificate(self.tri, self.coords,
                    self.proof, max_operations=bad)
        checkpoints = 0
        def count_checkpoints():
            nonlocal checkpoints
            checkpoints += 1
        self.assertTrue(verify_normal_surface_certificate(self.tri, self.coords,
            self.proof, check=count_checkpoints))
        for stop in (1, checkpoints // 2, checkpoints - 1):
            calls = 0
            def check():
                nonlocal calls
                calls += 1
                if calls == stop:
                    raise ValueError('external cancellation')
            with self.assertRaisesRegex(ValueError, 'external cancellation'):
                verify_normal_surface_certificate(self.tri, self.coords,
                    self.proof, check=check)

    def test_ambient_validation_cannot_be_replaced_by_a_hash(self):
        with self.assertRaises(NormalOrbitError):
            verify_normal_surface_certificate({'tetrahedra': [[None] * 4]},
                [[0] * 7], self.proof)
        bad = deepcopy(self.coords)
        bad[0][0] = True
        with self.assertRaises(NormalOrbitError):
            verify_normal_surface_certificate(self.tri, bad, self.proof)


if __name__ == '__main__':
    unittest.main()
