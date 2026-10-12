"""Carry-free port encoding against explicit geometry and legacy source proofs."""
from contextlib import ExitStack
from copy import deepcopy
import json
from pathlib import Path
import unittest
from unittest.mock import patch

from fastunknot.integer_codec import json_safe
from fastunknot.normal_prism_interfaces import normal_prism_face_regions
from fastunknot.normal_prism_interfaces_verify import verify_normal_prism_interfaces
from normal_orbit_research.fixtures import layered_torus
from normal_orbit_research.prism_interfaces import explicit


class PrismPortEncodingTests(unittest.TestCase):
    def test_vector_bitset_and_literal_geometry_agree(self):
        for t in (1, 2, 4, 8):
            raw, vector = layered_torus(t)
            for n in (0, 1, 2, 3, 7):
                rows = [[n * x for x in row] for row in vector]
                expected = explicit(raw, rows)
                for encoding in ('auto', 'vector', 'bitset'):
                    result = normal_prism_face_regions(raw, rows, port_encoding=encoding, record_certificate=True)
                    self.assertEqual(result['structure'], expected)
                    self.assertTrue(verify_normal_prism_interfaces(raw, rows, result['certificate']))
                    if encoding == 'bitset':
                        self.assertEqual(result['weight_dimension'], 3)
                        self.assertEqual(result['certificate']['schema'], 'normal-prism-interfaces-v2')
                    elif encoding == 'vector':
                        self.assertEqual(result['weight_dimension'], 2 + len(expected['ports']))
                        self.assertEqual(result['certificate']['schema'], 'normal-prism-interfaces-v1')

    def test_every_saved_legacy_proof_replays_with_producers_disabled(self):
        path = Path(__file__).resolve().parents[2] / 'synthesis/data/prism-interfaces-audit.json'
        proofs = json.loads(path.read_text())['source_proofs']
        self.assertEqual(len(proofs), 58)
        with ExitStack() as stack:
            for name in ('fastunknot.normal_prism_interfaces._interface_system',
                         'fastunknot.normal_prism_interfaces._profiles',
                         'fastunknot.weighted_orbits.weighted_orbit_histogram',
                         'fastunknot.interval_orbits.count_orbits'):
                stack.enter_context(patch(name, side_effect=AssertionError('producer used')))
            for row in proofs:
                self.assertTrue(verify_normal_prism_interfaces(row['triangulation'], row['coordinates'], row['certificate']))

    def test_many_ports_and_large_binary_multiplicity(self):
        raw, vector = layered_torus(64)
        rows = [[(1 << 500) * x for x in row] for row in vector]
        bitset = normal_prism_face_regions(raw, rows, port_encoding='bitset', record_certificate=True)
        vector_result = normal_prism_face_regions(raw, rows, port_encoding='vector')
        self.assertEqual(bitset['structure'], vector_result['structure'])
        self.assertGreater(len(bitset['structure']['ports']), 100)
        self.assertEqual(bitset['structure']['unattached_components'], (1 << 500) - 1)
        wire = json.loads(json.dumps(json_safe(bitset['certificate'])))
        with patch('fastunknot.normal_prism_interfaces._profiles', side_effect=AssertionError('producer used')):
            self.assertTrue(verify_normal_prism_interfaces(raw, rows, wire))

    def test_bit_weights_histogram_schema_and_membership_forgery_rejected(self):
        raw, rows = layered_torus(8)
        proof = normal_prism_face_regions(raw, rows, port_encoding='bitset', record_certificate=True)['certificate']
        mutations = []
        wrong = deepcopy(proof)
        wrong['schema'] = 'normal-prism-interfaces-v1'
        mutations.append(wrong)
        for value in (-1, True, 1 << len(proof['structure']['ports'])):
            wrong = deepcopy(proof)
            wrong['weighted_certificate']['histogram'][0]['weight'][2] = value
            mutations.append(wrong)
        wrong = deepcopy(proof)
        marked = next(row for row in wrong['weighted_certificate']['weights'] if row[2][2])
        marked[2][2] *= 2
        mutations.append(wrong)
        wrong = deepcopy(proof)
        wrong['structure']['attached_regions'][0]['ports'].append(0)
        mutations.append(wrong)
        for wrong in mutations:
            self.assertFalse(verify_normal_prism_interfaces(raw, rows, wrong))

    def test_invalid_encoding_caps_and_callback_propagation(self):
        raw, rows = layered_torus(4)
        with self.assertRaises(ValueError):
            normal_prism_face_regions(raw, rows, port_encoding='hash')
        result = normal_prism_face_regions(raw, rows, port_encoding='bitset', max_cycles=0, record_certificate=True)
        self.assertEqual(result['status'], 'INCONCLUSIVE')
        self.assertNotIn('structure', result)
        self.assertNotIn('certificate', result)
        class Stop(Exception):
            pass
        def cancel():
            raise Stop()
        with self.assertRaises(Stop):
            normal_prism_face_regions(raw, rows, port_encoding='bitset', check=cancel)


if __name__ == '__main__':
    unittest.main()
