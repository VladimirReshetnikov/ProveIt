"""Source-chart absorption, self-pairings, independent replay and hostile proofs."""

from contextlib import ExitStack
from copy import deepcopy
import json
from pathlib import Path
import random
import unittest
from unittest.mock import patch

from fastunknot.disk_bundle_absorption_verify import replay_disk_bundle_absorption
from fastunknot.integer_codec import json_safe
from fastunknot.normal_cut_handlebodies import normal_cut_handlebodies
from fastunknot.normal_cut_handlebodies_verify import verify_normal_cut_handlebodies
from tests.test_normal_surface_orbits import relabel


class DiskBundleAbsorptionTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        bank = json.loads((Path(__file__).parents[1] /
                           'marked_parallelity_research/corpus.json').read_text())['cases']
        cls.bank = bank
        cls.case = next(c for c in bank if c['id'] == 'pilot/fibonacci_lst_02/0')
        cls.raw, cls.rows = cls.case['triangulation'], cls.case['coordinates']
        cls.result = normal_cut_handlebodies(cls.raw, cls.rows, record_certificate=True)

    def test_full_annulus_becomes_a_source_two_handle(self):
        a = self.result
        self.assertEqual(a['status'], 'COMPLETE')
        self.assertEqual(a['census']['histogram'], [dict(genus=1, multiplicity=2)])
        proof = a['certificate']
        self.assertEqual(proof['schema'], 'normal-cut-handlebodies-v2')
        self.assertTrue(verify_normal_cut_handlebodies(self.raw, self.rows, proof))
        crossings = proof['absorption']['components'][0]['crossings']
        self.assertEqual(len(crossings), 4)
        self.assertEqual(sum(c['handle'] == 8 for c in crossings), 2)
        self.assertEqual({c['sign'] for c in crossings}, {-1, 1})
        # These two occurrences traverse the SAME zero-handle and tetrahedron
        # at both ends. Distinct face flags still recover the crossing sign.
        g = proof['parallelity']['geometry']
        h = g['core']['handles1'][8]
        self.assertEqual(h['ends'][0], h['ends'][1])
        self.assertEqual(h['tetrahedron'], h['target_tetrahedron'])
        self.assertNotEqual(h['face'], h['target_face'])

    def test_relabelled_self_pairings_preserve_census(self):
        rng = random.Random(852026)
        for _ in range(12):
            raw, rows = relabel(self.raw, self.rows, rng)
            a = normal_cut_handlebodies(raw, rows, record_certificate=True)
            self.assertEqual(a['status'], 'COMPLETE')
            self.assertEqual(a['census']['histogram'], self.result['census']['histogram'])
            self.assertTrue(verify_normal_cut_handlebodies(raw, rows, a['certificate']))
    def test_nondisk_annuli_and_stalled_augmented_cores_remain_unresolved(self):
        for name, reason in [('pilot/fibonacci_lst_04/0', 'raw_cancellation_stalled')]:
            c = next(c for c in self.bank if c['id'] == name)
            a = normal_cut_handlebodies(c['triangulation'], c['coordinates'],
                                       record_certificate=True, lower_forest='source')
            self.assertEqual(a['status'], 'INCONCLUSIVE')
            self.assertEqual(a['reason'], reason)
            self.assertNotIn('certificate', a)

    def test_replay_does_not_call_producers(self):
        names = (
            'fastunknot.disk_bundle_absorption.absorb_disk_bundles',
            'fastunknot.normal_cut_handlebodies.absorb_disk_bundles',
            'fastunknot.normal_cut_handlebodies.normal_cut_handlebodies',
            'fastunknot.normal_cut_handlebodies._census',
            'fastunknot.core_handlebody.core_handlebody_certificate',
        )
        with ExitStack() as stack:
            for name in names:
                stack.enter_context(patch(name, side_effect=AssertionError('producer used')))
            self.assertTrue(verify_normal_cut_handlebodies(
                self.raw, self.rows, self.result['certificate']))

    def test_forged_absorption_and_omitted_two_handles_are_rejected(self):
        original = self.result['certificate']
        mutations = [
            lambda p: p.pop('absorption'),
            lambda p: p.update(schema='normal-cut-handlebodies-v1'),
            lambda p: p['absorption']['components'].clear(),
            lambda p: p['absorption']['components'][0].update(base_profile=1),
            lambda p: p['absorption']['components'][0].update(two_handle=0),
            lambda p: p['absorption']['components'][0]['crossings'][0].update(sign=-1),
            lambda p: p['absorption']['components'][0]['crossings'][0].update(start=0),
            lambda p: p['absorption']['components'][0]['crossings'].pop(),
            lambda p: p['absorption']['components'][0]['crossings'][0].update(handle=True),
            lambda p: p['core']['cancellations'].pop(),
        ]
        for change in mutations:
            with self.subTest(change=change):
                proof = deepcopy(original)
                change(proof)
                self.assertFalse(verify_normal_cut_handlebodies(self.raw, self.rows, proof))

    def test_face_flag_corruption_fails_low_level_reconstruction(self):
        proof = self.result['certificate']
        g = deepcopy(proof['parallelity']['geometry'])
        component = proof['absorption']['components'][0]
        port = g['ports'][component['crossings'][1]['port']]
        poly = g['polygons'][port['polygon']]
        poly['vertices'][port['edge']]['face'] = 99
        self.assertIsNone(replay_disk_bundle_absorption(g, proof['parallelity']['summary'],
            proof['boundary']['skeleton'], proof['absorption']))

    def test_exact_hexadecimal_absorption_transport_and_caps(self):
        proof = deepcopy(self.result['certificate'])
        record = proof['absorption']['components'][0]
        record['two_handle'] = hex(record['two_handle'])
        record['crossings'][0]['sign'] = '+0X1'
        self.assertTrue(verify_normal_cut_handlebodies(self.raw, self.rows, proof))
        self.assertFalse(verify_normal_cut_handlebodies(self.raw, self.rows, proof, max_operations=0))
        self.assertEqual(normal_cut_handlebodies(self.raw, self.rows, max_cycles=0)['status'],
                         'INCONCLUSIVE')

    def test_binary_multiple_preserves_exact_component_multiplicity(self):
        for n in (2, 5, 1 << 1024):
            rows = [[n * x for x in row] for row in self.rows]
            a = normal_cut_handlebodies(self.raw, rows, record_certificate=True)
            self.assertEqual(a['status'], 'COMPLETE')
            self.assertEqual(a['census']['histogram'], [dict(genus=1, multiplicity=n + 1)])
            proof = json.loads(json.dumps(json_safe(a['certificate'])))
            self.assertTrue(verify_normal_cut_handlebodies(self.raw, json_safe(rows), proof))


if __name__ == '__main__':
    unittest.main()
