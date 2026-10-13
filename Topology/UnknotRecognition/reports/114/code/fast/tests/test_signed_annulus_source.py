"""Source-sign and independent replay tests; these are not knot verdicts."""

from copy import deepcopy
import json
from pathlib import Path
import unittest

from fastunknot.core_handlebody import core_handlebody_certificate
from fastunknot.disk_bundle_absorption import absorb_disk_bundles
from fastunknot.normal_parallelity import normal_cut_parallelity
from fastunknot.parallelity_boundary_moments import _compile
from fastunknot.signed_annulus_source import signed_annulus_source
from fastunknot.signed_annulus_source_verify import verify_signed_annulus_source


def native_parts(name):
    path = Path(__file__).resolve().parents[1] / 'marked_parallelity_research/corpus.json'
    case = next(c for c in json.loads(path.read_text())['cases'] if c['id'] == name)
    parallelity = normal_cut_parallelity(case['triangulation'], case['coordinates'],
                                         record_certificate=True)
    geometry, summary = parallelity['geometry'], parallelity['summary']
    boundary = _compile(geometry, parallelity['certificate']['input_sha256'],
                        None, True, lambda: None, 'pair')['skeleton']
    deferred = {i for i, p in enumerate(summary['base_profiles'])
                if (p['euler_characteristic'], p['boundary_components']) != (1, 1)}
    augmented, _, _ = absorb_disk_bundles(geometry, summary, boundary,
                                         primitive_bases=deferred)
    core = core_handlebody_certificate(augmented)
    if core['status'] != 'COMPLETE':
        raise AssertionError('fixture has no authenticated complete core')
    return geometry, summary, boundary, augmented, core['certificate']


class SignedAnnulusSourceTests(unittest.TestCase):
    def test_native_annulus_source_word(self):
        parts = native_parts('pilot/fibonacci_lst_05/0')
        packet = signed_annulus_source(*parts)
        self.assertEqual(packet['method'], 'column_leaf')
        self.assertEqual(len(packet['passive']), 1)
        self.assertEqual(packet['passive'][0]['word'], [-13, -13, 5])
        self.assertTrue(verify_signed_annulus_source(*parts, packet))

    def test_native_disk_absorption_and_leaf_source(self):
        parts = native_parts('fibonacci_lst_05/mixed')
        packet = signed_annulus_source(*parts)
        self.assertEqual(packet['method'], 'leaf')
        self.assertEqual(len(packet['passive']), 2)
        self.assertGreater(len(packet['active']), len(parts[0]['core']['handles2']))
        self.assertTrue(verify_signed_annulus_source(*parts, packet))

    def test_native_multiple_base_components(self):
        parts = native_parts('fibonacci_lst_09/mixed')
        packet = signed_annulus_source(*parts)
        self.assertEqual(len(packet['passive']), 6)
        self.assertEqual(len({r['base_profile'] for r in packet['passive']}), 2)
        self.assertTrue(verify_signed_annulus_source(*parts, packet))

    def test_self_loop_uses_face_flags_and_keeps_inverse_neighbors(self):
        # A conditional handle-chart fixture isolates the orientation issue:
        # both endpoint vertices agree, while the two face flags differ.
        core = dict(handles0=[dict(id=0)], handles1=[
            dict(id=0, ends=[0, 0], tetrahedron=0, face=0,
                 target_tetrahedron=0, target_face=1),
            dict(id=1, ends=[0, 0], tetrahedron=0, face=2,
                 target_tetrahedron=0, target_face=3)], handles2=[
            dict(id=0, cycle=[
                dict(dimension=0, handle=0),
                dict(dimension=1, handle=0, tetrahedron=0, face=0),
                dict(dimension=0, handle=0),
                dict(dimension=1, handle=0, tetrahedron=0, face=1),
                dict(dimension=0, handle=0),
                dict(dimension=1, handle=1, tetrahedron=0, face=2)])], handles3=[])
        proof = core_handlebody_certificate(core)['certificate']
        parts = (dict(core=core, ports=[]), dict(base_profiles=[]),
                 dict(attachment_components=[]), core, proof)
        packet = signed_annulus_source(*parts)
        self.assertEqual(packet['active'][0]['word'], [1, -1, 2])
        self.assertEqual(packet['cancellations'], [[0, 2]])
        self.assertTrue(verify_signed_annulus_source(*parts, packet))
        corrupted = deepcopy(packet)
        corrupted['active'][0]['word'][1] = 1
        self.assertFalse(verify_signed_annulus_source(*parts, corrupted))

    def test_source_packet_mutations_are_rejected(self):
        parts = native_parts('pilot/fibonacci_lst_05/0')
        packet = signed_annulus_source(*parts)
        changes = [
            lambda p: p['passive'][0]['word'].__setitem__(0, 13),
            lambda p: p['passive'][0].__setitem__('core_component', -1),
            lambda p: p['passive'][0].__setitem__('base_profile', -1),
            lambda p: p['components'][0]['generators'].append(999),
            lambda p: p.__setitem__('method', 'capped'),
            lambda p: p.__setitem__('untrusted_extra', True),
            lambda p: p['passive'][0]['word'].__setitem__(0, True),
        ]
        for change in changes:
            mutated = deepcopy(packet)
            change(mutated)
            self.assertFalse(verify_signed_annulus_source(*parts, mutated))

    def test_absorbed_disk_cycle_corruption_is_rejected(self):
        parts = list(native_parts('fibonacci_lst_05/mixed'))
        packet = signed_annulus_source(*parts)
        parts[3] = deepcopy(parts[3])
        parts[3]['handles2'][-1]['cycle'][0]['handle'] += 1
        self.assertIsNone(signed_annulus_source(*parts))
        self.assertFalse(verify_signed_annulus_source(*parts, packet))

    def test_legacy_capped_proof_is_unsupported(self):
        parts = list(native_parts('pilot/fibonacci_lst_05/0'))
        packet = signed_annulus_source(*parts)
        parts[4] = dict(parts[4], schema='normal-core-handlebody-v1', method='capped')
        self.assertIsNone(signed_annulus_source(*parts))
        self.assertFalse(verify_signed_annulus_source(*parts, packet))


if __name__ == '__main__':
    unittest.main()
