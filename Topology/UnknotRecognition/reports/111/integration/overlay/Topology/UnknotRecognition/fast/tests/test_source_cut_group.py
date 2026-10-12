"""Source-bound group compilation, independent replay and adversarial packets."""

from copy import deepcopy
import json
from pathlib import Path
import unittest
from unittest.mock import patch

from fastunknot.integer_codec import json_safe
from fastunknot.normal_parallelity import normal_cut_parallelity
from fastunknot.parallelity_boundary_words import normal_parallelity_boundary_words
from fastunknot.source_cut_group import compile_disk_cut_presentation
from fastunknot.source_cut_group_verify import verify_disk_cut_presentation
from normal_orbit_research.fixtures import layered_torus


FAST = Path(__file__).resolve().parents[1]


class SourceCutGroupTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.bank = {}
        for name in ('corpus.json', 'three_handle_corpus.json'):
            path = FAST/'marked_parallelity_research'/name
            cls.bank.update((c['id'], c) for c in json.loads(path.read_text())['cases'])
        cls.cache = {}

    @classmethod
    def source(cls, name):
        if name not in cls.cache:
            c = cls.bank[name]
            p = normal_cut_parallelity(c['triangulation'], c['coordinates'])
            b = normal_parallelity_boundary_words(c['triangulation'], c['coordinates'])
            if p['status'] != 'COMPLETE' or b['status'] != 'COMPLETE':
                raise AssertionError('unbounded source compiler unexpectedly refused')
            g, summary, skeleton = p['geometry'], p['summary'], b['skeleton']
            proof = compile_disk_cut_presentation(g, summary, skeleton)
            cls.cache[name] = g, summary, skeleton, proof
        return cls.cache[name]

    def test_native_figure_eight_exact_signed_words(self):
        g, summary, skeleton, proof = self.source('pilot/finite_figureEight/0')
        self.assertTrue(verify_disk_cut_presentation(g, summary, skeleton, proof))
        self.assertEqual(proof['stats']['generators'], 25)
        self.assertEqual(proof['stats']['relators'], 22)
        self.assertEqual(proof['stats']['word_length'], 53)
        self.assertEqual(proof['source_euler_characteristic'], -1)
        first = proof['components'][0]
        self.assertEqual(first['generators'], [33, 41, 45, 49, 57, 61, 65])
        self.assertEqual(first['relators'][0]['word'], [65, 45, -61, -41, -61, -49])
        self.assertEqual([r['source_kind'] for r in first['relators']],
                         ['disk_annulus'] * 5)

    def test_interval_attachment_cycles_supply_free_generators(self):
        g, summary, skeleton, proof = self.source('lst_3_7/mixed')
        self.assertTrue(verify_disk_cut_presentation(g, summary, skeleton, proof))
        self.assertEqual(proof['stats']['interval_attachments'], 8)
        self.assertEqual(proof['stats']['stable_generators'], 3)
        self.assertEqual(sum(p['attachment_cycle_rank'] for p in proof['components']), 3)
        stable = {x for p in proof['components'] for x in p['generators']
                  if x > len(g['core']['handles1'])}
        self.assertEqual(len(stable), 3)
        self.assertTrue(all(abs(x) not in stable for p in proof['components']
                            for r in p['relators'] for x in r['word']))

    def test_original_three_handles_remain_in_euler_ledger(self):
        g, summary, skeleton, proof = self.source('interior_loop/empty')
        self.assertEqual(len(g['core']['handles3']), 1)
        self.assertTrue(verify_disk_cut_presentation(g, summary, skeleton, proof))
        stats = proof['stats']
        chi = (len(proof['components']) + proof['isolated_ball_count']
               - stats['generators'] + stats['relators'] - stats['core_three_handles'])
        self.assertEqual(chi, proof['source_euler_characteristic'])

    def test_binary_isolated_disks_are_not_expanded(self):
        raw, primitive = layered_torus(1)
        multiple = 1 << 4097
        coordinates = [[multiple * x for x in row] for row in primitive]
        p = normal_cut_parallelity(raw, coordinates)
        b = normal_parallelity_boundary_words(raw, coordinates)
        proof = compile_disk_cut_presentation(p['geometry'], p['summary'], b['skeleton'])
        self.assertEqual(proof['isolated_ball_count'], multiple - 1)
        self.assertLess(proof['stats']['generators'], 100)
        self.assertLess(proof['stats']['word_length'], 100)
        safe = json_safe(proof)
        self.assertIsInstance(safe['isolated_ball_count'], str)
        self.assertTrue(verify_disk_cut_presentation(p['geometry'], p['summary'], b['skeleton'], safe))

    def test_nondisk_base_is_a_supported_contract_refusal(self):
        g, summary, skeleton, proof = self.source('pilot/fibonacci_lst_04/0')
        self.assertIsNone(proof)
        self.assertFalse(verify_disk_cut_presentation(g, summary, skeleton, {}))

    def test_independent_replay_does_not_call_any_producer(self):
        g, summary, skeleton, proof = self.source('pilot/finite_figureEight/0')
        with patch('fastunknot.source_cut_group.compile_disk_cut_presentation',
                   side_effect=AssertionError('compiler must not be called')), \
             patch('fastunknot.source_cut_group._annular_word',
                   side_effect=AssertionError('producer chart reader must not be called')), \
             patch('fastunknot.source_cut_group._original_word',
                   side_effect=AssertionError('producer chart reader must not be called')):
            self.assertTrue(verify_disk_cut_presentation(g, summary, skeleton, proof))

    def test_changed_original_or_annular_sign_is_rejected(self):
        g, summary, skeleton, proof = self.source('pilot/finite_figureEight/0')
        for part in (0, 1):
            bad = deepcopy(proof)
            bad['components'][part]['relators'][0]['word'][0] *= -1
            self.assertFalse(verify_disk_cut_presentation(g, summary, skeleton, bad))

    def test_component_reassignment_and_missing_relator_are_rejected(self):
        g, summary, skeleton, proof = self.source('pilot/finite_figureEight/0')
        bad = deepcopy(proof)
        bad['components'][0]['relators'].append(bad['components'][1]['relators'].pop())
        self.assertFalse(verify_disk_cut_presentation(g, summary, skeleton, bad))
        bad = deepcopy(proof)
        bad['components'][0]['relators'].pop()
        self.assertFalse(verify_disk_cut_presentation(g, summary, skeleton, bad))

    def test_invalid_core_and_bridge_forests_are_rejected(self):
        for case, key in [('pilot/finite_figureEight/0', 'core_forest'),
                          ('lst_3_7/mixed', 'bridge_forest')]:
            g, summary, skeleton, proof = self.source(case)
            bad = deepcopy(proof)
            bad[key].pop()
            self.assertFalse(verify_disk_cut_presentation(g, summary, skeleton, bad))
            bad = deepcopy(proof)
            bad[key].append(bad[key][0])
            self.assertFalse(verify_disk_cut_presentation(g, summary, skeleton, bad))

    def test_forged_metadata_extra_fields_and_boolean_labels_are_rejected(self):
        g, summary, skeleton, proof = self.source('pilot/finite_figureEight/0')
        for key in ('source_euler_characteristic', 'isolated_ball_count'):
            bad = deepcopy(proof)
            bad[key] += 1
            self.assertFalse(verify_disk_cut_presentation(g, summary, skeleton, bad))
        bad = deepcopy(proof)
        bad['trusted'] = True
        self.assertFalse(verify_disk_cut_presentation(g, summary, skeleton, bad))
        bad = deepcopy(proof)
        bad['components'][0]['generators'][0] = True
        self.assertFalse(verify_disk_cut_presentation(g, summary, skeleton, bad))

    def test_malformed_source_face_and_annular_port_are_rejected(self):
        g, summary, skeleton, proof = self.source('pilot/finite_figureEight/0')
        damaged = deepcopy(g)
        damaged['core']['handles2'][0]['cycle'][1]['face'] = 5
        self.assertFalse(verify_disk_cut_presentation(damaged, summary, skeleton, proof))
        changed = deepcopy(skeleton)
        word = changed['attachment_components'][0]['word']
        position = next(i for i, letter in enumerate(word)
                        if g['ports'][abs(letter) - 1]['core_dimension'] == 1
                        and g['ports'][abs(letter) - 1]['core_handle'] not in proof['core_forest'])
        word[position] *= -1
        self.assertFalse(verify_disk_cut_presentation(g, summary, changed, proof))

    def test_source_euler_identity_is_checked(self):
        g, summary, skeleton, proof = self.source('pilot/finite_figureEight/0')
        broken = deepcopy(summary)
        broken['attachment_euler_characteristic'] += 1
        with self.assertRaises(ValueError):
            compile_disk_cut_presentation(g, broken, skeleton)
        self.assertFalse(verify_disk_cut_presentation(g, broken, skeleton, proof))

    def test_callbacks_propagate_inside_replay_including_value_error(self):
        g, summary, skeleton, proof = self.source('pilot/finite_figureEight/0')
        for error in (RuntimeError, ValueError, KeyError):
            for operation in ('compile', 'verify'):
                ticks = 0

                def stop():
                    nonlocal ticks
                    ticks += 1
                    if ticks == 7:
                        raise error('stop after source replay has started')

                with self.assertRaises(error):
                    if operation == 'compile':
                        compile_disk_cut_presentation(g, summary, skeleton, check=stop)
                    else:
                        verify_disk_cut_presentation(g, summary, skeleton, proof, check=stop)


if __name__ == '__main__':
    unittest.main()
