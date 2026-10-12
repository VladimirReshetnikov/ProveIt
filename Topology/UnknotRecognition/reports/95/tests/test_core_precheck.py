"""Optional early-core filtering on authenticated native normal cuts."""

from collections import Counter
from copy import deepcopy
import importlib
import json
from pathlib import Path
import unittest
from unittest.mock import patch

from fastunknot.integer_codec import json_safe
from normal_cut_saturation import normal_cut_saturation
from normal_cut_saturation_verify import verify_normal_cut_saturation, _orbit_operations


ROOT = Path(__file__).resolve().parents[1]


class CorePrecheckTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.bank = json.loads((ROOT / 'data/native_corpus.json').read_text())['cases']
        cls.case = cls.bank[3]
        cls.answer = normal_cut_saturation(
            cls.case['triangulation'], cls.case['coordinates'],
            precheck_core=True, record_certificate=True)
        cls.proof = cls.answer['certificate']

    def verify(self, proof, case=None, **kwargs):
        case = self.case if case is None else case
        return verify_normal_cut_saturation(
            case['triangulation'], case['coordinates'], proof, **kwargs)

    def test_all_106_native_cases_preserve_topology_status_and_census(self):
        counts, records = Counter(), []
        for case in self.bank:
            raw, rows = case['triangulation'], case['coordinates']
            old = normal_cut_saturation(raw, rows, record_certificate=True)
            new = normal_cut_saturation(raw, rows, precheck_core=True,
                                        record_certificate=True)
            self.assertEqual(new['status'], old['status'], case['id'])
            counts[new['status']] += 1
            if new['status'] == 'COMPLETE':
                self.assertEqual(new['census'], old['census'], case['id'])
                self.assertEqual(new['certificate'], old['certificate'], case['id'])
                counts['identical_success_certificates'] += 1
            elif new.get('reason') != 'original_core_raw_obstruction':
                self.assertEqual(new.get('reason'), old.get('reason'), case['id'])
            if 'certificate' in new:
                self.assertTrue(verify_normal_cut_saturation(raw, rows, new['certificate']),
                                case['id'])
                counts['independent_replays'] += 1
            early = new.get('reason') == 'original_core_raw_obstruction'
            saved = new['stats'].get('avoided_boundary_queries', 0)
            if early:
                self.assertEqual(old['reason'], 'full_raw_cancellation_obstructed')
                self.assertEqual(new['certificate']['schema'], 'normal-cut-core-obstruction-v1')
                self.assertNotIn('boundary', new['certificate'])
                self.assertNotIn('boundary', new['stats'])
                self.assertEqual(saved, len(old['stats']['boundary']))
                self.assertIn(saved, (0, 2))
                counts['early_core_obstructions'] += 1
                counts['avoided_boundary_queries'] += saved
                counts['query_saving_cases' if saved else 'zero_port_early_proofs'] += 1
                self.assertEqual(
                    new['certificate']['parallelity'], old['certificate']['parallelity'])
            records.append(dict(id=case['id'], status=new['status'],
                                baseline_reason=old.get('reason'), reason=new.get('reason'),
                                avoided_boundary_queries=saved,
                                same_complete_census=(new['census'] == old['census']
                                                      if new['status'] == 'COMPLETE' else None)))
        self.assertEqual(len(self.bank), 106)
        self.assertEqual(counts['early_core_obstructions'], 6)
        self.assertEqual(counts['query_saving_cases'], 5)
        self.assertEqual(counts['zero_port_early_proofs'], 1)
        self.assertEqual(counts['avoided_boundary_queries'], 10)
        output = ROOT / 'data' / 'core_precheck_audit.json'
        output.write_text(json.dumps(dict(
            source_revision='704600626606a9097cfd89d4e3d2bbc63c8dd1cb',
            scope='optional precheck on versus off; no timing claim',
            cases_checked=len(self.bank), counts=counts, cases=records), indent=2) + '\n')

    def test_early_certificate_and_json_round_trip(self):
        self.assertEqual(self.answer['status'], 'INCONCLUSIVE')
        self.assertEqual(self.answer['reason'], 'original_core_raw_obstruction')
        self.assertEqual(self.proof['schema'], 'normal-cut-core-obstruction-v1')
        self.assertTrue(self.verify(self.proof))
        self.assertTrue(self.verify(json.loads(json.dumps(json_safe(self.proof)))))
        self.assertTrue(self.proof['peeling']['residual_rows'])
        output = ROOT / 'data' / 'certificates' / 'precheck_003_original_core.json'
        output.parent.mkdir(exist_ok=True)
        payload = dict(id=self.case['id'], triangulation=self.case['triangulation'],
                       coordinates=self.case['coordinates'], certificate=self.proof)
        output.write_text(json.dumps(json_safe(payload), indent=2) + '\n')

    def test_no_ordered_boundary_call_on_early_exit(self):
        with patch('normal_cut_saturation.normal_parallelity_boundary_words',
                   side_effect=AssertionError('ordered boundary was called')):
            answer = normal_cut_saturation(
                self.case['triangulation'], self.case['coordinates'], precheck_core=True,
                record_certificate=True)
        self.assertEqual(answer['certificate'], self.proof)
        plain = normal_cut_saturation(
            self.case['triangulation'], self.case['coordinates'], precheck_core=True)
        self.assertEqual(plain['reason'], 'original_core_raw_obstruction')
        self.assertNotIn('certificate', plain)

    def test_independent_early_replay_calls_no_producer_or_boundary_replay(self):
        forbidden = [
            ('normal_cut_saturation', '_original_core_model'),
            ('normal_cut_saturation', 'normal_cut_saturation'),
            ('normal_cut_saturation', 'column_peeling_plan'),
            ('column_peeling', 'column_peeling_plan'),
            ('relative_bundles', 'compile_relative_bundles'),
            ('fastunknot.normal_parallelity', 'normal_cut_parallelity'),
            ('normal_cut_saturation_verify', 'verify_parallelity_boundary_words'),
            ('normal_cut_saturation_verify', 'replay_relative_bundle_compilation'),
        ]
        contexts = []
        try:
            for module, name in forbidden:
                context = patch.object(importlib.import_module(module), name,
                                       side_effect=AssertionError('forbidden producer called'))
                context.start(); contexts.append(context)
            self.assertTrue(self.verify(self.proof))
        finally:
            for context in reversed(contexts):
                context.stop()

    def test_forged_core_source_matrix_peeling_and_conclusion_are_rejected(self):
        mutations = [
            lambda p: p.update(schema='forged'),
            lambda p: p.update(boundary={}),
            lambda p: p['parallelity'].update(input_sha256='0' * 64),
            lambda p: p['parallelity']['geometry']['core']['handles1'][0]['ends'].__setitem__(0, 999),
            lambda p: p['core']['forest'].append(0),
            lambda p: p['core']['rows'][0].update(counts=[[999, 1]]),
            lambda p: p['peeling'].update(residual_rows=[]),
            lambda p: p['peeling']['residual_rows'].__setitem__(0, True),
            lambda p: p['conclusion'].update(reason='full_raw_cancellation_obstructed'),
            lambda p: p['conclusion'].update(status='COMPLETE'),
            lambda p: p['conclusion'].update(remaining_two_handles=[]),
        ]
        for mutate in mutations:
            proof = deepcopy(self.proof)
            mutate(proof)
            self.assertFalse(self.verify(proof), mutate)
        wrong_source = deepcopy(self.case)
        wrong_source['coordinates'] = [[2 * x for x in row]
                                       for row in wrong_source['coordinates']]
        self.assertFalse(self.verify(self.proof, wrong_source))

    def test_four_trace_operation_and_discovery_cycle_caps(self):
        operations = _orbit_operations(self.proof['parallelity'])
        self.assertGreater(operations, 0)
        self.assertTrue(self.verify(self.proof, max_operations=operations))
        self.assertFalse(self.verify(self.proof, max_operations=operations - 1))
        cycles = sum(stats['orbit_cycles']
                     for stats in self.answer['stats']['parallelity'].values())
        early = normal_cut_saturation(
            self.case['triangulation'], self.case['coordinates'], max_cycles=cycles,
            precheck_core=True, record_certificate=True)
        self.assertEqual(early['reason'], 'original_core_raw_obstruction')
        self.assertTrue(self.verify(early['certificate']))
        ordinary = normal_cut_saturation(
            self.case['triangulation'], self.case['coordinates'], max_cycles=cycles,
            precheck_core=False, record_certificate=True)
        self.assertEqual(ordinary['reason'], 'boundary_budget_exhausted')
        refused = normal_cut_saturation(
            self.case['triangulation'], self.case['coordinates'], max_cycles=0,
            precheck_core=True, record_certificate=True)
        self.assertEqual(refused['reason'], 'parallelity_budget_exhausted')
        self.assertNotIn('certificate', refused)
        for bad in (True, -1, 0.5):
            with self.assertRaises(ValueError):
                self.verify(self.proof, max_operations=bad)
        for bad in (0, 1, None, 'yes'):
            with self.assertRaises(ValueError):
                normal_cut_saturation(self.case['triangulation'], self.case['coordinates'],
                                      precheck_core=bad)

    def test_callback_errors_keep_their_original_type(self):
        class StopAt:
            def __init__(self, exception, count):
                self.exception, self.count = exception, count

            def __call__(self):
                self.count -= 1
                if not self.count:
                    raise self.exception('early-core stop')

        for exception in (ValueError, TypeError, RuntimeError):
            with self.assertRaisesRegex(exception, 'early-core stop'):
                self.verify(self.proof, check=StopAt(exception, 40))
            with self.assertRaisesRegex(exception, 'early-core stop'):
                normal_cut_saturation(
                    self.case['triangulation'], self.case['coordinates'], precheck_core=True,
                    check=StopAt(exception, 40))


if __name__ == '__main__':
    unittest.main()
