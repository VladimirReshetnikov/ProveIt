"""Whole-cut trust-boundary checks on actual native normal surfaces."""

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


class NormalCutSaturationTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.bank = json.loads((ROOT / 'data/native_corpus.json').read_text())['cases']
        cls.case = cls.bank[4]  # A saturated Mobius bundle in a genuine cut.
        cls.answer = normal_cut_saturation(
            cls.case['triangulation'], cls.case['coordinates'], record_certificate=True)
        cls.proof = cls.answer['certificate']

    def verify(self, proof, case=None, **kwargs):
        case = self.case if case is None else case
        return verify_normal_cut_saturation(
            case['triangulation'], case['coordinates'], proof, **kwargs)

    def test_new_native_success_and_json_round_trip(self):
        self.assertEqual(self.answer['status'], 'COMPLETE')
        self.assertTrue(self.verify(self.proof))
        self.assertTrue(self.verify(json.loads(json.dumps(json_safe(self.proof)))))
        self.assertEqual(self.answer['census']['histogram'],
                         [dict(genus=1, multiplicity=1), dict(genus=2, multiplicity=1)])

    def test_forged_source_or_conclusion_is_rejected(self):
        mutations = [
            lambda p: p.update(schema='forged'),
            lambda p: p.update(unchecked_note=True),
            lambda p: p['parallelity'].update(input_sha256='0' * 64),
            lambda p: p['parallelity']['summary'].update(core_euler_characteristic=True),
            lambda p: p['boundary']['skeleton']['attachment_components'][0]['word'].reverse(),
            lambda p: p['relative']['joined_components'][0].update(private_one_handles=100),
            lambda p: p['relative']['rows'][0].update(counts=[]),
            lambda p: p['peeling']['eliminations'].pop(),
            lambda p: p['conclusion']['census'].update(all_balls=True),
            lambda p: p['conclusion']['census']['histogram'][0].update(genus=0),
        ]
        for mutate in mutations:
            proof = deepcopy(self.proof)
            mutate(proof)
            self.assertFalse(self.verify(proof), mutate)

    def test_wrong_normal_surface_does_not_reuse_certificate(self):
        case = deepcopy(self.case)
        case['coordinates'] = [[2 * x for x in row] for row in case['coordinates']]
        self.assertFalse(self.verify(self.proof, case))

    def test_verifier_does_not_call_discovery_or_compilation_producers(self):
        forbidden = [
            ('normal_cut_saturation', 'normal_cut_saturation'),
            ('relative_bundles', 'compile_relative_bundles'),
            ('relative_bundles', 'census_after_complete_cancellation'),
            ('column_peeling', 'column_peeling_plan'),
            ('fastunknot.normal_parallelity', 'normal_cut_parallelity'),
            ('fastunknot.parallelity_boundary_words', 'normal_parallelity_boundary_words'),
        ]
        contexts = []
        try:
            for module, name in forbidden:
                context = patch.object(importlib.import_module(module), name,
                                       side_effect=AssertionError('producer called'))
                context.start()
                contexts.append(context)
            self.assertTrue(self.verify(self.proof))
        finally:
            for context in reversed(contexts):
                context.stop()

    def test_discovery_and_replay_operation_allowances(self):
        refused = normal_cut_saturation(self.case['triangulation'], self.case['coordinates'],
                                        max_cycles=0, record_certificate=True)
        self.assertEqual(refused['status'], 'INCONCLUSIVE')
        self.assertEqual(refused['reason'], 'parallelity_budget_exhausted')
        self.assertNotIn('certificate', refused)
        operations = _orbit_operations(self.proof['parallelity'], self.proof['boundary'])
        self.assertGreater(operations, 0)
        self.assertTrue(self.verify(self.proof, max_operations=operations))
        self.assertFalse(self.verify(self.proof, max_operations=operations - 1))
        for value in (True, -1, 0.5):
            with self.assertRaises(ValueError):
                self.verify(self.proof, max_operations=value)

    def test_callback_failure_preserves_type_after_entering_verifier(self):
        class Cancel:
            def __init__(self, exception):
                self.calls = 0
                self.exception = exception

            def __call__(self):
                self.calls += 1
                if self.calls == 40:
                    raise self.exception('stop replay')

        for exception in (ValueError, TypeError, RuntimeError):
            with self.assertRaisesRegex(exception, 'stop replay'):
                self.verify(self.proof, check=Cancel(exception))

    def test_raw_obstruction_authenticates_only_inconclusive_conclusion(self):
        case = self.bank[3]
        answer = normal_cut_saturation(case['triangulation'], case['coordinates'],
                                       record_certificate=True)
        self.assertEqual(answer['status'], 'INCONCLUSIVE')
        self.assertEqual(answer['reason'], 'full_raw_cancellation_obstructed')
        proof = answer['certificate']
        self.assertTrue(self.verify(proof, case))
        bad = deepcopy(proof)
        bad['conclusion'] = dict(status='COMPLETE', census=self.answer['census'])
        self.assertFalse(self.verify(bad, case))

    def test_binary_multiplicity_is_authenticated_without_expansion(self):
        case = self.bank[99]
        answer = normal_cut_saturation(case['triangulation'], case['coordinates'],
                                       record_certificate=True)
        self.assertEqual(answer['status'], 'COMPLETE')
        proof = json.loads(json.dumps(json_safe(answer['certificate'])))
        self.assertTrue(self.verify(proof, case))
        self.assertGreater(answer['census']['components'], 1 << 100)


if __name__ == '__main__':
    unittest.main()
