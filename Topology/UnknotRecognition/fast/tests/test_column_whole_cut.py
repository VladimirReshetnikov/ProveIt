"""Column replay and the source stopping-set filter in the whole-cut operator."""
from copy import deepcopy
import json
from pathlib import Path
import unittest
from unittest.mock import patch

from fastunknot.core_handlebody import core_handlebody_certificate
from fastunknot.normal_cut_handlebodies import normal_cut_handlebodies
from fastunknot.normal_cut_handlebodies_verify import verify_normal_cut_handlebodies
from tests.test_core_handlebody import source_core


class ColumnWholeCutTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.bank = json.loads((Path(__file__).parents[1]/'marked_parallelity_research/corpus.json').read_text())['cases']
        cls.case = next(c for c in cls.bank if c['id']=='fibonacci_lst_09/mixed')
        cls.result = normal_cut_handlebodies(cls.case['triangulation'], cls.case['coordinates'], record_certificate=True)

    def test_kernel_timestamp_and_legacy_dense_replay(self):
        c, result = self.case, self.result
        proof = deepcopy(result['certificate'])
        self.assertEqual(proof['kernel']['schema'], 'bundle-boundary-kernel-v2')
        names = ('fastunknot.bundle_boundary_kernel.column_cancellation_plan',
                 'fastunknot.core_handlebody.column_cancellation_plan')
        with patch(names[0], side_effect=AssertionError('producer called')), patch(names[1], side_effect=AssertionError('producer called')):
            self.assertTrue(verify_normal_cut_handlebodies(c['triangulation'], c['coordinates'], proof))
        proof['kernel']['schema'] = 'bundle-boundary-kernel-v1'
        with patch('fastunknot.bundle_boundary_kernel_verify.verify_column_cancellations', side_effect=AssertionError('legacy path used timestamps')):
            self.assertTrue(verify_normal_cut_handlebodies(c['triangulation'], c['coordinates'], proof))

    def test_source_obstruction_skips_boundary_discovery(self):
        c = next(c for c in self.bank if c['id']=='pilot/fibonacci_lst_04/0')
        core = source_core(c['triangulation'], c['coordinates'])
        self.assertEqual(core_handlebody_certificate(core)['status'], 'INCONCLUSIVE')
        name = 'fastunknot.normal_cut_handlebodies.normal_parallelity_boundary_words'
        with patch(name, side_effect=RuntimeError('boundary requested')):
            a = normal_cut_handlebodies(c['triangulation'], c['coordinates'], record_certificate=True,
                                       lower_forest='source')
            self.assertEqual(a['status'], 'INCONCLUSIVE')
            self.assertNotIn('boundary', a['stats'])
            self.assertNotIn('certificate', a)
            with self.assertRaisesRegex(RuntimeError, 'boundary requested'):
                normal_cut_handlebodies(c['triangulation'], c['coordinates'], precheck_core=False)

    def test_precheck_preserves_positive_certificate_and_caps(self):
        c = self.case
        a = normal_cut_handlebodies(c['triangulation'], c['coordinates'], record_certificate=True, precheck_core=False)
        self.assertEqual(a['certificate'], self.result['certificate'])
        self.assertEqual(a['census'], self.result['census'])
        for value in (0, 1, None, 'yes'):
            with self.assertRaises(ValueError):
                normal_cut_handlebodies(c['triangulation'], c['coordinates'], precheck_core=value)
        self.assertEqual(normal_cut_handlebodies(c['triangulation'], c['coordinates'], max_cycles=0)['status'], 'INCONCLUSIVE')


if __name__ == '__main__':
    unittest.main()
