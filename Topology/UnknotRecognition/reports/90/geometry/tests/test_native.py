from copy import deepcopy
import importlib.util
import json
from pathlib import Path
import unittest
from unittest.mock import patch

from unsaturated_bundles.native import (
    normal_cut_unsaturated_handlebodies, verify_normal_cut_unsaturated_handlebodies)


@unittest.skipUnless(importlib.util.find_spec('fastunknot'), 'optional pinned native runtime')
class NativeTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.saved = json.loads((Path(__file__).resolve().parents[1] / 'evidence' /
            'pilot_lst_5_7_0_certificate.json').read_text())
        cls.source = cls.saved['source']

    def test_newly_covered_source_and_independent_replay(self):
        from fastunknot.normal_cut_handlebodies import normal_cut_handlebodies
        raw, rows = self.source['triangulation'], self.source['coordinates']
        old = normal_cut_handlebodies(raw, rows)
        self.assertEqual(old.get('reason'), 'annular_core_attachment')
        new = normal_cut_unsaturated_handlebodies(raw, rows, record_certificate=True)
        self.assertEqual(new['status'], 'COMPLETE')
        self.assertEqual(new['census']['histogram'],
                         [dict(genus=1, multiplicity=1), dict(genus=2, multiplicity=1)])
        with patch('unsaturated_bundles.native.make_certificate', side_effect=AssertionError), \
             patch('fastunknot.normal_parallelity.normal_cut_parallelity', side_effect=AssertionError), \
             patch('fastunknot.core_handlebody.core_handlebody_certificate', side_effect=AssertionError):
            self.assertTrue(verify_normal_cut_unsaturated_handlebodies(raw, rows, new['certificate']))

    def test_source_and_interface_mutations_rejected(self):
        raw, rows = self.source['triangulation'], self.source['coordinates']
        for field in ('census', 'owner', 'boundary', 'coordinates'):
            proof, changed_rows = deepcopy(self.saved['certificate']), deepcopy(rows)
            if field == 'census':
                proof['reduction']['census']['histogram'][0]['genus'] += 1
            elif field == 'owner':
                proof['boundary']['skeleton']['ports'][0]['core_handle'] += 1
            elif field == 'boundary':
                proof['parallelity']['summary']['base_profiles'][0]['boundary_components'] += 1
            else:
                changed_rows[0][0] += 1
            self.assertFalse(verify_normal_cut_unsaturated_handlebodies(raw, changed_rows, proof))

    def test_budget_and_invalid_schema_never_mean_negative(self):
        raw, rows = self.source['triangulation'], self.source['coordinates']
        self.assertFalse(verify_normal_cut_unsaturated_handlebodies(
            raw, rows, self.saved['certificate'], max_operations=0))
        self.assertFalse(verify_normal_cut_unsaturated_handlebodies(raw, rows, {}))
        result = normal_cut_unsaturated_handlebodies(raw, rows, max_cycles=0)
        self.assertEqual(result['status'], 'INCONCLUSIVE')

    def test_all_saved_new_cases_replay(self):
        for path in sorted((Path(__file__).resolve().parents[1] / 'evidence').glob('*_certificate.json')):
            saved = json.loads(path.read_text())
            source = saved['source']
            self.assertTrue(verify_normal_cut_unsaturated_handlebodies(
                source['triangulation'], source['coordinates'], saved['certificate']), path.name)


if __name__ == '__main__':
    unittest.main()
