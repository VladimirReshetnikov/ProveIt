import unittest
from integration.occurrence_adapter import propose_core_plan

class AdapterTests(unittest.TestCase):
    def test_abstract_core_shape_with_unused_handle(self):
        core = {'handles0': [{}, {}],
                'handles1': [{'id': 0, 'ends': [0, 1]},
                             {'id': 1, 'ends': [0, 1]},
                             {'id': 2, 'ends': [1, 1]}],
                'handles2': [{'id': 8, 'cycle': [
                    {'dimension': 1, 'handle': 0},
                    {'dimension': 1, 'handle': 1}]}]}
        result = propose_core_plan(core)
        self.assertEqual(result['status'], 'MATRIX_PLAN_NOT_GEOMETRY')
        self.assertFalse(result['source_geometry_authenticated'])
        self.assertEqual(result['matrix_result']['matched_weight'], 1)
        self.assertEqual(len(result['deferred_forest']['forest']), 1)

    def test_bad_parity_refused(self):
        core = {'handles0': [{}, {}], 'handles1': [{'id': 0, 'ends': [0, 1]}],
                'handles2': [{'id': 0, 'cycle': [{'dimension': 1, 'handle': 0}]}]}
        with self.assertRaises(ValueError): propose_core_plan(core)

if __name__ == '__main__': unittest.main()
