import copy
import json
from pathlib import Path
import unittest

from fastunknot.normal_cut_groups import normal_cut_group_handlebodies
from fastunknot.normal_cut_groups_verify import verify_normal_cut_group_handlebodies
from fastunknot.normal_cut_handlebodies import normal_cut_handlebodies
from fastunknot.normal_cut_handlebodies_verify import verify_normal_cut_handlebodies


ROOT = Path(__file__).resolve().parents[1]


class EulerGroupTerminalTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.cases = {}
        for name in ('corpus.json', 'three_handle_corpus.json'):
            data = json.loads((ROOT / 'marked_parallelity_research' / name).read_text())
            cls.cases.update((c['id'], c) for c in data['cases'])
        cls.target = cls.cases['pilot/finite_figureEight/0']
        cls.result = normal_cut_group_handlebodies(cls.target['triangulation'],
                                                  cls.target['coordinates'], record_certificate=True)

    def test_missed_figure_eight_is_certified(self):
        result = self.result
        self.assertEqual(result['status'], 'COMPLETE')
        self.assertEqual(result['census']['histogram'],
                         [dict(genus=1, multiplicity=1), dict(genus=2, multiplicity=1)])
        self.assertFalse(result['census']['all_balls'])
        self.assertEqual(result['census']['euler_characteristic'], -1)
        self.assertEqual(result['census']['free_rank_sum'], 3)
        stats = result['stats']['terminal']['presentation']
        self.assertEqual((stats['generators'], stats['relators'], stats['word_length']), (25, 22, 53))
        self.assertTrue(verify_normal_cut_group_handlebodies(self.target['triangulation'],
                        self.target['coordinates'], result['certificate']))

    def test_existing_verifier_dispatches_new_schema(self):
        self.assertTrue(verify_normal_cut_handlebodies(self.target['triangulation'],
                        self.target['coordinates'], self.result['certificate']))

    def test_opt_in_fallback(self):
        old = normal_cut_handlebodies(self.target['triangulation'], self.target['coordinates'])
        self.assertEqual(old['status'], 'INCONCLUSIVE')
        new = normal_cut_handlebodies(self.target['triangulation'], self.target['coordinates'],
                                     record_certificate=True, group_fallback=True)
        self.assertEqual(new['status'], 'COMPLETE')
        self.assertTrue(verify_normal_cut_handlebodies(self.target['triangulation'],
                        self.target['coordinates'], new['certificate']))

    def test_free_group_with_positive_h2_is_refused(self):
        case = self.cases['pilot/solid_torus_sum_s2xs1/0']
        result = normal_cut_group_handlebodies(case['triangulation'], case['coordinates'])
        self.assertEqual(result['status'], 'INCONCLUSIVE')
        self.assertEqual(result['reason'], 'positive_second_betti_number')
        self.assertEqual(result['second_betti_sum'], 1)

    def test_census_and_euler_mutations_rejected(self):
        for field, value in [('components', 1), ('free_rank_sum', 2),
                             ('all_balls', True), ('euler_characteristic', 0)]:
            proof = copy.deepcopy(self.result['certificate'])
            proof['census'][field] = value
            self.assertFalse(verify_normal_cut_group_handlebodies(self.target['triangulation'],
                             self.target['coordinates'], proof), field)

    def test_presentation_and_group_mutations_rejected(self):
        proof = copy.deepcopy(self.result['certificate'])
        proof['presentation']['components'][0]['relators'][0]['word'][0] *= -1
        self.assertFalse(verify_normal_cut_group_handlebodies(self.target['triangulation'],
                         self.target['coordinates'], proof))
        proof = copy.deepcopy(self.result['certificate'])
        proof['groups'][0]['proof']['free_rank'] += 1
        self.assertFalse(verify_normal_cut_group_handlebodies(self.target['triangulation'],
                         self.target['coordinates'], proof))

    def test_wrong_source_rejected(self):
        coordinates = copy.deepcopy(self.target['coordinates'])
        coordinates = [[2 * x for x in row] for row in coordinates]
        self.assertFalse(verify_normal_cut_group_handlebodies(self.target['triangulation'],
                         coordinates, self.result['certificate']))

    def test_operation_cap_and_invalid_options(self):
        self.assertFalse(verify_normal_cut_group_handlebodies(self.target['triangulation'],
                         self.target['coordinates'], self.result['certificate'], max_operations=0))
        for value in (-1, True):
            with self.assertRaises(ValueError):
                normal_cut_group_handlebodies(self.target['triangulation'],
                                               self.target['coordinates'], max_cycles=value)
        with self.assertRaises(ValueError):
            normal_cut_handlebodies(self.target['triangulation'], self.target['coordinates'],
                                   group_fallback='yes')

    def test_cooperative_stop(self):
        class Stop(RuntimeError):
            pass
        def check():
            raise Stop()
        with self.assertRaises(Stop):
            normal_cut_group_handlebodies(self.target['triangulation'],
                                          self.target['coordinates'], check=check)
        with self.assertRaises(Stop):
            verify_normal_cut_group_handlebodies(self.target['triangulation'],
                self.target['coordinates'], self.result['certificate'], check=check)


if __name__ == '__main__':
    unittest.main()
