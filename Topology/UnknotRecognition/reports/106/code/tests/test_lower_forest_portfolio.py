"""Portability, source integrity and refusal tests for the optional adapter."""

from copy import deepcopy
import importlib
import json
from pathlib import Path
import unittest
from unittest.mock import patch

from fastunknot.normal_cut_handlebodies import normal_cut_handlebodies
from fastunknot.normal_cut_handlebodies_verify import verify_normal_cut_handlebodies
from lower_forest_research import normal_cut_handlebodies_with_forests
from normal_orbit_research.fixtures import layered_torus


class LowerForestPortfolioTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        corpus = Path(__file__).resolve().parents[1] / 'marked_parallelity_research/corpus.json'
        cls.cases = {c['id']: c for c in json.loads(corpus.read_text())['cases']}

    def source(self, name='pilot/fibonacci_lst_04/0'):
        case = deepcopy(self.cases[name])
        return case['triangulation'], case['coordinates']

    def test_success_uses_ordinary_independent_whole_cut_replay(self):
        raw, rows = self.source()
        result = normal_cut_handlebodies_with_forests(raw, rows, record_certificate=True)
        self.assertEqual(result['status'], 'COMPLETE')
        self.assertTrue(verify_normal_cut_handlebodies(raw, rows, result['certificate']))
        stats = result['stats']['lower_forest_portfolio']
        self.assertEqual(stats['extra_forests'], 1)
        self.assertEqual(stats['core_searches'][0]['trials'][0]['policy'], 'exceptional_first')
        broken = deepcopy(result['certificate'])
        broken['core']['forest'].append(broken['core']['forest'][0])
        self.assertFalse(verify_normal_cut_handlebodies(raw, rows, broken))

    def test_baseline_complete_returns_exact_native_result(self):
        raw, rows = layered_torus(1)
        expected = normal_cut_handlebodies(raw, rows, record_certificate=True)
        actual = normal_cut_handlebodies_with_forests(raw, rows, record_certificate=True)
        self.assertEqual(actual, expected)
        self.assertNotIn('lower_forest_portfolio', actual['stats'])

    def test_zero_limit_returns_native_refusal(self):
        raw, rows = self.source()
        expected = normal_cut_handlebodies(raw, rows, record_certificate=True)
        self.assertEqual(expected['status'], 'INCONCLUSIVE')
        self.assertEqual(normal_cut_handlebodies_with_forests(
            raw, rows, max_extra_forests=0, record_certificate=True), expected)

    def test_second_policy_and_global_forest_limit(self):
        raw, rows = self.source('pachner23_5_8_2/mixed')
        limited = normal_cut_handlebodies_with_forests(raw, rows, max_extra_forests=1)
        self.assertEqual(limited['status'], 'INCONCLUSIVE')
        self.assertTrue(limited['stats']['lower_forest_portfolio']['forest_limit_reached'])
        complete = normal_cut_handlebodies_with_forests(
            raw, rows, max_extra_forests=2, record_certificate=True)
        self.assertEqual(complete['status'], 'COMPLETE')
        stats = complete['stats']['lower_forest_portfolio']
        self.assertEqual(stats['extra_forests'], 2)
        self.assertEqual([t['policy'] for t in stats['core_searches'][0]['trials']],
                         ['exceptional_first', 'reverse'])
        self.assertTrue(verify_normal_cut_handlebodies(raw, rows, complete['certificate']))

    def test_augmented_core_shares_extra_forest_limit(self):
        raw, rows = self.source('pilot/fibonacci_lst_06/0')
        limited = normal_cut_handlebodies_with_forests(raw, rows, max_extra_forests=1)
        self.assertEqual(limited['status'], 'INCONCLUSIVE')
        self.assertEqual(limited['stats']['lower_forest_portfolio']['extra_forests'], 1)
        complete = normal_cut_handlebodies_with_forests(
            raw, rows, max_extra_forests=2, record_certificate=True)
        self.assertEqual(complete['status'], 'COMPLETE')
        self.assertTrue(verify_normal_cut_handlebodies(raw, rows, complete['certificate']))

    def test_inputs_and_public_modules_are_unchanged_without_file_loading(self):
        raw, rows = self.source()
        before = deepcopy((raw, rows))
        module = importlib.import_module('fastunknot.normal_cut_handlebodies')
        global_bindings = dict(vars(module))
        with patch('pathlib.Path.read_text', side_effect=AssertionError('no source reload')):
            result = normal_cut_handlebodies_with_forests(raw, rows, record_certificate=True)
        self.assertEqual(result['status'], 'COMPLETE')
        self.assertEqual((raw, rows), before)
        self.assertEqual(set(vars(module)), set(global_bindings))
        for key, value in global_bindings.items():
            self.assertIs(vars(module)[key], value)
        again = normal_cut_handlebodies_with_forests(raw, rows, record_certificate=True)
        self.assertEqual(result, again)

    def test_cancellation_callback_covers_alternative_planning(self):
        raw, rows = self.source()
        from lower_forest_research import producer
        original = producer._forest

        class Cancel(Exception):
            pass

        active = False

        def observed_forest(core, check):
            nonlocal active
            active = True
            return original(core, check)

        def stop():
            if active:
                raise Cancel('stop during alternative forest traversal')

        with patch.object(producer, '_forest', side_effect=observed_forest):
            with self.assertRaises(Cancel):
                normal_cut_handlebodies_with_forests(raw, rows, check=stop)
        self.assertEqual(normal_cut_handlebodies_with_forests(raw, rows)['status'], 'COMPLETE')

    def test_shared_cycle_budget_never_resets_on_retry(self):
        raw, rows = self.source()
        unrestricted = normal_cut_handlebodies_with_forests(raw, rows, record_certificate=True)
        spent = unrestricted['stats']['lower_forest_portfolio']['total_orbit_cycles']
        self.assertGreater(spent, 0)
        limited = normal_cut_handlebodies_with_forests(raw, rows, max_cycles=spent - 1)
        self.assertEqual(limited['status'], 'INCONCLUSIVE')
        sufficient = normal_cut_handlebodies_with_forests(
            raw, rows, max_cycles=spent, record_certificate=True)
        self.assertEqual(sufficient['status'], 'COMPLETE')
        self.assertEqual(sufficient['certificate'], unrestricted['certificate'])
        self.assertEqual(normal_cut_handlebodies_with_forests(
            raw, rows, max_cycles=0)['status'], 'INCONCLUSIVE')

    def test_invalid_new_options_and_native_validation(self):
        raw, rows = self.source()
        for value in (-1, True, None, 0.5, '2'):
            with self.assertRaises(ValueError):
                normal_cut_handlebodies_with_forests(raw, rows, max_extra_forests=value)
        for option in ({'max_cycles': -1}, {'record_certificate': 1}, {'precheck_core': 1}):
            with self.assertRaises(ValueError):
                normal_cut_handlebodies_with_forests(raw, rows, **option)


if __name__ == '__main__':
    unittest.main()
