"""Shared source budgets and independent replay for the default group fallback."""
from contextlib import ExitStack
from copy import deepcopy
import json
from pathlib import Path
import unittest
from unittest.mock import patch

from fastunknot import normal_cut_handlebodies as producer
from fastunknot.normal_cut_handlebodies_verify import verify_normal_cut_handlebodies


class EulerGroupPortfolioTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cases = json.loads((Path(__file__).parents[1] /
                            'marked_parallelity_research/corpus.json').read_text())['cases']
        c = next(c for c in cases if c['id'] == 'pilot/finite_figureEight/0')
        cls.args = c['triangulation'], c['coordinates']

    def test_single_source_and_boundary_for_each_backend(self):
        for method, helper in [('masks', 'normal_parallelity_boundary_words'),
                               ('moments', '_compile_moment_boundary')]:
            with self.subTest(method=method), ExitStack() as stack:
                source = stack.enter_context(patch.object(producer, 'normal_cut_parallelity',
                    wraps=producer.normal_cut_parallelity))
                boundary = stack.enter_context(patch.object(producer, helper,
                    wraps=getattr(producer, helper)))
                r = producer.normal_cut_handlebodies(*self.args, boundary_method=method,
                                                     record_certificate=True)
                self.assertEqual(source.call_count, 1)
                self.assertEqual(boundary.call_count, 1)
                self.assertEqual(r['status'], 'COMPLETE')
                self.assertEqual(r['stats']['lower_forest_attempts'][-1]['strategy'], 'euler_free')
                self.assertTrue(verify_normal_cut_handlebodies(*self.args, r['certificate']))

    def test_exact_cycle_and_replay_operation_budgets(self):
        for method in ('masks', 'moments'):
            with self.subTest(method=method):
                r = producer.normal_cut_handlebodies(*self.args, boundary_method=method,
                                                     record_certificate=True)
                cycles = sum(s['orbit_cycles'] for s in r['stats']['parallelity'].values())
                cycles += sum(s['orbit_cycles'] for s in r['stats']['boundary'].values()
                              if isinstance(s, dict) and 'orbit_cycles' in s)
                exact = producer.normal_cut_handlebodies(*self.args, boundary_method=method,
                            record_certificate=True, max_cycles=cycles)
                self.assertEqual(exact['certificate'], r['certificate'])
                below = producer.normal_cut_handlebodies(*self.args, boundary_method=method,
                                                         max_cycles=cycles-1)
                self.assertEqual(below['status'], 'INCONCLUSIVE')
                p = r['certificate']; operations = 0
                for name in ('vertex_selector', 'boundary_selector', 'polygon_weights', 'fibre_cover'):
                    proof = p['parallelity'][name]
                    if name.endswith('selector'): proof = proof['weighted_certificate']
                    operations += len(proof['orbit_proof']['operations'])
                for name in (('census',) if method == 'moments' else ('vertex_partition', 'gap_cover')):
                    if p['boundary'][name] is not None:
                        operations += len(p['boundary'][name]['orbit_proof']['operations'])
                pivots = sum(len(g['proof']['moves']) for g in p['groups'])
                self.assertGreater(pivots, 0)
                self.assertTrue(verify_normal_cut_handlebodies(*self.args, p,
                                                               max_operations=operations+pivots))
                self.assertFalse(verify_normal_cut_handlebodies(*self.args, p,
                                                                max_operations=operations+pivots-1))

    def test_replay_without_producer_helpers_and_hostile_masks(self):
        r = producer.normal_cut_handlebodies(*self.args, record_certificate=True)
        names = ['normal_cut_handlebodies.normal_cut_handlebodies',
                 'normal_cut_groups._group_terminal', 'normal_cut_groups._group_result',
                 'normal_cut_groups.normal_cut_group_handlebodies',
                 'normal_cut_groups.compile_disk_cut_presentation',
                 'normal_cut_groups.certify_free_group',
                 'source_cut_group.compile_disk_cut_presentation',
                 'free_group_elimination.certify_free_group']
        with ExitStack() as stack:
            for name in names:
                stack.enter_context(patch('fastunknot.' + name, side_effect=AssertionError(name)))
            self.assertTrue(verify_normal_cut_handlebodies(*self.args, r['certificate']))
        for name in ('vertex_partition', 'gap_cover'):
            bad = deepcopy(r['certificate']); bad['boundary'][name] = {'bad': 1}
            self.assertFalse(verify_normal_cut_handlebodies(*self.args, bad))
            self.assertFalse(verify_normal_cut_handlebodies(*self.args, bad, max_operations=100000))
        plain = producer.normal_cut_handlebodies(*self.args)
        self.assertEqual(plain['census'], r['census'])
        self.assertNotIn('certificate', plain)

    def test_falsey_cancellation_reaches_terminal_and_checker(self):
        class Stop(ValueError): pass
        class Cancel:
            def __bool__(self): return False
            def __call__(self): raise Stop('cancel')
        r = producer.normal_cut_handlebodies(*self.args, record_certificate=True)
        # Fail after source and boundary authentication, inside signed group work.
        from fastunknot.normal_cut_groups import _group_terminal
        p = r['certificate']
        with self.assertRaises(Stop):
            _group_terminal(p['parallelity']['geometry'], p['parallelity']['summary'],
                            p['boundary']['skeleton'], Cancel())
        with self.assertRaises(Stop):
            verify_normal_cut_handlebodies(*self.args, p, check=Cancel())

if __name__ == '__main__': unittest.main()
