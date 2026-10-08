"""One-way representation handoff, trace continuity and shared allowances."""
import json
import subprocess
import sys
import unittest
from unittest.mock import patch

from benchmark_compressed_words import cases, ROOT
from fastunknot import Diagram, recognize, compressed_search
from fastunknot.compressed_words import WordArena
from fastunknot.group_certificate import group_certificate, group_decide, verify_group_certificate
from fastunknot.scan import ScanLimit


class AdaptiveGroupTests(unittest.TestCase):
    def test_default_keeps_explicit_paths_and_never_constructs_an_arena(self):
        for name, d in cases():
            with self.subTest(name=name):
                expected = group_certificate(d, relator_moves=True, max_work=10000000)
                with patch.object(compressed_search, 'WordArena', side_effect=AssertionError('no switch expected')):
                    result = group_decide(d, seconds=None, adaptive_search=True,
                                          relator_moves=True, max_work=10000000)
                self.assertEqual(result['certificate'], expected)
                self.assertEqual(result['search_backend'], 'adaptive')
                self.assertEqual(result['verification_backend'], 'explicit-letters')
                self.assertFalse(result['search_stats']['switched'])

    def test_all_real_handoffs_pass_both_replayers(self):
        for name, d in cases():
            stats = {}
            with self.subTest(name=name), patch.object(compressed_search, '_presentation', side_effect=AssertionError('must not restart')):
                certificate = group_certificate(d, adaptive=True, switch_letters=100,
                    relator_moves=True, max_work=10000000, stats=stats)
                self.assertIsNotNone(certificate)
                for compressed in (False, True):
                    self.assertTrue(verify_group_certificate(d, certificate,
                        compressed=compressed, max_work=10000000))
                if stats['switched']:
                    switch = stats['switch']
                    original = group_certificate(d, relator_moves=True, max_work=10000000)
                    n = switch['before_move']
                    self.assertEqual(certificate['moves'][:n], original['moves'][:n])
                    self.assertGreater(switch['projected_letters'], switch['threshold'])
                    self.assertEqual(stats['work'], switch['explicit_work']+stats['compressed']['work']+1)

    def test_real_letter_cap_exhaustion_becomes_verified_success(self):
        _, d = next(cases())
        for cap, kind in ((64, 'eliminate'), (128, 'whitehead')):
            old = group_decide(d, seconds=None, max_letters=cap)
            self.assertEqual(old['status'], 'INCONCLUSIVE')
            self.assertIn('expanded-letter', old['reason'])
            result = group_decide(d, seconds=None, max_letters=cap, adaptive_search=True)
            self.assertEqual(result['status'], 'UNKNOT')
            self.assertEqual(result['verification_backend'], 'compressed-slp')
            switch = result['search_stats']['switch']
            self.assertEqual(switch['kind'], kind)
            self.assertGreater(switch['before_move'], 0)
            self.assertLessEqual(switch['current_letters'], cap)
            self.assertTrue(verify_group_certificate(d, result['certificate']))

    def test_budget_not_refilled_and_global_cancellation_propagates(self):
        _, d = next(cases())
        result = group_decide(d, seconds=None, max_letters=64, adaptive_search=True)
        spent = result['search_stats']['switch']['explicit_work']
        limited = group_decide(d, seconds=None, max_letters=64, adaptive_search=True,
                               max_work=spent+1)
        self.assertEqual(limited['status'], 'INCONCLUSIVE')
        self.assertEqual(limited['search_stats']['switch']['remaining_work'], 1)
        self.assertIn('work allowance', limited['reason'])
        self.assertEqual(group_decide(d, seconds=None, adaptive_search=True, max_nodes=0)['status'], 'UNKNOT')
        self.assertEqual(group_decide(d, seconds=None, adaptive_search=True,
                                     max_nodes=0, max_letters=64)['status'], 'INCONCLUSIVE')
        cancelled = False
        def check():
            if cancelled:
                raise ScanLimit('global cancellation at handoff')
        def factory(**kwargs):
            nonlocal cancelled
            cancelled = True
            return WordArena(**kwargs)
        with patch.object(compressed_search, 'WordArena', side_effect=factory), self.assertRaises(ScanLimit):
            group_decide(d, seconds=None, max_letters=64, adaptive_search=True, check=check)

    def test_validation_cli_and_nontrivial_knots(self):
        _, d = next(cases())
        for options in ({'adaptive_search': 1}, {'switch_letters': 1},
                        {'adaptive_search': True, 'compressed_search': True},
                        {'adaptive_search': True, 'switch_letters': -1}):
            with self.assertRaises(ValueError):
                group_decide(d, **options)
        for options in ({'adaptive': 1}, {'stats': []}, {'max_nodes': -1},
                        {'switch_letters': 1}, {'adaptive': True, 'switch_letters': True}):
            with self.assertRaises(ValueError):
                group_certificate(d, **options)
        for options in ({'group_adaptive': 1}, {'group_switch_letters': 1},
                        {'group_adaptive': True, 'group_compressed_search': True}):
            with self.assertRaises(ValueError):
                recognize(d, **options)
        result = recognize(Diagram.from_pd(d.pd), use_group=True, group_adaptive=True,
                           group_switch_letters=64, group_seconds=None)
        self.assertTrue(result.evidence['group']['search_stats']['switched'])
        run = subprocess.run([sys.executable, '-B', '-m', 'fastunknot', 'recognize', '-',
            '--group-switch-letters', '64', '--group-seconds', '2'],
            input=json.dumps({'pd': d.pd}), text=True, capture_output=True, cwd=ROOT)
        self.assertEqual(run.returncode, 0, run.stderr)
        group = json.loads(run.stdout)['evidence']['group']
        self.assertEqual(group['search_backend'], 'adaptive')
        self.assertTrue(group['search_stats']['switched'])
        for word in ([1]*3, [1]*5, [1, -2]*2):
            knot = Diagram.from_braid(3 if -2 in word else 2, word)
            self.assertIsNone(group_certificate(knot, adaptive=True, switch_letters=0, relator_moves=True))


if __name__ == '__main__':
    unittest.main()
