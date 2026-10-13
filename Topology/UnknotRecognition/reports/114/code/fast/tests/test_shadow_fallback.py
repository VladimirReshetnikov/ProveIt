"""One-way observer fallback retains exact values and the original query cap."""
import json
from pathlib import Path
import unittest
from unittest.mock import patch

from fastunknot import Diagram
from fastunknot.euler_scan import EulerBudget
from fastunknot.geometry import ScanLimit
from fastunknot.scan_fast import FastScan
from fastunknot.shadow_scan import (ClosureShadow, ShadowWorkBudget, _EulerPart,
                                   shadow_compressed_khovanov_decide)
from test_shadow_scan import diagrams, ReferenceDiagram, reduced_homology


def conway_sum():
    path = Path(__file__).resolve().parents[1] / 'examples/conway_sum_8.json'
    return Diagram.from_json(json.loads(path.read_text()))


class ShadowFallbackTests(unittest.TestCase):
    def test_zero_marked_work_preserves_an_early_euler_certificate(self):
        out = shadow_compressed_khovanov_decide(conway_sum().pd, shadow_max_work=0,
                                               euler_max_states=2)
        self.assertEqual((out['status'], out['method'], out['stage']),
                         ('KNOTTED', 'component-euler', 11))
        self.assertTrue(out['shadow_exhausted'])
        self.assertFalse(out['euler_exhausted'])
        stats = out['shadow_stats']
        self.assertEqual(stats['observer_mode'], 'euler')
        self.assertEqual(stats['states'], 2)
        self.assertEqual(stats['euler_fallback_states'], 2)
        self.assertEqual(stats['work_units'], 0)
        self.assertEqual(stats['determinants'], 0)
        self.assertGreater(stats['euler_fallback_traversed_darts'], 0)

    def test_partial_determinant_does_not_reset_the_shared_query_cap(self):
        diagram = conway_sum()
        for cap in (1, 2):
            out = shadow_compressed_khovanov_decide(diagram.pd, shadow_max_work=2800,
                                                   euler_max_states=cap)
            self.assertEqual(out['status'], 'KNOTTED')
            self.assertTrue(out['shadow_exhausted'])
            self.assertEqual(out['euler_exhausted'], cap == 1)
            stats = out['shadow_stats']
            self.assertEqual(stats['states'], cap)
            self.assertEqual(stats['euler_fallback_states'], cap - 1)
            self.assertGreater(stats['tait_block_determinants'], 0)
            self.assertLessEqual(stats['work_units'], 2800)
            self.assertEqual((out['method'], out['stage']),
                             ('closed-rank', 88) if cap == 1 else ('component-euler', 11))
            self.assertEqual(stats['observer_mode'], 'scan' if cap == 1 else 'euler')

    def test_cached_euler_value_survives_work_exhaustion_and_deadline_wins(self):
        d = Diagram.from_braid(2, [1, 1, 1])
        engine = ClosureShadow(d.pd, [0, 1, 2], max_states=1)
        expected = engine.evaluate_one(0, ())
        engine.max_work = engine.stats['work_units']
        with self.assertRaises(ShadowWorkBudget):
            engine.evaluate(0, ())
        self.assertNotIn((0, ()), engine.shadow_cache)
        cache = engine.cache
        observer = _EulerPart(engine)
        observer.disable_shadow()
        before = dict(engine.stats)
        with patch.object(engine, '_tick', side_effect=AssertionError('spent marked allowance reused')):
            self.assertEqual(observer.evaluate(0, ()), expected)
        self.assertIs(cache, engine.cache)
        self.assertEqual(engine.stats['states'], 1)
        self.assertEqual(engine.stats['work_units'], before['work_units'])
        self.assertEqual(engine.stats['euler_fallback_states'], 0)
        self.assertEqual(engine.stats['euler_fallback_traversed_darts'], 0)
        scan = FastScan()
        scan.add_crossing(d.pd[0])
        pairs = scan.algebra.pairs[next(m for m in scan.mid if m is not None)]
        with self.assertRaises(EulerBudget):
            observer.evaluate(1, pairs)
        with self.assertRaises(ValueError):
            observer.evaluate(3, ())
        engine.deadline = 0
        with self.assertRaises(ScanLimit):
            observer.evaluate(0, ())

    def test_random_budget_transitions_against_independent_homology(self):
        for diagram, order in diagrams(20, 2613):
            for d in (diagram, diagram.mirror()):
                rank = reduced_homology(ReferenceDiagram(d.pd))['rank']
                for work, states in ((0, 0), (0, 1), (0, 100), (25, 2), (100, 100)):
                    out = shadow_compressed_khovanov_decide(d.pd, order=order,
                        shadow_max_work=work, euler_max_states=states, check_d_squared=True)
                    self.assertEqual(out['status'], 'UNKNOT' if rank == 1 else 'KNOTTED')
                    self.assertLessEqual(out['shadow_stats']['work_units'], work)
                    self.assertLessEqual(out['shadow_stats']['states'], states)
                    if out['status'] == 'UNKNOT':
                        self.assertEqual(out['stage'], d.crossings)
                        self.assertEqual(out['method'], 'closed-rank')

    def test_global_interrupt_during_transition_is_not_an_euler_decline(self):
        original = _EulerPart.disable_shadow
        def expire(observer):
            original(observer)
            observer.engine.deadline = 0
        d = Diagram.from_braid(2, [1, 1, 1])
        with patch.object(_EulerPart, 'disable_shadow', expire), self.assertRaises(ScanLimit):
            shadow_compressed_khovanov_decide(d.pd, shadow_max_work=0)


if __name__ == '__main__':
    unittest.main()
