"""Actual policy transitions, independent scalars and one shared resource cap."""
import contextlib
import io
import json
from pathlib import Path
import random
import unittest
from unittest.mock import patch

from fastunknot import Diagram, recognize
from fastunknot.__main__ import main
from fastunknot.adaptive_potts import adaptive_potts_exact
from fastunknot.geometry import ScanLimit
from fastunknot.potts_exact import PottsLimit, potts_exact
from fastunknot.separator_order import verify_width_bounded_order
from check_potts_independent import laurent_jones, evaluate, times
from disk_grid import descending_grid
from test_shadow_scan import diagrams


def shuffled_grids():
    rng = random.Random(2621)
    for m in (4, 6, 8, 10):
        d = Diagram.from_pd(descending_grid(m))
        order = list(range(d.crossings))
        rng.shuffle(order)
        yield d, order


class AdaptivePottsTests(unittest.TestCase):
    def test_easy_queries_skip_preparation_and_match_independent_cube(self):
        switches = 0
        for d, order in diagrams(20, 2622):
            polynomial = laurent_jones(d)
            for colors in (5, 6, 7):
                for shade in (0, 1):
                    result = adaptive_potts_exact(d, colors=colors, shade=shade, order=order)
                    self.assertEqual(tuple(result['partition_function']),
                                     times(evaluate(polynomial, colors),
                                           tuple(result['unknot_partition']), colors))
                    switches += result['ordering_policy']['mode'] != 'ordinary'
        self.assertGreater(switches, 0)  # The independent oracle covers real switches too.
        with patch('fastunknot.adaptive_potts.width_bounded_scan_order',
                   side_effect=AssertionError('easy query prepared a separator')):
            result = adaptive_potts_exact(Diagram.from_braid(2, [1, 1, 1]))
        self.assertEqual(result['ordering_policy']['mode'], 'ordinary')
        self.assertNotIn('order_certificate', result)
        self.assertFalse(adaptive_potts_exact(Diagram.from_pd([]), max_states=0)['differs'])

    def test_measured_restart_preserves_values_and_exact_shared_budget(self):
        d, order = list(shuffled_grids())[2]
        result = adaptive_potts_exact(d, order=order, max_states=None, max_transitions=None)
        policy = result['ordering_policy']
        self.assertEqual(policy['mode'], 'certified-restart')
        self.assertEqual(policy['trigger'], 'measured-work')
        self.assertEqual(policy['restarts'], 1)
        self.assertGreater(policy['discarded_transitions'], 0)
        cert = result['order_certificate']
        self.assertTrue(verify_width_bounded_order(d.pd, cert))
        reference = potts_exact(d, shade=result['shade'], order=cert['order'])
        for field in ('partition_function', 'unknot_partition', 'differs'):
            self.assertEqual(result[field], reference[field])
        self.assertEqual(result['transitions'], reference['transitions']+policy['discarded_transitions'])
        self.assertEqual(adaptive_potts_exact(d, order=order, max_states=None,
                         max_transitions=result['transitions']), result)
        stats = {}
        with self.assertRaises(PottsLimit) as failure:
            adaptive_potts_exact(d, order=order, max_states=None, max_transitions=result['transitions']-1,
                                 statistics=stats)
        self.assertEqual(failure.exception.transitions, result['transitions']-1)
        self.assertEqual(stats['ordering_policy']['spent_transitions'], failure.exception.transitions)
        self.assertTrue(verify_width_bounded_order(d.pd, stats['order_certificate']))
        self.assertNotIn('partition_function', stats)

    def test_unchanged_order_continues_without_repeating_any_work(self):
        d = Diagram.from_pd(descending_grid(12))
        reference = potts_exact(d)
        with patch('fastunknot.adaptive_potts.potts_exact', wraps=potts_exact) as calls:
            result = adaptive_potts_exact(d)
        self.assertEqual(calls.call_count, 1)
        self.assertEqual(result['ordering_policy']['mode'], 'certified-continue')
        self.assertEqual(result['ordering_policy']['discarded_transitions'], 0)
        for field in reference:
            self.assertEqual(result[field], reference[field])
        d = Diagram.from_pd(descending_grid(10))
        with patch('fastunknot.adaptive_potts.width_bounded_scan_order',
                   side_effect=AssertionError('polynomial tail prepared a separator')):
            tail = adaptive_potts_exact(d)
        self.assertEqual(tail['ordering_policy']['mode'], 'polynomial-tail')
        self.assertEqual(tail['transitions'], potts_exact(d)['transitions'])

    def test_actual_state_limit_can_reorder_but_unchanged_failure_is_not_retried(self):
        d, order = list(shuffled_grids())[1]
        result = adaptive_potts_exact(d, order=order)
        self.assertEqual(result['ordering_policy']['trigger'], 'state-limit')
        self.assertEqual(result['ordering_policy']['mode'], 'certified-restart')
        self.assertFalse(result['differs'])
        stats = {}
        with patch('fastunknot.adaptive_potts.potts_exact', wraps=potts_exact) as calls:
            with self.assertRaises(PottsLimit):
                adaptive_potts_exact(d, max_states=1, statistics=stats)
        self.assertEqual(calls.call_count, 1)
        self.assertEqual(stats['ordering_policy']['mode'], 'certified-declined')
        self.assertTrue(verify_width_bounded_order(d.pd, stats['order_certificate']))

    def test_no_preparation_without_remaining_budget_and_global_stop_is_atomic(self):
        d, order = list(shuffled_grids())[1]
        for options in ({'max_states': 0}, {'max_transitions': 0}, {'max_transitions': 1}):
            with patch('fastunknot.adaptive_potts.width_bounded_scan_order',
                       side_effect=AssertionError('no remaining work')):
                with self.assertRaises(PottsLimit):
                    adaptive_potts_exact(d, order=order, **options)
        stats = {}
        with patch('fastunknot.adaptive_potts.width_bounded_scan_order',
                   side_effect=ScanLimit('global stop during preparation')):
            with self.assertRaises(ScanLimit):
                adaptive_potts_exact(d, order=order, statistics=stats)
        self.assertNotIn('order_certificate', stats)
        self.assertNotIn('partition_function', stats)
        self.assertEqual(stats['ordering_policy']['restarts'], 0)
        for options in ({'colors': True}, {'shade': True}, {'max_states': -1},
                        {'max_transitions': 1.5}, {'order': [0]}):
            with self.assertRaises(ValueError):
                adaptive_potts_exact(d, **options)

    def test_cli_and_pipeline_keep_scalar_agreement_inconclusive(self):
        root = Path(__file__).resolve().parents[1] / 'examples'
        stream = io.StringIO()
        with contextlib.redirect_stdout(stream):
            code = main(['jones', str(root/'trefoil.json'), '--backend', 'potts-adaptive'])
        self.assertEqual(code, 0)
        witness = json.loads(stream.getvalue())['witness']
        self.assertEqual(witness['ordering_policy']['mode'], 'ordinary')
        d = Diagram.from_pd(Diagram.from_braid(3, [1, -2]*5).pd)
        out = recognize(d, jones_backend='potts-adaptive', potts_colors=5,
                        use_braid=False, use_seifert=False, use_reduction=False,
                        use_descending=False, use_factorization=False, use_modular=False,
                        use_alexander=False, use_r3=False)
        self.assertEqual(out.status, 'KNOTTED')
        self.assertEqual(out.evidence['jones'], 'inconclusive')
        self.assertIn('khovanov', out.evidence)
        self.assertEqual(out.evidence['jones_ordering_policy']['mode'], 'ordinary')


if __name__ == '__main__':
    unittest.main()
