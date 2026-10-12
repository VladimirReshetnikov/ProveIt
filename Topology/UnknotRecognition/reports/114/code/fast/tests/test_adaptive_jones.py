"""Exact cross-backend switching, shared work limits and one-sided integration."""
import contextlib
import io
import json
import random
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

from fastunknot import Diagram, recognize
from fastunknot.__main__ import main
from fastunknot.adaptive_jones import (AdaptiveJonesLimit, adaptive_jones_exact,
                                       adaptive_jones_obstruction)
from fastunknot.faithful_jones import faithful_potts_exact
from fastunknot.geometry import ScanLimit
from fastunknot.separator_order import verify_width_bounded_order
from fastunknot.spin_jones import spin_jones_exact
from check_potts_independent import laurent_jones
from disk_grid import descending_grid
from test_spin_jones import examples
from test_spin_jones_integration import OPTIONS


class AdaptiveJonesTests(unittest.TestCase):
    def test_both_winners_and_direct_spin_match_independent_cube(self):
        winners = set()
        for original, order in examples(18, 26100866):
            for diagram in (original, original.mirror()):
                oracle = {-k: c for k, c in laurent_jones(diagram).items()}
                for trial in (None, 0, 1):
                    result = adaptive_jones_exact(diagram, order=order,
                        potts_trial_transitions=trial, include_polynomial=True)
                    observed = {k: int(c, 16) for k, c in result['jones_polynomial']['coefficients_hex']}
                    self.assertEqual(observed, oracle)
                    self.assertEqual(result['polynomial_identity']['is_one'], oracle == {0: 1})
                    policy = result['backend_policy']
                    self.assertEqual(result['transitions'], policy['spent_transitions'])
                    self.assertEqual(result['transitions'],
                        policy['potts_transitions']+policy['spin_transitions'])
                    winners.add(result['selected_backend'])
        self.assertEqual(winners, {'potts', 'spin'})

    def test_easy_potts_completion_avoids_spin_and_separator(self):
        diagram = Diagram.from_braid(2, [1, 1, 1])
        with patch('fastunknot.adaptive_jones.spin_jones_exact',
                   side_effect=AssertionError('easy query entered spin')):
            with patch('fastunknot.adaptive_potts.width_bounded_scan_order',
                       side_effect=AssertionError('easy query prepared separator')):
                result = adaptive_jones_exact(diagram, include_polynomial=True)
        self.assertEqual(result['selected_backend'], 'potts')
        self.assertEqual(result['backend_policy']['switches'], 0)
        self.assertEqual(result['backend_policy']['trial_limit'], 128*3)

    def test_default_measured_switch_reuses_certified_order_and_caps_total_work(self):
        diagram = Diagram.from_pd(descending_grid(12))
        with patch('fastunknot.spin_jones.width_bounded_scan_order',
                   side_effect=AssertionError('spin rebuilt the retained order')):
            result = adaptive_jones_exact(diagram, max_states=None, max_transitions=None,
                                           include_polynomial=True)
        policy = result['backend_policy']
        self.assertEqual(result['selected_backend'], 'spin')
        self.assertEqual(policy['potts_transitions'], 128*diagram.crossings)
        self.assertTrue(policy['reused_order'])
        self.assertEqual(policy['switches'], 1)
        self.assertTrue(verify_width_bounded_order(diagram.pd, result['order_certificate']))
        exact = adaptive_jones_exact(diagram, max_states=None,
            max_transitions=result['transitions'], include_polynomial=True)
        self.assertEqual(exact, result)
        stats = {}
        with self.assertRaises(AdaptiveJonesLimit) as caught:
            adaptive_jones_exact(diagram, max_states=None,
                max_transitions=result['transitions']-1, statistics=stats)
        self.assertEqual(caught.exception.transitions, result['transitions']-1)
        self.assertEqual(stats['backend_policy']['spent_transitions'], caught.exception.transitions)
        self.assertTrue(verify_width_bounded_order(diagram.pd, stats['order_certificate']))
        for field in ('scaled_bracket', 'partition_function', 'polynomial_identity', 'jones_polynomial'):
            self.assertNotIn(field, stats)

    def test_state_limit_can_switch_to_a_smaller_representation(self):
        diagram = Diagram.from_pd(descending_grid(14))
        result = adaptive_jones_exact(diagram, include_polynomial=True)
        self.assertEqual(result['jones_polynomial']['coefficients_hex'], [[0, '0x1']])
        self.assertIn('frontier', result['backend_policy']['potts_stop'])
        self.assertEqual(result['selected_backend'], 'spin')
        self.assertEqual(result['peak_states'], 4097)  # Includes rejected Potts insertion.
        self.assertGreater(result['transitions'], result['backend_policy']['spin_transitions'])

        # Potts can spend work on two orders before the cross-backend switch.
        diagram = Diagram.from_pd(descending_grid(8))
        order = list(range(64))
        random.Random(26100859).shuffle(order)
        with patch('fastunknot.adaptive_jones.faithful_potts_exact',
                   wraps=faithful_potts_exact) as prelude:
            result = adaptive_jones_exact(diagram, order=order,
                potts_trial_transitions=5500, include_polynomial=True)
        internal = prelude.call_args.kwargs['statistics']['ordering_policy']
        self.assertEqual(internal['restarts'], 1)
        self.assertGreater(internal['discarded_transitions'], 0)
        self.assertEqual(internal['spent_transitions'], 5500)
        self.assertEqual(result['backend_policy']['potts_transitions'], 5500)
        direct = spin_jones_exact(diagram, certify_order=False,
            order=result['order_certificate']['order'], include_polynomial=True)
        self.assertEqual(result['transitions'], 5500+direct['transitions'])
        self.assertEqual(result['jones_polynomial'], direct['jones_polynomial'])

    def test_exhausted_prelude_does_not_reset_budget_or_start_spin(self):
        diagram = Diagram.from_braid(3, [1, -2]*5)
        stats = {}
        with patch('fastunknot.adaptive_jones.spin_jones_exact',
                   side_effect=AssertionError('exhausted caller cap restarted')):
            with self.assertRaises(AdaptiveJonesLimit) as caught:
                adaptive_jones_exact(diagram, max_transitions=2, statistics=stats)
        self.assertEqual(caught.exception.transitions, 2)
        self.assertEqual(stats['backend_policy']['mode'], 'exhausted-before-spin')
        self.assertEqual(stats['backend_policy']['switches'], 0)
        self.assertNotIn('polynomial_identity', stats)

    def test_validation_empty_knot_and_global_cancellation_do_not_publish_values(self):
        empty = adaptive_jones_exact(Diagram.from_pd([]), max_states=0,
                                     max_transitions=0, include_polynomial=True)
        self.assertEqual(empty['jones_polynomial']['coefficients_hex'], [[0, '0x1']])
        diagram = Diagram.from_braid(2, [1, 1, 1])
        for options in ({'max_states': False}, {'max_transitions': -1},
                        {'potts_trial_transitions': True}, {'include_polynomial': 1},
                        {'potts_trial_transitions': -1}, {'order': [0]}):
            with self.assertRaises(ValueError):
                adaptive_jones_exact(diagram, **options)
        for options in ({'max_states': 0}, {'max_transitions': 0}):
            with patch('fastunknot.adaptive_jones.faithful_potts_exact',
                       side_effect=AssertionError('zero cap started work')):
                with self.assertRaises(AdaptiveJonesLimit):
                    adaptive_jones_exact(diagram, **options)
        for trial in (None, 0):
            stats = {}
            target = ('fastunknot.faithful_jones.reconstruct_jones' if trial is None
                      else 'fastunknot.spin_jones.reconstruct_spin_jones')
            with patch(target, side_effect=ScanLimit('global stop during decoding')):
                with self.assertRaises(ScanLimit):
                    adaptive_jones_exact(diagram, include_polynomial=True,
                        potts_trial_transitions=trial, statistics=stats)
            self.assertNotIn('polynomial_identity', stats)
            self.assertNotIn('jones_polynomial', stats)

    def test_json_safe_witnesses_cli_and_recognition_identity_fallback(self):
        diagram = Diagram.from_braid(2, [1]*101)
        for trial in (None, 0):
            witness = adaptive_jones_obstruction(diagram, potts_trial_transitions=trial,
                                                include_polynomial=True)
            self.assertIsNotNone(witness)
            json.loads(json.dumps(witness))
        options = dict(OPTIONS, jones_backend='faithful-adaptive')
        result = recognize(Diagram.from_pd(Diagram.from_braid(2, [1]).pd), **options)
        self.assertEqual(result.status, 'UNKNOT')
        self.assertTrue(result.evidence['jones_polynomial_identity']['is_one'])
        self.assertIn('khovanov', result.evidence)
        self.assertIn('jones_backend_policy', result.evidence)
        knot = recognize(Diagram.from_pd(Diagram.from_braid(3, [1, -2]*5).pd), **options)
        self.assertEqual(knot.method, 'jones-faithful-adaptive')
        self.assertEqual(knot.status, 'KNOTTED')
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory)/'trefoil.json'
            path.write_text(json.dumps({'pd': Diagram.from_braid(2, [1, 1, 1]).pd}))
            stream = io.StringIO()
            with contextlib.redirect_stdout(stream):
                code = main(['jones', str(path), '--backend', 'faithful-adaptive'])
            self.assertEqual(code, 0)
            decoded = json.loads(stream.getvalue())
            self.assertEqual(decoded['verdict'], 'KNOTTED')
            self.assertIn('jones_polynomial', decoded)
            self.assertEqual(decoded['backend_policy']['mode'], 'potts-complete')


if __name__ == '__main__':
    unittest.main()
