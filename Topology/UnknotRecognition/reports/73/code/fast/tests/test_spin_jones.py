"""Independent whole-cube, turning, gauge, decoding and resource audits."""
import copy
import json
from pathlib import Path
import random
import sys
import unittest
from unittest.mock import patch

from fastunknot.diagram import Diagram
from fastunknot.geometry import ScanLimit
from fastunknot.separator_order import verify_width_bounded_order
from fastunknot.spin_jones import (SpinLimit, faithful_base_log,
    reconstruct_spin_jones, spin_jones_exact, turn_certificate,
    verify_turn_certificate, witness_from_spin)
from check_potts_independent import laurent_jones


def examples(count=32, seed=26100853):
    rng = random.Random(seed)
    accepted = 0
    while accepted < count:
        strands = rng.randrange(2, 6)
        word = [rng.choice((-1, 1))*rng.randrange(1, strands)
                for _ in range(rng.randrange(1, 11))]
        try:
            diagram = Diagram.from_braid(strands, word)
        except ValueError:
            continue
        order = list(range(diagram.crossings))
        rng.shuffle(order)
        accepted += 1
        yield diagram, order


def coefficients(result):
    return {degree: int(value, 16) for degree, value in
            result['jones_polynomial']['coefficients_hex']}


class SpinJonesTests(unittest.TestCase):
    def test_identity_shortcut_checks_the_prescribed_normalization(self):
        diagram = Diagram.from_braid(2, [1, -1, 1])
        result = spin_jones_exact(diagram, certify_order=False)
        self.assertEqual(reconstruct_spin_jones(result), {0: 1})
        for forged in (0, 1, 2*result['unknot_scaled_bracket'],
                       -result['unknot_scaled_bracket']):
            corrupted = dict(result, scaled_bracket=forged, unknot_scaled_bracket=forged)
            with self.assertRaisesRegex(ArithmeticError, 'normalization'):
                reconstruct_spin_jones(corrupted)
        with self.assertRaisesRegex(ArithmeticError, 'normalization'):
            reconstruct_spin_jones(dict(result, bracket_shift=result['bracket_shift']+1))
        with self.assertRaises(ValueError):
            reconstruct_spin_jones(dict(result, base_log2=True))
        enormous = 1 << 500
        with self.assertRaisesRegex(ArithmeticError, 'normalization'):
            reconstruct_spin_jones(dict(crossing_count=enormous,
                base_log2=faithful_base_log(enormous), writhe=0,
                bracket_shift=6*enormous+4, scaled_bracket=1, unknot_scaled_bracket=1))
        calls = 0

        def stop_before_identity():
            nonlocal calls
            calls += 1
            if calls == 3:
                raise ScanLimit('cancel before identity publication')

        with self.assertRaises(ScanLimit):
            reconstruct_spin_jones(result, check=stop_before_identity)

    def test_full_polynomial_against_whole_cube_mirrors_orders_and_outer_faces(self):
        cases = list(examples())
        root = Path(__file__).resolve().parents[1]/'examples'
        for name in ('conway', 'kinoshita_terasaka', 'hard_unknot_8'):
            diagram = Diagram.from_json(json.loads((root/(name+'.json')).read_text()))
            cases.append((diagram, list(range(diagram.crossings))))
        comparisons = 0
        for original, order in cases:
            for diagram in (original, original.mirror()):
                expected = {-degree: value for degree, value in laurent_jones(diagram).items()}
                for outer in (0, len(diagram.faces())-1):
                    result = spin_jones_exact(diagram, order=order, outer_face=outer,
                        include_polynomial=True, certify_order=False,
                        max_states=None, max_transitions=None)
                    self.assertEqual(coefficients(result), expected)
                    self.assertEqual(result['polynomial_identity']['is_one'], expected == {0: 1})
                    self.assertLessEqual(result['peak_states'], 1 << result['max_boundary'])
                    comparisons += 1
        self.assertEqual(comparisons, 140)
        empty = spin_jones_exact(Diagram.from_pd([]), max_states=0,
                                 max_transitions=0, include_polynomial=True)
        self.assertEqual(coefficients(empty), {0: 1})

    def test_every_oriented_smoothing_circle_has_total_turn_four(self):
        comparisons = 0
        for diagram, _ in examples(20, 26100854):
            if diagram.crossings > 7:
                continue
            alpha = diagram.alpha()
            for outer in range(len(diagram.faces())):
                certificate = turn_certificate(diagram, outer_face=outer)
                turns = certificate['dart_turns']
                self.assertTrue(verify_turn_certificate(diagram.pd, certificate))
                for smoothing in range(1 << diagram.crossings):
                    paired = [0]*len(alpha)
                    for crossing in range(diagram.crossings):
                        # Independent local pair construction.
                        pairs = ((0, 3), (1, 2)) if smoothing >> crossing & 1 else ((0, 1), (2, 3))
                        for a, b in pairs:
                            paired[4*crossing+a] = 4*crossing+b
                            paired[4*crossing+b] = 4*crossing+a
                    remaining = set(range(len(alpha)))
                    while remaining:
                        dart = start = min(remaining)
                        rotation = 0
                        while True:
                            remaining.remove(dart)
                            incoming = alpha[dart]
                            outgoing = paired[incoming]
                            delta = (outgoing-incoming) % 4
                            self.assertIn(delta, (1, 3))
                            rotation += turns[dart]+(delta-2)
                            dart = outgoing
                            if dart == start:
                                break
                        self.assertIn(rotation, (-4, 4))
                        comparisons += 1
        self.assertGreater(comparisons, 500)

    def test_dual_certificate_rejects_forgery_and_vertex_gauge_preserves_value(self):
        rng = random.Random(26100855)
        for diagram, order in examples(20, 26100856):
            certificate = turn_certificate(diagram)
            bad = copy.deepcopy(certificate)
            bad['dart_turns'][0] += 1
            self.assertFalse(verify_turn_certificate(diagram.pd, bad))
            bad = copy.deepcopy(certificate)
            bad['outer_face'] = (bad['outer_face']+1) % len(diagram.faces())
            self.assertFalse(verify_turn_certificate(diagram.pd, bad))
            bad = copy.deepcopy(certificate)
            bad['dart_turns'][0] = True
            self.assertFalse(verify_turn_certificate(diagram.pd, bad))
            potentials = [rng.randrange(-20, 21) for _ in diagram.pd]
            alpha = diagram.alpha()
            changed = copy.deepcopy(certificate)
            changed['dart_turns'] = [turn+potentials[alpha[dart]//4]-potentials[dart//4]
                for dart, turn in enumerate(certificate['dart_turns'])]
            self.assertTrue(verify_turn_certificate(diagram.pd, changed))
            original = spin_jones_exact(diagram, order=order, certify_order=False,
                                       include_polynomial=True)
            with patch('fastunknot.spin_jones.turn_certificate', return_value=changed):
                modified = spin_jones_exact(diagram, order=order, certify_order=False,
                                           include_polynomial=True)
            self.assertEqual(original['jones_polynomial'], modified['jones_polynomial'])

    def test_balanced_decoder_extreme_degrees_and_signed_coefficients(self):
        rng = random.Random(26100857)
        for n in range(1, 19):
            base_log = faithful_base_log(n)
            bound, base = 1 << (2*n), 1 << (8*base_log)
            cases = [{-2*n: bound}, {2*n: -bound},
                     {-2*n: bound//2, 2*n: -bound//2}, {0: 1}]
            for _ in range(6):
                polynomial = {}
                for _ in range(8):
                    degree = rng.randrange(-2*n, 2*n+1)
                    polynomial[degree] = polynomial.get(degree, 0)+rng.randrange(-(bound//32), bound//32+1)
                cases.append({k: v for k, v in polynomial.items() if v})
            shift, writhe = 40*n*n+10, -n
            exponent = 16*n+4-shift-6*writhe
            self.assertLess(exponent, 0)
            expected = (base+1) << (base_log*(shift+6*writhe-4))
            sign = -1 if (writhe+1) % 2 else 1
            for polynomial in cases:
                encoded = sum(value*base**(2*n-degree) for degree, value in polynomial.items())
                scalar = sign*(encoded*(base+1) << (-base_log*exponent))
                result = dict(crossing_count=n, base_log2=base_log, writhe=writhe,
                              bracket_shift=shift, scaled_bracket=scalar,
                              unknot_scaled_bracket=sign*expected)
                self.assertEqual(reconstruct_spin_jones(result), polynomial)
        with self.assertRaises(ValueError):
            reconstruct_spin_jones(dict(crossing_count=1, base_log2=2))

    def test_exact_budget_bound_and_completed_certificate_survives_exhaustion(self):
        diagram = Diagram.from_braid(3, [1, -2]*5)
        result = spin_jones_exact(diagram, include_polynomial=True)
        self.assertTrue(verify_width_bounded_order(diagram.pd, result['order_certificate']))
        self.assertTrue(verify_turn_certificate(diagram.pd, result['turn_certificate']))
        exact = spin_jones_exact(diagram, max_transitions=result['transitions'],
                                 include_polynomial=True)
        self.assertEqual(exact, result)
        stats = {}
        with self.assertRaises(SpinLimit) as caught:
            spin_jones_exact(diagram, statistics=stats,
                             max_transitions=result['transitions']-1)
        self.assertEqual(caught.exception.transitions, result['transitions']-1)
        self.assertTrue(verify_width_bounded_order(diagram.pd, stats['order_certificate']))
        self.assertNotIn('scaled_bracket', stats)
        self.assertNotIn('polynomial_identity', stats)
        with self.assertRaises(SpinLimit):
            spin_jones_exact(diagram, max_states=1)

    def test_validation_zero_caps_and_cancellation_before_publication(self):
        diagram = Diagram.from_braid(2, [-1, -1, -1])
        for options in ({'include_polynomial': 1}, {'certify_order': 0},
                        {'outer_face': True}, {'outer_face': 100}, {'order': [0]},
                        {'max_states': -1}, {'max_transitions': False}):
            with self.assertRaises(ValueError):
                spin_jones_exact(diagram, **options)
        for value in (True, -1, 1.5):
            with self.assertRaises(ValueError):
                faithful_base_log(value)
        for options in ({'max_states': 0}, {'max_transitions': 0}):
            with patch('fastunknot.spin_jones.width_bounded_scan_order',
                       side_effect=AssertionError('zero cap constructed an order')):
                with self.assertRaises(SpinLimit):
                    spin_jones_exact(diagram, **options)
        stats = {}
        with patch('fastunknot.spin_jones.reconstruct_spin_jones',
                   side_effect=ScanLimit('cancel during decoding')):
            with self.assertRaises(ScanLimit):
                spin_jones_exact(diagram, include_polynomial=True, statistics=stats)
        self.assertNotIn('scaled_bracket', stats)
        self.assertNotIn('jones_polynomial', stats)
        with self.assertRaises(ScanLimit):
            turn_certificate(diagram, check=lambda: (_ for _ in ()).throw(ScanLimit('stop')))

    def test_large_exact_scalars_are_json_safe_and_bit_counter_includes_normalization(self):
        before = getattr(sys, 'get_int_max_str_digits', lambda: None)()
        diagram = Diagram.from_braid(2, [1]*101)
        result = spin_jones_exact(diagram, certify_order=False, include_polynomial=True)
        witness = witness_from_spin(result)
        self.assertIsNotNone(witness)
        decoded = json.loads(json.dumps(witness))
        self.assertEqual(int(decoded['scaled_bracket_hex'], 16), result['scaled_bracket'])
        self.assertEqual(int(decoded['unknot_scaled_bracket_hex'], 16), result['unknot_scaled_bracket'])
        self.assertGreater(result['max_coefficient_bits'], 14000)
        self.assertGreaterEqual(result['max_coefficient_bits'],
                                abs(result['unknot_scaled_bracket']).bit_length())
        self.assertEqual(getattr(sys, 'get_int_max_str_digits', lambda: None)(), before)


if __name__ == '__main__':
    unittest.main()
