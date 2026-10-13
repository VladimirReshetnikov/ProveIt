"""Valuation arithmetic versus literal integers and independent Jones oracles."""
import random
import unittest
from unittest.mock import patch

from fastunknot import Diagram
from fastunknot.spin_jones import (
    _add_valuations, _multiply_valuation, _normalize_valuation,
    _valuation_terms, spin_jones_exact,
)
from separator_research.graphs import tree_medial
from test_spin_jones import examples


class SpinValuationTests(unittest.TestCase):
    def test_signed_addition_carries_and_tensor_phases_against_literal_integers(self):
        rng = random.Random(26100863)
        for _ in range(2000):
            left = rng.randrange(-(1 << 100), 1 << 100) << rng.randrange(150)
            right = rng.randrange(-(1 << 100), 1 << 100) << rng.randrange(150)
            ls, lm = _normalize_valuation(0, left)
            rs, rm = _normalize_valuation(0, right)
            shift, value = _add_valuations((ls, lm), (rs, rm))
            self.assertEqual(value << shift, left+right)
            self.assertTrue(value == 0 and shift == 0 or value % 2)
            self.assertEqual(_add_valuations((ls, lm), (ls, -lm)), (0, 0))
            phase, tensor_phase = rng.randrange(4), rng.randrange(4)
            terms = tuple((rng.randrange(200), rng.randrange(-4, 5)) for _ in range(4))
            out_phase, out_shift, out_value = _multiply_valuation(
                (phase, ls, lm), _valuation_terms((tensor_phase, terms)))
            # Independent four-coordinate multiplication in Z[z]/(z^4+1).
            lhs = [0]*4
            lhs[out_phase] = out_value << out_shift
            rhs = [0]*4
            for exponent, multiplier in terms:
                degree = phase+tensor_phase
                rhs[degree % 4] += (1 if degree < 4 else -1)*(left << exponent)*multiplier
            self.assertEqual(lhs, rhs)
            self.assertTrue(out_value == 0 and out_shift == 0 or out_value % 2)
        self.assertEqual(_add_valuations((0, 0), (4, -3)), (4, -3))
        self.assertEqual(_add_valuations((4, -3), (0, 0)), (4, -3))
        self.assertEqual(_add_valuations((0, -1), (0, -1)), (1, -1))

    def test_huge_common_valuation_is_not_materialized_in_local_arithmetic(self):
        huge = 1 << 500
        self.assertEqual(_add_valuations((huge, 3), (huge, -3)), (0, 0))
        self.assertEqual(_add_valuations((huge, 3), (huge, 5)), (huge+3, 1))
        self.assertEqual(_multiply_valuation((3, huge, -3),
            _valuation_terms((3, ((huge, 1), (huge+2, -1))))),
            (2, 2*huge, -9))

    def test_modes_preserve_exact_scalars_phases_and_work_on_mirrors_and_orders(self):
        for original, order in examples(35, 26100864):
            for diagram in (original, original.mirror()):
                options = dict(order=order, certify_order=False, include_polynomial=True,
                               outer_face=len(diagram.faces())-1)
                old = spin_jones_exact(diagram, arithmetic='shifted', **options)
                new = spin_jones_exact(diagram, **options)
                for key in old:
                    if key not in ('arithmetic', 'max_frontier_mantissa_bits',
                                   'max_frontier_valuation'):
                        self.assertEqual(old[key], new[key], key)
                self.assertLessEqual(new['max_frontier_mantissa_bits'],
                                     old['max_frontier_mantissa_bits'])
        for arithmetic in ('shifted', 'valuation'):
            result = spin_jones_exact(Diagram.from_pd([]), arithmetic=arithmetic,
                max_states=0, max_transitions=0, include_polynomial=True)
            self.assertEqual(result['jones_polynomial']['coefficients_hex'], [[0, '0x1']])
        for value in (None, True, 'float'):
            with patch('fastunknot.spin_jones.turn_certificate',
                       side_effect=AssertionError('invalid arithmetic started preparation')):
                with self.assertRaisesRegex(ValueError, 'arithmetic'):
                    spin_jones_exact(Diagram.from_pd([]), arithmetic=value)

    def test_tree_frontier_padding_is_removed_without_changing_the_exact_result(self):
        diagram = tree_medial(7)
        old = spin_jones_exact(diagram, arithmetic='shifted', include_polynomial=True)
        new = spin_jones_exact(diagram, include_polynomial=True)
        self.assertEqual(old['scaled_bracket'], new['scaled_bracket'])
        self.assertEqual(old['jones_polynomial'], new['jones_polynomial'])
        self.assertEqual(old['transitions'], new['transitions'])
        self.assertEqual(old['peak_states'], new['peak_states'])
        self.assertGreater(old['max_frontier_mantissa_bits'],
                           30*new['max_frontier_mantissa_bits'])
        self.assertGreater(new['max_frontier_valuation'], 10000)
        # The established bit counter still includes materialized final scalars.
        self.assertEqual(old['max_coefficient_bits'], new['max_coefficient_bits'])


if __name__ == '__main__':
    unittest.main()
