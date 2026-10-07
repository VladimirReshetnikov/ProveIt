"""Exact mathematical, independent-count, API-boundary and optimization regressions."""
import sys
sys.dont_write_bytecode = True
import ast
from fractions import Fraction
import importlib.util
from itertools import product, combinations
from math import comb
from pathlib import Path
import unittest
from unittest.mock import patch

ROOT = Path(__file__).absolute().parents[1]
spec = importlib.util.spec_from_file_location('report288_exact_checks', ROOT / 'companion/exact_checks.py')
e = importlib.util.module_from_spec(spec); sys.modules[spec.name] = e; spec.loader.exec_module(e)


def direct_quadruples(domain, target, weights, images):
    ordinary = respected = 0
    for x, y, z, t in product(weights, repeat=4):
        if domain._add(x, y) == domain._add(z, t):
            mass = weights[x] * weights[y] * weights[z] * weights[t]
            ordinary += mass
            if target._add(images[x], images[y]) == target._add(images[z], images[t]):
                respected += mass
    return e.Energy(ordinary, respected)


class GroupValidationTests(unittest.TestCase):
    def test_finite_infinite_and_mixed_arithmetic(self):
        group = e.Group((0, 3, 2))
        self.assertEqual(group.add((-2, 2, 1), (5, 2, 1)), (3, 1, 0))
        self.assertEqual(group.zero, (0, 0, 0))
        self.assertEqual(e.Group((2, 3)).elements(), tuple(product(range(2), range(3))))
        self.assertEqual(e.Group((1,)).elements(), ((0,),))
        with self.assertRaises(ValueError): group.elements()

    def test_invalid_group_shapes_types_and_sizes(self):
        for moduli in (None, [], [2], (), (2,) * 4, (True,), (2.0,), ('2',), (-1,), (129,), (12, 12), (0, 16, 16)):
            with self.subTest(moduli=moduli), self.assertRaises(ValueError): e.Group(moduli)

    def test_invalid_points_and_coordinate_limit(self):
        group = e.Group((0, 3))
        for point in (None, [0, 1], (0,), (0, 1, 2), (True, 0), (0.0, 0), (0, -1), (0, 3), (4097, 0), (-4097, 0)):
            with self.subTest(point=point), self.assertRaises(ValueError): group.point(point)
        self.assertEqual(group.point((-4096, 2)), (-4096, 2))

    def test_parameters_reject_bool_float_and_out_of_range(self):
        for function in (e.interval_ratio, e.cylinder_ratio, e.binomial_ratio):
            for value in (False, True, 0, -1, 33, 2.0, '2', None):
                with self.subTest(function=function.__name__, value=value), self.assertRaises(ValueError): function(value)
        for value in (True, 0, 33):
            with self.assertRaises(ValueError): e.box_ratio(1, value)
            with self.assertRaises(ValueError): e.box_ratio(value, 1)


class EnergyTests(unittest.TestCase):
    def setUp(self):
        self.Z = e.Group((0,)); self.H = e.Group((3,))

    def test_ordered_pair_buckets_against_independent_fourfold_count(self):
        for modulus, target in product((0, 3, 4), (e.Group((0,)), e.Group((3,)), e.Group((2, 2)))):
            domain = e.Group((modulus,)); size = 3 if modulus in (0, 3) else 4
            weights = {(x,): Fraction(x + 1, 2 + x % 2) for x in range(size)}
            images = {x: ((x[0] * x[0] - 1,) if target.moduli == (0,) else ((x[0] * x[0]) % 3,) if target.moduli == (3,) else (x[0] % 2, x[0] // 2)) for x in weights}
            self.assertEqual(e.energy(domain, target, weights, images), direct_quadruples(domain, target, weights, images))

    def test_affine_map_keeps_all_energy(self):
        domain = e.Group((6,)); target = e.Group((2, 3))
        w = {(j,): j + 1 for j in range(6)}
        measured = e.energy(domain, target, w, {(j,): ((j + 1) % 2, (2 * j + 1) % 3) for j in range(6)})
        self.assertEqual(measured.ratio, 1)

    def test_image_target_torsion_changes_respectedness(self):
        w = {(j,): 1 for j in range(4)}; a = {x: (x[0] % 2,) for x in w}
        self.assertEqual(e.energy(self.Z, e.Group((2,)), w, a).ratio, 1)
        self.assertEqual(e.energy(self.Z, e.Group((0,)), w, a).ratio, e.interval_ratio(2))
        self.assertEqual(e.energy(self.Z, e.Group((3,)), w, a).ratio, e.interval_ratio(2))

    def test_zero_entries_are_ignored_but_images_match_positive_support(self):
        self.assertEqual(e.energy(self.Z, self.H, {(0,): 0, (1,): 2}, {(1,): (2,)}), e.Energy(16, 16))
        with self.assertRaises(ValueError): e.energy(self.Z, self.H, {(0,): 0, (1,): 2}, {(0,): (0,), (1,): (2,)})

    def test_weight_and_mapping_validation(self):
        bad = (None, [], {}, {(0,): 0}, {(0,): -1}, {(0,): 1.0}, {(0,): True}, {(0,): 1 << 256}, {(0,): Fraction(1, 1 << 128)}, {(0, 0): 1})
        for weights in bad:
            with self.subTest(weights=str(weights)[:100]), self.assertRaises(ValueError): e.energy(self.Z, self.H, weights, {(0,): (0,)})
        for images in (None, [], {}, {(1,): (0,)}, {(0,): (3,)}, {(0,): [0]}):
            with self.subTest(images=images), self.assertRaises(ValueError): e.energy(self.Z, self.H, {(0,): 1}, images)
        with self.assertRaises(ValueError): e.energy(None, self.H, {(0,): 1}, {(0,): (0,)})
        with self.assertRaises(ValueError): e.energy(self.Z, None, {(0,): 1}, {(0,): (0,)})

    def test_oversized_images_rejected_before_key_materialization(self):
        images = {(j,): (0,) for j in range(129)}
        with patch.object(e, 'set', side_effect=RuntimeError('key traversal occurred'), create=True):
            with self.assertRaises(ValueError): e.energy(self.Z, self.H, {(0,): 1}, images)

    def test_support_limit_before_pair_enumeration(self):
        weights = {(j,): 1 for j in range(129)}
        with patch.object(e, '_convolution') as conv:
            with self.assertRaises(ValueError): e.convolution(self.Z, weights, {})
            conv.assert_not_called()
        with self.assertRaises(ValueError): e.energy(self.Z, self.H, weights, {x: (0,) for x in weights})

    def test_convolution_exact_and_empty(self):
        self.assertEqual(e.convolution(self.Z, {(0,): 1, (1,): 2}, {(0,): 1, (1,): 2}), {(0,): 1, (1,): 4, (2,): 4})
        self.assertEqual(e.convolution(self.Z, {}, {(0,): 1}), {})
        self.assertEqual(e.convolution(e.Group((2,)), {(0,): 1, (1,): 2}, {(0,): 1, (1,): 2}), {(0,): 5, (1,): 4})

    def test_translation_and_weight_scaling_invariance(self):
        w = {(j,): j + 1 for j in range(4)}; a = {x: (x[0] % 2,) for x in w}
        original = e.energy(self.Z, self.H, w, a)
        translated = {(x[0] - 11,): 3 * v for x, v in w.items()}
        images = {(x[0] - 11,): ((a[x][0] + 2) % 3,) for x in w}
        answer = e.energy(self.Z, self.H, translated, images)
        self.assertEqual(answer, e.Energy(81 * original.ordinary, 81 * original.respected))


class CyclicTests(unittest.TestCase):
    def test_histograms_agree_with_independent_pair_count(self):
        for n in range(1, 9):
            target = e.Group((2, 3)); values = tuple((j * j % 2, (j * j + j) % 3) for j in range(n))
            hist = e.cyclic_histograms(values, target)
            direct = e.energy(e.Group((n,)), target, {(j,): 1 for j in range(n)}, {(j,): values[j] for j in range(n)})
            self.assertEqual(hist['energy'], direct)
            self.assertEqual(hist['Q'][0], n * n)
            self.assertEqual(hist['Q'][1:], tuple(reversed(hist['Q'][1:])))

    def test_small_cycle_bound_for_every_target_two_map(self):
        target = e.Group((2,)); nonaffine = 0
        for n in range(1, 7):
            for tail in product(target.elements(), repeat=n - 1):
                answer = e.cyclic_histograms((target.zero,) + tail, target)
                if not answer['affine']:
                    self.assertLessEqual(answer['energy'].ratio, Fraction(3, 4)); nonaffine += 1
        self.assertEqual(nonaffine, 54)

    def test_histogram_validation(self):
        for values in (None, [], (), ((0,),) * 9, ((True,),), ((2,),)):
            with self.subTest(values=values), self.assertRaises(ValueError): e.cyclic_histograms(values, e.Group((2,)))

    def test_noncyclic_target_normal_form(self):
        target = e.Group((2, 3)); domain = e.Group((6,))
        # d=(0,1), u=(1,0); 3d=0 and eta=2u-d=(0,2) is nonzero.
        values = tuple((j % 2, (j // 2) % 3) for j in range(6))
        measured = e.energy(domain, target, {(j,): 1 for j in range(6)}, {(j,): values[j] for j in range(6)})
        self.assertEqual(measured.ratio, Fraction(3, 4))
        self.assertFalse(e.cyclic_histograms(values, target)['affine'])

    def test_four_point_count_and_target_without_torsion(self):
        w = {(j,): 1 for j in range(4)}
        result = e.energy(e.Group((0,)), e.Group((0,)), w, {(j,): (int(j == 3),) for j in range(4)})
        self.assertEqual(result, e.Energy(44, 32))


class IdentityTests(unittest.TestCase):
    def test_sos_on_negative_and_fractional_inputs(self):
        result = e.parity_sos(e.Group((0,)), {(-3,): Fraction(1, 2), (-2,): Fraction(5, 3), (2,): Fraction(2, 5), (5,): 7})
        self.assertGreater(result['difference_norm'], 0)
        self.assertGreater(result['energy'].ratio, Fraction(3, 4))
        self.assertEqual(4 * result['energy'].respected - 3 * result['energy'].ordinary, result['difference_norm'] + 2 * result['correlation_asymmetry'])

    def test_sos_one_coset_and_full_even_cycle(self):
        for modulus in (0, 2, 4, 6):
            singleton = e.parity_sos(e.Group((modulus,)), {(1,): 2})
            self.assertEqual(singleton['energy'].ratio, 1)
        for n in range(1, 9):
            result = e.parity_sos(e.Group((2 * n,)), {(j,): 1 for j in range(2 * n)})
            self.assertEqual([result[k] for k in ('U', 'V', 'C', 'D')], [n ** 3] * 4)
            self.assertEqual(result['energy'], e.Energy(8 * n ** 3, 6 * n ** 3))

    def test_sos_on_a_product_group(self):
        group = e.Group((4, 3))
        result = e.parity_sos(group, {x: 1 + x[0] + 2 * x[1] for x in group.elements()})
        self.assertGreaterEqual(result['energy'].ratio, Fraction(3, 4))
        with self.assertRaises(ValueError): e.parity_sos(e.Group((3,)), {(0,): 1})

    def test_jensen_quadratic_and_exact_24_failures(self):
        group = e.Group((2, 2)); target = e.Group((2,)); w = dict.fromkeys(group.elements(), 1)
        images = {x: (x[0] * x[1],) for x in w}
        self.assertEqual(e.energy(group, target, w, images), e.Energy(64, 40))
        failing = []
        for points in product(w, repeat=4):
            x, y, z, t = points
            if group._add(x, y) == group._add(z, t) and target._add(images[x], images[y]) != target._add(images[z], images[t]):
                failing.append(points)
        self.assertEqual(len(failing), 24)
        self.assertTrue(all(len(set(points)) == 4 for points in failing))

    def test_box_regression_requires_positive_17(self):
        for m1, m2 in ((1, 1), (1, 2), (2, 2), (3, 5)):
            a, b = m1 * m1, m2 * m2
            self.assertEqual(e.box_ratio(m1, m2) - Fraction(5, 8), Fraction(3 * (8 * a + 8 * b + 17), 8 * (8 * a + 1) * (8 * b + 1)))
            self.assertNotEqual(e.box_ratio(m1, m2) - Fraction(5, 8), Fraction(3 * (8 * a + 8 * b + 1), 8 * (8 * a + 1) * (8 * b + 1)))
        self.assertEqual(e.box_ratio(1, 2), Fraction(23, 33))
        self.assertEqual(e.box_ratio(2, 2), Fraction(79, 121))

    def test_one_side_growth_does_not_give_five_eighths(self):
        self.assertGreater(e.box_ratio(1, 32), Fraction(2, 3))
        self.assertGreater(e.box_ratio(32, 32), Fraction(5, 8))
        self.assertLess(e.box_ratio(32, 32), e.box_ratio(1, 32))

    def test_interval_and_cylinder_samples(self):
        self.assertEqual(e.interval_ratio(1), 1)
        self.assertEqual(e.interval_ratio(2), Fraction(9, 11))
        self.assertEqual(e.cylinder_ratio(1), Fraction(2, 3))
        for m in range(1, 10):
            self.assertEqual(e.cylinder_ratio(m), Fraction(5, 8) + Fraction(3, 64 * m * m + 8))


class QuantitativeTests(unittest.TestCase):
    def test_wrapping_regressions_full_and_near_full(self):
        for n, m, U, C in ((3, 2, 6, 5), (4, 2, 6, 4), (2, 2, 8, 8), (3, 3, 27, 27)):
            result = e.parity_sos(e.Group((2 * n,)), {(j,): 1 for j in range(2 * m)})
            self.assertEqual((result['U'], result['C']), (U, C))
            self.assertEqual(U - C, min(m, n - m))
            self.assertLessEqual(result['energy'].ratio, e.interval_ratio(m))

    def test_six_point_witness_all_six_wrapping_types(self):
        expected = {(4, 2): (48, 32), (2, 2): (64, 40), (4, 4): (126, 94),
                    (2, 4): (168, 120), (4, 6): (114, 82), (2, 6): (152, 104)}
        for (N1, N2), (ordinary, respected) in expected.items():
            domain = e.Group((N1, N2)); target = e.Group((2,))
            w = dict.fromkeys(product(range(2), range(2 if N2 == 2 else 3)), 1)
            a = {x: ((x[0] % 2) * (x[1] % 2),) for x in w}
            measured = e.energy(domain, target, w, a)
            self.assertEqual(measured, e.Energy(ordinary, respected))
            self.assertEqual(measured, direct_quadruples(domain, target, w, a))
            self.assertLessEqual(len(w), 6)
            self.assertLessEqual(measured.ratio, Fraction(47, 63))
        self.assertEqual(Fraction(3, 4) - Fraction(47, 63), Fraction(1, 252))

    def test_exact_support_ceiling_at_and_around_square_boundaries(self):
        for m in range(9, 33):
            eps = Fraction(9, 32 * m * m)
            self.assertEqual(e.indicator_support_bound(eps), 2 * m)
            self.assertEqual(e.indicator_support_bound(eps - Fraction(1, 10 ** 12)), 2 * (m + 1))
            self.assertEqual(e.indicator_support_bound(eps + Fraction(1, 10 ** 12)), 2 * m)
        self.assertEqual(e.indicator_support_bound(100), 6)

    def test_support_epsilon_validation(self):
        for eps in (True, False, 0, -1, 0.1, '1/10', None, Fraction(1, 1 << 128), 1 << 128):
            with self.subTest(epsilon=eps), self.assertRaises(ValueError): e.indicator_support_bound(eps)

    def test_laurent_coefficient_parity_with_negative_exponents(self):
        for A in ((-4,), (-3, -2, 0, 3), (-5, -3, -1, 1), (-2, -1, 0, 1, 4)):
            domain = e.Group((0,)); even = {(j,): 1 for j in A if not j % 2}; odd = {(j,): 1 for j in A if j % 2}
            ee = e.convolution(domain, even, even); oo = e.convolution(domain, odd, odd)
            self.assertTrue(all((ee.get((2 * j,), 0) - oo.get((2 * j,), 0)) % 2 == 1 for j in A))
            result = e.parity_sos(domain, {(j,): 1 for j in A})
            self.assertGreaterEqual(result['energy'].ratio - Fraction(3, 4), Fraction(1, 4 * len(A) ** 2))

    def test_binomial_exact_formula_and_symmetric_correlation(self):
        for m in range(1, 9):
            result = e.parity_sos(e.Group((0,)), {(j,): comb(2 * m, j) for j in range(2 * m + 1)})
            self.assertEqual(result['energy'].ordinary, comb(8 * m, 4 * m))
            self.assertEqual(result['difference_norm'], comb(4 * m, 2 * m))
            self.assertEqual(result['correlation_asymmetry'], 0)
            self.assertEqual(result['energy'].ratio, e.binomial_ratio(m))
        self.assertEqual(e.binomial_ratio(1), Fraction(27, 35))

    def test_finite_folding_with_collisions_and_without_collisions(self):
        for m, N in ((2, 6), (3, 8), (4, 10), (4, 18)):
            weights = {(j,): comb(2 * m, j) for j in range(2 * m + 1)}
            result = e.parity_sos(e.Group((N,)), weights)
            self.assertLessEqual(result['difference_norm'], 2 * comb(4 * m, 2 * m))
            self.assertGreaterEqual(result['energy'].ordinary, comb(8 * m, 4 * m))
            self.assertLessEqual(result['energy'].ratio - Fraction(3, 4), Fraction(1, 2 * 4 ** m))
            if N > 4 * m:
                self.assertEqual(result['energy'].ratio, e.binomial_ratio(m))

    def test_indicator_lower_bound_is_not_a_weighted_claim(self):
        m = 5; s = 2 * m + 1
        self.assertLess(e.binomial_ratio(m) - Fraction(3, 4), Fraction(1, 4 * s * s))


class ScopeAndModeTests(unittest.TestCase):
    def test_runtime_guards_have_no_optimization_removable_assertions(self):
        source = (ROOT / 'companion/exact_checks.py').read_text()
        self.assertFalse(any(isinstance(node, ast.Assert) for node in ast.walk(ast.parse(source))))
        self.assertNotIn('set_int_max_str_digits(', source)
        with self.assertRaisesRegex(RuntimeError, 'sentinel'): e.require(False, 'sentinel')

    def test_command_line_refuses_arguments_before_work(self):
        for argv in (['--help'], ['1000000'], (), None):
            with patch.object(e, 'run_checks') as run:
                if argv is None:
                    with patch.object(e.sys, 'argv', ['checks.py', '--unexpected']):
                        with self.assertRaises(ValueError): e.main(argv)
                else:
                    with self.assertRaises(ValueError): e.main(argv)
                run.assert_not_called()

    def test_fixed_diagnostic_components(self):
        self.assertEqual(e.check_sos()['cases'], 80)
        self.assertEqual(e.check_jensen()['weighted_cases'], 255)
        self.assertEqual(e.check_boxes()['excess_constant'], 17)
        support = e.check_wrapping_and_support()
        self.assertEqual(support['wrapped_intervals'], 136)
        self.assertEqual(support['jensen_support_upper'], 6)
        self.assertEqual(support['jensen_ratio_upper'], '47/63')
        self.assertEqual(len(support['six_wrapping_types']), 6)
        self.assertEqual(e.check_indicator_lower_bound()['cases'], 1023)
        self.assertEqual(e.check_binomial()['finite_cases'], 180)


if __name__ == '__main__':
    unittest.main()
