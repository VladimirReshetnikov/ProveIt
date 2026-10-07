"""Exact independent oracles, finite structural classification, and strict API tests."""
import ast
from fractions import Fraction
import importlib.util
from itertools import product
import json
from pathlib import Path
import subprocess
import sys
import unittest

sys.dont_write_bytecode = True
ROOT = Path(__file__).absolute().parents[1]
SPEC = importlib.util.spec_from_file_location('report290_exact_checks', ROOT / 'companion/exact_checks.py')
e = importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name] = e
SPEC.loader.exec_module(e)


def independent_classification(domain, target, mapping):
    """Search all characters to C2, without using the translation subgroup."""
    points = domain.elements()
    beta = mapping[domain.zero]
    b = {x: target._sub(mapping[x], beta) for x in points}
    if all(b[domain._add(x, y)] == target._add(b[x], b[y]) for x, y in product(points, repeat=2)):
        return 'affine', points
    for coefficients in product(range(2), repeat=len(domain.moduli)):
        if not any(coefficients) or any(c and m % 2 for c, m in zip(coefficients, domain.moduli)):
            continue
        kernel = tuple(x for x in points if sum(c * coordinate for c, coordinate in zip(coefficients, x)) % 2 == 0)
        t = next(x for x in points if x not in kernel)
        if (all(b[domain._add(x, y)] == target._add(b[x], b[y]) for x, y in product(kernel, repeat=2))
                and all(b[domain._add(t, x)] == target._add(b[t], b[x]) for x in kernel)
                and target._scale(2, b[t]) != b[domain._scale(2, t)]):
            return 'index_two', kernel
    return 'other', None


class GroupTests(unittest.TestCase):
    def test_mixed_arithmetic(self):
        group = e.Group((0, 3, 2))
        self.assertEqual(group.add((-2, 2, 1), (5, 2, 1)), (3, 1, 0))
        self.assertEqual(group.sub((-2, 2, 1), (5, 2, 1)), (-7, 0, 0))
        self.assertEqual(group.scale(-2, (-2, 2, 1)), (4, 2, 0))
        self.assertEqual(group.zero, (0, 0, 0))
        self.assertFalse(group.finite)

    def test_finite_elements_and_trivial_factor(self):
        self.assertEqual(e.Group((2, 3)).elements(), tuple(product(range(2), range(3))))
        self.assertEqual(e.Group((1,)).elements(), ((0,),))
        self.assertEqual(len(e.Group((8, 8)).elements()), 64)
        with self.assertRaises(ValueError):
            e.Group((0, 2)).elements()

    def test_invalid_group_inputs(self):
        for moduli in (None, [], (), [2], (True,), (2.0,), ('2',), (-1,), (129,), (2,) * 5, (16, 16)):
            with self.subTest(moduli=moduli), self.assertRaises(ValueError):
                e.Group(moduli)

    def test_invalid_coordinates(self):
        group = e.Group((0, 3))
        for point in (None, [0, 0], (0,), (0, 0, 0), (True, 0), (0.0, 0), (0, -1), (0, 3), (4097, 0)):
            with self.subTest(point=point), self.assertRaises(ValueError):
                group.point(point)
        self.assertEqual(group.point((-4096, 2)), (-4096, 2))

    def test_scale_rejects_nonexact_or_unbounded(self):
        for n in (True, 1.0, '1', 4097, -4097):
            with self.subTest(n=n), self.assertRaises(ValueError):
                e.Group((0,)).scale(n, (1,))


class EnergyTests(unittest.TestCase):
    def test_rational_histogram_and_literal_counts(self):
        self.assertEqual(e.check_energy_oracles()['weighted_cases'], 27)

    def test_independent_integer_quadruples(self):
        for n in (2, 3, 4):
            domain, target = e.Group((n,)), e.Group((5,))
            points = domain.elements()
            images = {x: ((x[0] * x[0]) % 5,) for x in points}
            ordinary = respected = 0
            for x, y, z, t in product(range(n), repeat=4):
                if (x + y - z - t) % n == 0:
                    ordinary += 1
                    respected += (x * x + y * y - z * z - t * t) % 5 == 0
            result = e.energy(domain, target, dict.fromkeys(points, 1), images)
            self.assertEqual(result, e.Energy(ordinary, respected))
            self.assertEqual(result.respected, sum(e.derivative_masses(domain, target, images).values()))

    def test_repetitions_and_weight_scale(self):
        domain = e.Group((2,))
        target = e.Group((0,))
        images = {(0,): (0,), (1,): (1,)}
        base = e.energy(domain, target, {(0,): 1, (1,): 1}, images)
        self.assertEqual(base, e.Energy(8, 6))
        scaled = e.energy(domain, target, {(0,): Fraction(3, 2), (1,): Fraction(3, 2)}, images)
        self.assertEqual(scaled.ordinary, base.ordinary * Fraction(3, 2) ** 4)
        self.assertEqual(scaled.ratio, Fraction(3, 4))

    def test_zero_weights_are_removed(self):
        group = e.Group((0,))
        self.assertEqual(e.energy(group, group, {(0,): 0, (1,): 2}, {(1,): (0,)}), e.Energy(16, 16))
        with self.assertRaises(ValueError):
            e.energy(group, group, {(0,): 0, (1,): 2}, {(0,): (0,), (1,): (0,)})

    def test_bad_weights_and_image_keys(self):
        group = e.Group((0,))
        for weights in (None, [], {}, {(0,): 0}, {(0,): -1}, {(0,): True}, {(0,): 1.0},
                        {(0,): 1 << 128}, {(0,): Fraction(1, 1 << 64)}, {(0, 0): 1},
                        {(j,): 1 for j in range(129)}):
            with self.subTest(weights=str(weights)[:60]), self.assertRaises(ValueError):
                e.energy(group, group, weights, {(0,): (0,)})
        for images in (None, [], {}, {(1,): (0,)}, {(0,): [0]}, {(0,): (True,)}, {(0,): (4097,)}):
            with self.subTest(images=images), self.assertRaises(ValueError):
                e.energy(group, group, {(0,): 1}, images)
        with self.assertRaises(ValueError):
            e.energy(None, group, {(0,): 1}, {(0,): (0,)})

    def test_literal_oracle_hard_limit(self):
        group = e.Group((9,))
        points = group.elements()
        with self.assertRaises(ValueError):
            e.direct_energy(group, group, dict.fromkeys(points, 1), {x: x for x in points})

    def test_energy_value_validation(self):
        for args in ((0, 0), (-1, 0), (1, -1), (1, 2), (True, 1), (1.0, 1), (1, True)):
            with self.subTest(args=args), self.assertRaises(ValueError):
                e.Energy(*args)

    def test_c5_all_subset_minima(self):
        data = e.check_c5_integer_example()
        self.assertEqual(data['subsets'], 31)
        self.assertEqual(data['minimum_by_size'], {1: Fraction(1), 2: Fraction(1), 3: Fraction(15, 19),
                                                 4: Fraction(9, 13), 5: Fraction(17, 25)})
        self.assertFalse(data['weighted_infimum_claimed'])

    def test_full_domain_validation_and_subset_limit(self):
        for function in (e.indicator_minimum, e.derivative_masses, e.condition_p, e.classify_finite):
            with self.subTest(function=function.__name__), self.assertRaises(ValueError):
                function(e.Group((0,)), e.Group((2,)), {(0,): (0,)})
            with self.subTest(function=function.__name__), self.assertRaises(ValueError):
                function(e.Group((2,)), e.Group((2,)), {(0,): (0,)})
        group = e.Group((9,))
        with self.assertRaises(ValueError):
            e.indicator_minimum(group, group, {x: x for x in group.elements()})


class ClassificationTests(unittest.TestCase):
    def test_independent_character_search(self):
        cases = 0
        for factors in ((1,), (2,), (3,), (4,), (2, 2), (2, 3)):
            domain = e.Group(factors)
            points = domain.elements()
            for modulus in (2, 3):
                target = e.Group((modulus,))
                for tail in product(range(modulus), repeat=len(points) - 1):
                    images = dict(zip(points, ((v,) for v in (0,) + tail)))
                    actual = e.classify_finite(domain, target, images)
                    expected, kernel = independent_classification(domain, target, images)
                    self.assertEqual(actual['kind'], expected)
                    if kernel is not None:
                        self.assertEqual(actual['kernel'], kernel)
                    cases += 1
        self.assertEqual(cases, 365)

    def test_nonextendable_kernel_homomorphism(self):
        domain, target = e.Group((4,)), e.Group((2,))
        images = {(j,): (j // 2,) for j in range(4)}
        data = e.classify_finite(domain, target, images)
        self.assertEqual(data['kind'], 'index_two')
        self.assertEqual(data['kernel'], ((0,), (2,)))
        self.assertEqual(data['homomorphism'][(2,)], (1,))
        self.assertEqual(data['eta'], (1,))
        # Every hom C4 -> C2 sends 2 to 0, so this kernel hom cannot extend.
        self.assertTrue(all(target.scale(2, v) == target.zero for v in target.elements()))
        self.assertEqual(e.indicator_minimum(domain, target, images)['ratio'], Fraction(3, 4))

    def test_curvature_kernel_with_nonzero_translation(self):
        domain, target = e.Group((6,)), e.Group((6,))
        images = {(j,): ((j + j % 2 + 3) % 6,) for j in range(6)}
        result = e.classify_finite(domain, target, images)
        self.assertEqual(result['kind'], 'index_two')
        self.assertEqual(result['beta'], (3,))
        self.assertEqual(result['eta'], (2,))
        for x in domain.elements():
            curvature = target.add(target.sub(images[domain.scale(2, x)], target.scale(2, images[x])), images[domain.zero])
            self.assertEqual(curvature, (0,) if x in result['kernel'] else (4,))
            self.assertEqual(curvature, result['curvature'][x])

    def test_infinite_target_endpoint(self):
        domain, target = e.Group((4,)), e.Group((0,))
        images = {(j,): (7 + j % 2,) for j in range(4)}
        result = e.classify_finite(domain, target, images)
        self.assertEqual(result['kind'], 'index_two')
        self.assertEqual(result['eta'], (2,))
        self.assertEqual(result['curvature'][(1,)], (-2,))

    def test_zero_defect_affine_and_other(self):
        domain, target = e.Group((4,)), e.Group((4,))
        self.assertEqual(e.classify_finite(domain, target, {(j,): ((j + 2) % 4,) for j in range(4)})['kind'], 'affine')
        values = (0, 0, 0, 1)
        self.assertEqual(e.classify_finite(domain, target, {(j,): (values[j],) for j in range(4)})['kind'], 'other')

    def test_P_automatic_order_two_and_explicit_failure(self):
        domain, target = e.Group((2,)), e.Group((0,))
        self.assertTrue(e.condition_p(domain, target, {(0,): (7,), (1,): (-13,)})['holds'])
        domain = e.Group((5,))
        images = {(j,): (j,) for j in range(5)}
        data = e.condition_p(domain, target, images)
        self.assertFalse(data['holds'])
        x, h = data['witness']
        values = [images[domain.add(x, domain.scale(j, h))][0] for j in range(4)]
        self.assertNotEqual(values[3] - values[2] - values[1] + values[0], 0)

    def test_high_full_energy_is_not_a_hereditary_bound(self):
        domain, target = e.Group((16,)), e.Group((2,))
        images = {x: (int(x == domain.zero),) for x in domain.elements()}
        self.assertEqual(e.classify_finite(domain, target, images)['kind'], 'other')
        full = e.energy(domain, target, dict.fromkeys(images, 1), images)
        self.assertEqual(full.ratio, Fraction(407, 512))
        self.assertGreater(full.ratio, Fraction(3, 4))
        subset = tuple((j,) for j in (0, 4, 8, 12))
        witness = e.energy(domain, target, dict.fromkeys(subset, 1), {x: images[x] for x in subset})
        self.assertEqual(witness.ratio, Fraction(5, 8))

    def test_elementary_quadratic_sharp_example(self):
        domain, target = e.Group((2, 2)), e.Group((2,))
        images = {x: (x[0] * x[1],) for x in domain.elements()}
        self.assertEqual(e.classify_finite(domain, target, images)['kind'], 'other')
        self.assertTrue(e.condition_p(domain, target, images)['holds'])
        self.assertEqual(e.indicator_minimum(domain, target, images)['ratio'], Fraction(5, 8))


class PlaneGridBoxTests(unittest.TestCase):
    def test_plane_formula_three_categories(self):
        examples = ((e.Group((2,)), ((0,), (1,), (0,), (1,)), 64, 3),
                    (e.Group((0,)), ((0,), (1,), (0,), (1,)), 48, 2),
                    (e.Group((2,)), ((0,), (0,), (0,), (1,)), 40, 0))
        for target, values, respected, partitions in examples:
            data = e.plane_data(target, values)
            self.assertEqual(data['respected'], respected)
            self.assertEqual(data['partitions'], partitions)
            domain = e.Group((2, 2))
            mapping = dict(zip(domain.elements(), values))
            self.assertEqual(e.direct_energy(domain, target, dict.fromkeys(mapping, 1), mapping).respected, respected)

    def test_plane_input_limits(self):
        target = e.Group((2,))
        for values in (None, [], ((0,),) * 3, ((0,),) * 5, ((0,), (0,), (0,), (2,))):
            with self.subTest(values=values), self.assertRaises(ValueError):
                e.plane_data(target, values)
        with self.assertRaises(ValueError):
            e.affine_planes(e.Group((4,)))

    def test_affine_plane_enumeration(self):
        self.assertEqual(len(e.affine_planes(e.Group((2,)))), 0)
        self.assertEqual(len(e.affine_planes(e.Group((2, 2)))), 1)
        self.assertEqual(len(e.affine_planes(e.Group((2, 2, 2)))), 14)
        self.assertEqual(len(e.affine_planes(e.Group((2, 2, 2, 2)))), 140)

    def test_order_four_model_and_reciprocal_averages(self):
        result = e.check_order_four_obstruction()
        self.assertEqual(result['s'], (1,))
        self.assertEqual(result['P_equations'], 4096)
        self.assertEqual(result['energy'], e.Energy(262144, 71680))
        self.assertEqual(e.obstruction_average(2), Fraction(5, 8))
        self.assertEqual(e.obstruction_average(4), Fraction(11, 32))
        self.assertEqual(len(result['respected_difference_classes']), 16)

    def test_grid_derivatives_on_genuine_model(self):
        domain, target = e.Group((8, 8)), e.Group((4,))
        def value(i, j):
            m, epsilon = divmod(i, 2)
            n, delta = divmod(j, 2)
            return (m * delta - n * epsilon + 2 * m * n) % 4
        images = {(i, j): (value(i, j),) for i, j in domain.elements()}
        self.assertEqual(e.grid_obstruction(domain, target, images, (1, 0), (0, 1)), (1,))
        self.assertEqual(e.grid_obstruction(domain, target, images, (0, 1), (1, 0)), (3,))
        for i, j in product(range(-8, 9), repeat=2):
            self.assertEqual((value(i + 2, j) - value(i, j)) % 4, j % 4)
            self.assertEqual((value(i, j + 2) - value(i, j)) % 4, -i % 4)
            self.assertEqual(value(i + 8, j), value(i, j))
            self.assertEqual(value(i, j + 8), value(i, j))

    def test_box_counts_against_pair_histograms(self):
        domain, target = e.Group((0, 4)), e.Group((2,))
        for n in (0, 1, 2, 4):
            points = tuple(product(range(-n, n + 1), range(4)))
            images = {x: ((x[0] * x[1]) % 2,) for x in points}
            data = e.box_quotient_counts(n)
            self.assertEqual(data['energy'], e.energy(domain, target, dict.fromkeys(points, 1), images))
            self.assertEqual(sum(data['patterns'].values()), data['energy'].ordinary)
            self.assertEqual(sum(data['difference_counts'].values()), data['energy'].ordinary)
            self.assertEqual(len(data['patterns']), 64)

    def test_box_patterns_and_exact_spreads(self):
        rows = e.check_box_lifting()['rows']
        self.assertEqual([r['energy'].ratio for r in rows], [Fraction(13, 19), Fraction(11, 17), Fraction(103, 163), Fraction(121, 193)])
        self.assertTrue(all(r['smallest_pattern_lifts'] > 0 for r in rows))
        self.assertTrue(all(a['relative_pattern_spread'] > b['relative_pattern_spread'] for a, b in zip(rows, rows[1:])))
        self.assertEqual(e.box_energy(0, 5, 8), 125)
        self.assertEqual(e.box_energy(2, 1, 1), 19 ** 2)

    def test_counting_hard_limits(self):
        for n in (-1, 9, True, 1.0, '1', None):
            with self.subTest(n=n), self.assertRaises(ValueError):
                e.box_quotient_counts(n)
        for args in ((-1, 1, 0), (5, 1, 0), (0, 0, 0), (0, 129, 0), (0, 1, 33), (True, 1, 0)):
            with self.subTest(args=args), self.assertRaises(ValueError):
                e.box_energy(*args)
        for q in (0, 1, 3, 8, True, 2.0, None):
            with self.subTest(q=q), self.assertRaises(ValueError):
                e.obstruction_average(q)
        for args in ((9, 2), (1, 10), (True, 2), (8, 9)):
            with self.subTest(args=args), self.assertRaises(ValueError):
                e._bounded_enumeration(*args)


class SharpCertificateTests(unittest.TestCase):
    def test_eight_exact_no_wrap_histograms(self):
        expected = ((53, 28, 4), (98, 48, 0), (90, 40, 0), (98, 48, 0),
                    (204, 128, 12), (321, 168, 0), (139, 72, 0), (470, 200, 0))
        for row, counts in enumerate(expected, 1):
            c, subset = e.branch_data(row)
            pairs = e.coefficient_histogram(c, subset)
            direct = e.coefficient_histogram(c, subset, method='quadruples')
            self.assertEqual(pairs, direct)
            self.assertEqual(tuple(sum(count for (z, t), count in pairs.items() if abs(t) == j)
                                   for j in range(3)), counts)
            self.assertTrue(all(z == 0 and abs(t) <= 2 for z, t in pairs))
            self.assertEqual(e.branch_certificate(row)['energy'].ratio, Fraction(e.NO_WRAP_MAXIMA[row - 1]))

    def test_all_72_histograms_and_31_positive_wrap_polynomials(self):
        expected_polynomials = {(r, n): dict(p) for r, n, p in e.POSITIVE_WRAP_POLYNOMIALS}
        self.assertEqual(len(expected_polynomials), 31)
        for row, n in product(range(1, 9), range(10, 19)):
            certificate = e.branch_certificate(row, n)
            histogram = certificate['histogram']
            self.assertEqual(certificate['positive_wrap'], expected_polynomials.get((row, n), {}))
            self.assertTrue(all(histogram[(-z, -t)] == count for (z, t), count in histogram.items()))
            polynomial = certificate['positive_wrap']
            self.assertTrue(not polynomial or max(polynomial) - min(polynomial) <= 3)
            self.assertEqual(certificate['energy'].ratio, e.WRAP_MAXIMA[row - 1][n - 10])
            self.assertLessEqual(certificate['energy'].ratio, Fraction(59, 84))
        self.assertLess(Fraction(59, 84), Fraction(19, 27))

    def test_retained_slope_changes_realized_energy(self):
        c, subset = e.branch_data(8)
        first = e.realized_pair_energy(c, subset, 10, 3, 0)
        second = e.realized_pair_energy(c, subset, 10, 3, 1)
        self.assertNotEqual(first.respected, second.respected)
        histogram = e.coefficient_histogram(c, subset, 10)
        self.assertEqual(first.respected, e.symbolic_numerator(histogram, 3, 0))
        self.assertEqual(second.respected, e.symbolic_numerator(histogram, 3, 1))

    def test_general_q_h_range_and_large_order_reduction(self):
        for row, n in product(range(1, 9), range(10, 19)):
            c, subset = e.branch_data(row)
            histogram = e.coefficient_histogram(c, subset, n)
            result = e.symbolic_maximum(histogram)
            m = result['M']
            self.assertEqual(result['symbolic_patterns'], 2 * m * (2 * m + 1))
            realized = []
            for q in (*range(2, 2 * m + 1), None):
                for h in range(-m, m + 1):
                    pair_energy = e.realized_pair_energy(c, subset, n, q, h)
                    self.assertEqual(pair_energy.respected, e.symbolic_numerator(histogram, q, h))
                    realized.append(pair_energy.respected)
            self.assertEqual(max(realized), result['energy'].respected)
            for h in range(-m, m + 1):
                for q in (2 * m + 1, 2 * m + 2, 4096):
                    self.assertEqual(e.symbolic_numerator(histogram, q, h),
                                     e.symbolic_numerator(histogram, None, h))

    def test_three_torsion_case_numerators(self):
        certificate = e.branch_certificate(6, 10)
        d = certificate['zero_wrap']
        p = certificate['positive_wrap']
        w2 = max(sum(count for t, count in p.items() if t % 2 == r) for r in range(2))
        w3 = max(sum(count for t, count in p.items() if t % 3 == r) for r in range(3))
        winf = max(p.values())
        self.assertEqual(certificate['three_numerators'],
                         (d[0] + 2 * d.get(2, 0) + 2 * w2, d[0] + 2 * w3, d[0] + 2 * winf))
        self.assertEqual(certificate['energy'], e.Energy(657, 413))

    def test_invalid_branch_and_count_inputs(self):
        for row in (0, 9, True, 1.0, '1', None):
            with self.subTest(row=row), self.assertRaises(ValueError):
                e.branch_certificate(row, 10)
        for modulus in (0, 1, 9, 19, True, 10.0, '10'):
            with self.subTest(modulus=modulus), self.assertRaises(ValueError):
                e.branch_certificate(1, modulus)
        for c, subset in ((None, (0,)), ([], (0,)), ((), (0,)), ((0,) * 11, (0,)),
                          ((True,), (0,)), ((4,), (0,)), ((-1,), (0,)), ((0,), []),
                          ((0,), ()), ((0,), (0, 0)), ((0, 1), (1, 0)),
                          ((0,), (1,)), ((0,), (True,)), ((0,), (0.0,))):
            with self.subTest(coefficients=c, subset=subset), self.assertRaises(ValueError):
                e.coefficient_histogram(c, subset)
        for method in (None, True, 'direct', ''):
            with self.subTest(method=method), self.assertRaises(ValueError):
                e.coefficient_histogram((0,), (0,), method=method)

    def test_invalid_defects_orders_and_slopes(self):
        invalid = (None, {}, [], {(0, 0): True}, {(0, 0): 10001}, {(0, 0): 0},
                   {(False, 0): 1}, {(0, True): 1}, {(0, 0): 1, (2, 0): 1},
                   {(0, 0): 1, (0, 7): 1}, {(0, 0): 1, (1, 1): 1},
                   {(1, 0): 1, (-1, 0): 1}, {(0, 0): 9999, (1, 1): 1, (-1, -1): 1})
        for histogram in invalid:
            with self.subTest(histogram=histogram), self.assertRaises(ValueError):
                e.symbolic_maximum(histogram)
        hist = e.coefficient_histogram(*e.branch_data(1), 10)
        for q in (0, 1, True, 2.0, 'infinity', 4097):
            with self.subTest(q=q), self.assertRaises(ValueError):
                e.symbolic_numerator(hist, q, 0)
        for h in (True, 0.0, '0', -3, 3):
            with self.subTest(h=h), self.assertRaises(ValueError):
                e.symbolic_numerator(hist, 2, h)
        with self.assertRaises(ValueError):
            e.three_case_maximum({(0, 0): 1, (0, 3): 1, (0, -3): 1})
        with self.assertRaises(ValueError):
            e.three_case_maximum({(0, 0): 1, (1, 0): 1, (-1, 0): 1, (1, 4): 1, (-1, -4): 1})

    def test_zero_coefficient_histogram(self):
        histogram = e.coefficient_histogram((0, 0), (0, 1), 10)
        result = e.symbolic_maximum(histogram)
        self.assertEqual(result['M'], 0)
        self.assertEqual(result['symbolic_patterns'], 1)
        self.assertEqual(result['energy'].ratio, 1)
        self.assertEqual(e.three_case_maximum(histogram)['energy'], result['energy'])

    def test_c3_sharpness_and_weighted_distinction(self):
        result = e.check_c3_sharp_indicator()
        self.assertEqual([r['energy'].ratio for r in result['subsets']], [Fraction(1)] * 6 + [Fraction(19, 27)])
        self.assertEqual(result['indicator']['subsets'], 7)
        self.assertEqual(result['weighted_test'].ratio, Fraction(467, 683))
        self.assertLess(result['weighted_test'].ratio, Fraction(19, 27))
        self.assertFalse(result['weighted_sharpness_claimed'])

    def test_small_cyclic_case_arithmetic(self):
        rows = e.check_small_order_arithmetic()['rows']
        self.assertEqual([r['full_indicator_bound'] for r in rows], [Fraction(33, 49), Fraction(11, 16), Fraction(19, 27)])
        self.assertEqual([r['arithmetic_cut_ratio'] for r in rows], [Fraction(33, 49), Fraction(43, 64), Fraction(163, 243)])


class SummaryAndSafetyTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        command = [sys.executable, '-B', str(ROOT / 'companion/exact_checks.py')]
        cls.normal = subprocess.run(command, check=True, capture_output=True, text=True, timeout=45)
        cls.optimized = subprocess.run([sys.executable, '-O', '-B', str(ROOT / 'companion/exact_checks.py')],
                                       check=True, capture_output=True, text=True, timeout=45)
        cls.summary = json.loads(cls.normal.stdout)

    def test_normal_and_optimized_json_identical(self):
        self.assertEqual(self.normal.stdout, self.optimized.stdout)
        self.assertEqual(self.normal.stderr, '')
        self.assertEqual(self.optimized.stderr, '')
        self.assertEqual(self.summary['report'], 290)
        self.assertEqual(self.summary['status'], 'passed')
        self.assertEqual(self.summary['schema_version'], 2)
        self.assertEqual(self.summary['symbolic_certificates']['finite_wrap_cases'], 72)

    def test_declared_exhaustive_counts(self):
        self.assertEqual(self.summary['cyclic']['normalized_maps_total'], 138516)
        self.assertEqual(self.summary['cyclic']['canonical_classifications'], 222)
        self.assertEqual(self.summary['elementary_two']['plane_normalized_maps'], 1871)
        self.assertEqual(self.summary['elementary_two']['gluing_normalized_maps'], 35083)
        self.assertEqual(self.summary['mixed_classification']['normalized_maps_total'], 1299)

    def test_small_cyclic_exact_maxima(self):
        rows = self.summary['cyclic']['rows']
        self.assertEqual([row['largest_full_ratio_outside_P'] for row in rows],
                         [None, None, '19/27', '11/16', '17/25', '19/27'])
        self.assertEqual(sum(row['normalized_maps'] for row in rows), 138516)

    def test_global_gluing_counts(self):
        rows = self.summary['elementary_two']['gluing_rows']
        self.assertEqual([(r['affine'], r['index_two'], r['bad_plane']) for r in rows],
                         [(8, 0, 120), (1, 14, 2172), (8, 56, 16320), (64, 0, 16320)])

    def test_no_assert_only_safety_or_float_literals(self):
        tree = ast.parse((ROOT / 'companion/exact_checks.py').read_text())
        self.assertFalse(any(isinstance(node, ast.Assert) for node in ast.walk(tree)))
        self.assertFalse(any(isinstance(node, ast.Constant) and type(node.value) is float for node in ast.walk(tree)))
        with self.assertRaises(RuntimeError):
            e.require(False, 'deliberate test')

    def test_optimized_invalid_inputs_still_rejected(self):
        script = """
import sys
sys.path.insert(0, sys.argv[1])
from companion import exact_checks as e
bad = [lambda:e.Group((True,)),lambda:e.Group((16,16)),lambda:e.box_quotient_counts(9),
       lambda:e.obstruction_average(2.0),lambda:e._bounded_enumeration(8,9),
       lambda:e.branch_certificate(True),lambda:e.branch_certificate(1,9),
       lambda:e.coefficient_histogram((0,)*11,(0,)),
       lambda:e.symbolic_numerator({(0,0):1},True,0)]
for case in bad:
    try: case()
    except ValueError: pass
    else: raise RuntimeError('invalid input accepted')
try: e.require(False,'expected')
except RuntimeError: pass
else: raise RuntimeError('runtime guard disabled')
print('passed')
"""
        result = subprocess.run([sys.executable, '-O', '-B', '-c', script, str(ROOT)],
                                check=True, capture_output=True, text=True, timeout=10)
        self.assertEqual(result.stdout, 'passed\n')

    def test_cli_unknown_arguments_fail_before_checks(self):
        for argument in ('--quick', '--max-maps=999999999999', 'extra'):
            result = subprocess.run([sys.executable, '-B', str(ROOT / 'companion/exact_checks.py'), argument],
                                    capture_output=True, text=True, timeout=10)
            self.assertEqual(result.returncode, 2)
            self.assertEqual(result.stdout, '')

    def test_jsonable_exact_data_and_rejection(self):
        self.assertEqual(e.jsonable(Fraction(17, 25)), '17/25')
        self.assertEqual(e.jsonable({(1,): Fraction(3, 4)}), [{'key': [1], 'value': '3/4'}])
        with self.assertRaises(ValueError):
            e.jsonable(0.5)


if __name__ == '__main__':
    unittest.main()
