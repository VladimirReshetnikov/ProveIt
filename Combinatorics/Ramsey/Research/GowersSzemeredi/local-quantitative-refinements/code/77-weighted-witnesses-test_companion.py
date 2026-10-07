"""Independent exact counts, algebraic identities, lattice saturation and API tests."""
import ast
from fractions import Fraction
import importlib.util
from itertools import product
import json
from math import comb
from pathlib import Path
import subprocess
import sys
import unittest
from unittest.mock import patch

sys.dont_write_bytecode = True
ROOT = Path(__file__).absolute().parents[1]
spec = importlib.util.spec_from_file_location('report289_exact_checks', ROOT / 'companion/exact_checks.py')
e = importlib.util.module_from_spec(spec)
sys.modules[spec.name] = e
spec.loader.exec_module(e)


def direct_quadruples(domain, target, weights, images):
    ordinary = respected = Fraction(0)
    for x, y, z, t in product(weights, repeat=4):
        if domain._add(x, y) != domain._add(z, t):
            continue
        mass = weights[x] * weights[y] * weights[z] * weights[t]
        ordinary += mass
        if target._add(images[x], images[y]) == target._add(images[z], images[t]):
            respected += mass
    return e.Energy(ordinary, respected)


def coordinates_in_independent_basis(basis, vector):
    """Independent rational row elimination, used only to test Z-kernel saturation."""
    if not basis:
        return () if not any(vector) else None
    k = len(basis)
    A = [[Fraction(basis[j][i]) for j in range(k)] + [Fraction(vector[i])]
         for i in range(len(vector))]
    pivot_row = 0
    for column in range(k):
        row = next((r for r in range(pivot_row, len(A)) if A[r][column]), None)
        if row is None:
            raise RuntimeError('dependent test basis')
        A[pivot_row], A[row] = A[row], A[pivot_row]
        scale = A[pivot_row][column]
        A[pivot_row] = [value / scale for value in A[pivot_row]]
        for r in range(len(A)):
            if r == pivot_row:
                continue
            scale = A[r][column]
            A[r] = [a - scale * b for a, b in zip(A[r], A[pivot_row])]
        pivot_row += 1
    if any(all(not a for a in row[:-1]) and row[-1] for row in A):
        return None
    return tuple(A[j][-1] for j in range(k))


class GroupTests(unittest.TestCase):
    def test_mixed_arithmetic_and_elements(self):
        G = e.Group((0, 3, 2))
        self.assertEqual(G.add((-2, 2, 1), (5, 2, 1)), (3, 1, 0))
        self.assertEqual(G._sub((-2, 2, 1), (5, 2, 1)), (-7, 0, 0))
        self.assertEqual(G._neg((-2, 2, 1)), (2, 1, 1))
        self.assertEqual(G.zero, (0, 0, 0))
        self.assertEqual(e.Group((2, 3)).elements(), tuple(product(range(2), range(3))))
        self.assertEqual(e.Group((1,)).elements(), ((0,),))
        with self.assertRaises(ValueError):
            G.elements()

    def test_group_rejects_invalid_inputs(self):
        for moduli in (None, [], (), [2], (True,), (2.0,), ('2',), (-1,), (129,), (2,) * 5, (16, 16)):
            with self.subTest(moduli=moduli), self.assertRaises(ValueError):
                e.Group(moduli)

    def test_points_must_be_canonical_exact_and_bounded(self):
        G = e.Group((0, 3))
        for point in (None, [0, 0], (0,), (0, 0, 0), (True, 0), (0.0, 0), (0, -1), (0, 3), (4097, 0)):
            with self.subTest(point=point), self.assertRaises(ValueError):
                G.point(point)
        self.assertEqual(G.point((-4096, 2)), (-4096, 2))

    def test_general_parity_and_odd_cyclic_obstruction(self):
        G = e.Group((0, 4, 3))
        self.assertEqual(e.parity_character(G, (1, 1, 0)), (1, 1, 0))
        self.assertEqual(e.parity_character(e.Group((3,)), (0,)), (0,))
        for coefficients in ((0, 0, 1), (True, 0, 0), (2, 0, 0), [1, 0, 0], (1,), None):
            if coefficients is None:
                with self.assertRaises(ValueError):
                    e.parity_character(e.Group((3,)))
            else:
                with self.subTest(coefficients=coefficients), self.assertRaises(ValueError):
                    e.parity_character(G, coefficients)
        with self.assertRaises(ValueError):
            e.parity_sos(e.Group((3,)), {(0,): 1})


class QuadraticTests(unittest.TestCase):
    def test_exact_field_arithmetic_and_inverse(self):
        for d in (2, 6):
            r = e.Quadratic(0, 1, d)
            self.assertEqual(r * r, d)
            self.assertEqual((3 + 2 * r) * (3 - 2 * r), 9 - 4 * d)
            self.assertEqual((3 + 2 * r) / (3 + 2 * r), 1)
            self.assertEqual(1 / r, r / d)
            self.assertEqual(r ** -2, Fraction(1, d))
            self.assertEqual(r ** 0, 1)
            self.assertEqual(r ** 4, d * d)
            self.assertEqual((1 + r) - r, 1)
            self.assertEqual(3 - (1 + r), 2 - r)

    def test_exact_signs_without_float(self):
        r = e.Quadratic(0, 1, 2)
        self.assertTrue(1 < r < Fraction(3, 2))
        self.assertTrue(-Fraction(3, 2) < -r < -1)
        for value, sign in ((0, 0), (1, 1), (-1, -1), (1 + r, 1), (-1 - r, -1),
                            (1 - r, -1), (r - 1, 1), (2 - r, 1), (r - 2, -1)):
            self.assertEqual(e.Quadratic(value, 0).sign() if type(value) is int else value.sign(), sign)
        # A close Pell approximation remains exact; no cancellation through floats.
        self.assertLess(e.Quadratic(19601, -13860, 2), Fraction(1, 10000))
        self.assertGreater(e.Quadratic(19601, -13860, 2), 0)

    def test_rational_equality_hash_and_boolean(self):
        a = e.Quadratic(Fraction(3, 2), 0, 2)
        b = e.Quadratic(Fraction(3, 2), 0, 6)
        self.assertEqual(a, b)
        self.assertEqual(hash(a), hash(Fraction(3, 2)))
        self.assertEqual(len({a, b, Fraction(3, 2)}), 1)
        self.assertFalse(e.Quadratic())
        self.assertTrue(e.Quadratic(0, 1))
        self.assertNotEqual(e.Quadratic(0, 1, 2), e.Quadratic(0, 1, 6))
        self.assertNotEqual(a, 1.5)

    def test_invalid_scalar_fields_and_operations(self):
        for args in ((True,), (0.5,), (0, 1, 3), (0, 1, True), ('1',)):
            with self.subTest(args=args), self.assertRaises(ValueError):
                e.Quadratic(*args)
        r = e.Quadratic(0, 1, 2)
        for value in (True, 0.5, '1', e.Quadratic(0, 1, 6)):
            with self.subTest(value=value), self.assertRaises(ValueError):
                r + value
        for exponent in (True, 0.5, 33, -33):
            with self.subTest(exponent=exponent), self.assertRaises(ValueError):
                r ** exponent
        with self.assertRaises(ZeroDivisionError):
            r / 0


class EnergyTests(unittest.TestCase):
    def test_independent_ordered_quadruples_rational(self):
        for modulus, target in product((0, 3, 4), (e.Group((0,)), e.Group((3,)), e.Group((2, 2)))):
            domain = e.Group((modulus,))
            weights = {(j,): Fraction(j + 1, j + 2) for j in range(3)}
            images = {x: ((x[0] ** 2 - 1,) if target.moduli == (0,) else
                           ((x[0] ** 2) % 3,) if target.moduli == (3,) else
                           (x[0] % 2, x[0] // 2)) for x in weights}
            self.assertEqual(e.energy(domain, target, weights, images),
                             direct_quadruples(domain, target, weights, images))

    def test_independent_ordered_quadruples_algebraic(self):
        domain, target = e.Group((4,)), e.Group((0,))
        weights = {(0,): 1, (1,): e.Quadratic(1, Fraction(1, 2)), (3,): e.Quadratic(1, -Fraction(1, 2))}
        images = {x: (x[0] % 2,) for x in weights}
        self.assertEqual(e.energy(domain, target, weights, images),
                         direct_quadruples(domain, target, weights, images))

    def test_parity_target_is_Z_not_C2(self):
        G = e.Group((0,))
        weights = {(0,): 1, (1,): 2, (2,): 1}
        images = {x: (x[0] % 2,) for x in weights}
        self.assertEqual(e.energy(G, e.Group((2,)), weights, images).ratio, 1)
        self.assertEqual(e.energy(G, e.Group((0,)), weights, images).ratio, Fraction(27, 35))

    def test_convolution_wrap_and_empty(self):
        w = {(0,): 1, (1,): 2}
        self.assertEqual(e.convolution(e.Group((0,)), w, w), {(0,): 1, (1,): 4, (2,): 4})
        self.assertEqual(e.convolution(e.Group((2,)), w, w), {(0,): 5, (1,): 4})
        self.assertEqual(e.convolution(e.Group((2,)), {}, w), {})

    def test_zero_weight_keys_are_removed(self):
        G = e.Group((0,))
        self.assertEqual(e.energy(G, G, {(0,): 0, (1,): 2}, {(1,): (0,)}), e.Energy(16, 16))
        with self.assertRaises(ValueError):
            e.energy(G, G, {(0,): 0, (1,): 2}, {(0,): (0,), (1,): (0,)})

    def test_weights_and_images_are_validated(self):
        G = e.Group((0,))
        bad = (None, [], {}, {(0,): 0}, {(0,): -1}, {(0,): True}, {(0,): 1.0},
               {(0,): 1 << 256}, {(0,): Fraction(1, 1 << 128)}, {(0, 0): 1},
               {(0,): e.Quadratic(1, -1)}, {(0,): e.Quadratic(1), (1,): e.Quadratic(1, 0, 6)})
        for weights in bad:
            with self.subTest(weights=str(weights)[:100]), self.assertRaises(ValueError):
                e.energy(G, G, weights, {(0,): (0,)})
        for images in (None, [], {}, {(1,): (0,)}, {(0,): [0]}, {(0,): (True,)}):
            with self.subTest(images=images), self.assertRaises(ValueError):
                e.energy(G, G, {(0,): 1}, images)
        with self.assertRaises(ValueError):
            e.energy(None, G, {(0,): 1}, {(0,): (0,)})
        with self.assertRaises(ValueError):
            e.energy(G, None, {(0,): 1}, {(0,): (0,)})

    def test_limits_before_expensive_enumeration(self):
        G = e.Group((0,))
        too_many = {(j,): 1 for j in range(129)}
        with patch.object(e, '_convolution') as conv:
            with self.assertRaises(ValueError):
                e.convolution(G, too_many, {})
            conv.assert_not_called()
        def guarded_set(*args):
            if args:
                raise RuntimeError('traversed images')
            return set()
        with patch.object(e, 'set', side_effect=guarded_set, create=True):
            with self.assertRaises(ValueError):
                e.energy(G, G, {(0,): 1}, {(j,): (0,) for j in range(129)})

    def test_mixed_quadratic_fields_rejected_across_convolution(self):
        with self.assertRaises(ValueError):
            e.convolution(e.Group((0,)), {(0,): e.Quadratic(1, 1, 2)}, {(0,): e.Quadratic(1, 1, 6)})

    def test_translation_and_scaling(self):
        G = e.Group((4, 0))
        w = {(0, -2): Fraction(1, 2), (1, 0): 3, (2, 2): 2}
        original = e.parity_sos(G, w, (1, 1))
        moved = e.translate(G, w, (1, -3))
        translated = e.parity_sos(G, moved, (1, 1))
        self.assertEqual(original['energy'], translated['energy'])
        self.assertEqual(original['difference_norm'], translated['difference_norm'])
        self.assertEqual(original['correlation_asymmetry'], translated['correlation_asymmetry'])
        scale = Fraction(3, 2)
        scaled = e.parity_sos(G, {x: v * scale for x, v in w.items()}, (1, 1))['energy']
        self.assertEqual(scaled.ordinary, original['energy'].ordinary * scale ** 4)
        self.assertEqual(scaled.ratio, original['energy'].ratio)
        with self.assertRaises(ValueError):
            e.translate(e.Group((0,)), {(4096,): 1}, (1,))


class SOSTests(unittest.TestCase):
    def test_sos_and_correlation_negative_fractional_support(self):
        G = e.Group((0,))
        w = {(-3,): Fraction(1, 2), (-2,): Fraction(5, 3), (2,): Fraction(2, 5), (5,): 7}
        result = e.parity_sos(G, w)
        self.assertGreater(result['difference_norm'], 0)
        self.assertEqual(4 * result['energy'].respected - 3 * result['energy'].ordinary,
                         result['difference_norm'] + 2 * result['correlation_asymmetry'])
        self.assertGreater(result['correlation_asymmetry'], 0)

    def test_one_coset_and_trivial_character(self):
        for G, parity in ((e.Group((0,)), (1,)), (e.Group((3,)), (0,)), (e.Group((4, 3)), (0, 0))):
            result = e.parity_sos(G, {G.zero: 2}, parity)
            self.assertEqual(result['energy'].ratio, 1)
            self.assertEqual(result['energy'].defect, Fraction(1, 4))

    def test_endpoint_implies_second_square_vanishes(self):
        for n in range(1, 13):
            G = e.Group((2 * n,))
            result = e.parity_sos(G, dict.fromkeys(G.elements(), 1))
            self.assertEqual(result['ee'], result['oo'])
            self.assertEqual(result['correlation_asymmetry'], 0)
            self.assertEqual([result[k] for k in ('U', 'V', 'C', 'D')], [n ** 3] * 4)
            self.assertEqual(result['energy'], e.Energy(8 * n ** 3, 6 * n ** 3))

    def test_c6_exact_vectors_and_nonperiodicity(self):
        G = e.Group((6,))
        w = {(j,): value for j, value in enumerate((6, 5, 3, 2, 3, 5))}
        result = e.parity_sos(G, w)
        self.assertEqual(result['ee'], {(0,): 54, (2,): 45, (4,): 45})
        self.assertEqual(result['oo'], result['ee'])
        self.assertEqual(result['eo'], {(1,): 51, (3,): 42, (5,): 51})
        self.assertEqual(result['correlation'], result['eo'])
        self.assertEqual([e.convolution(G, w, w)[(j,)] for j in range(6)], [108, 102, 90, 84, 90, 102])
        self.assertEqual(result['energy'], e.Energy(55728, 41796))
        self.assertEqual(result['energy'], direct_quadruples(G, e.Group((0,)), w, {x: (x[0] % 2,) for x in w}))
        self.assertEqual(e.translation_periods(G, w), ((0,),))

    def test_c8_seven_point_exact_endpoint(self):
        result = e.c8_example()
        self.assertEqual(result['support_size'], 7)
        self.assertEqual(result['parity_one_element_orders'], [8])
        self.assertEqual(result['ordinary'], 576)
        self.assertEqual(result['respected'], 432)
        self.assertEqual(result['ratio'], Fraction(3, 4))
        self.assertEqual(result['difference_norm'], 0)
        self.assertEqual(result['correlation_asymmetry'], 0)
        self.assertEqual(result['weights'][4], 0)
        self.assertGreater(result['weights'][3], 0)

    def test_cyclotomic_n2_integer_and_wrapping_regressions(self):
        result = e.cyclotomic_n2_example()
        self.assertEqual(result['integer_energy'], e.Energy(34, 26))
        self.assertEqual(result['integer_energy'].defect, Fraction(1, 68))
        self.assertEqual(result['signed_polynomial'], {(0,): 1, (4,): 1})
        self.assertEqual(result['finite_cases'][0]['energy'], e.Energy(36, 28))
        self.assertEqual(result['finite_cases'][0]['energy'].defect, Fraction(1, 36))
        for sample in result['finite_cases'][1:]:
            self.assertEqual(sample['energy'], e.Energy(34, 26))
            self.assertEqual(sample['signed_norm'], 2)

    def test_cyclotomic_n4_polynomial_reduction_and_independent_counts(self):
        result = e.cyclotomic_n4_certificate()
        b, square_a = result['b'], result['square_a']
        self.assertEqual(b, e.Quadratic(2, 1, 2))
        self.assertEqual(b * b, 4 * b - 2)
        self.assertEqual(square_a, 2 * b)
        coefficients = (1, 1, b, 1, 1)
        for record in result['cases']:
            N = record['modulus']
            ordinary = respected = Fraction(0)
            for x, y, z, t in product(range(5), repeat=4):
                difference = x + y - z - t
                if (difference % N if N else difference):
                    continue
                odd_count = sum(i % 2 for i in (x, y, z, t))
                self.assertEqual(odd_count % 2, 0)
                mass = coefficients[x] * coefficients[y] * coefficients[z] * coefficients[t] * square_a ** (odd_count // 2)
                ordinary += mass
                if x % 2 + y % 2 == z % 2 + t % 2:
                    respected += mass
            self.assertEqual(record['energy'], e.Energy(ordinary, respected))
            self.assertLessEqual(record['energy'].defect, 2 * result['cases'][0]['energy'].defect)
        self.assertEqual(result['cases'][0]['energy'].ordinary, e.Quadratic(1154, 768, 2))
        self.assertEqual(result['cases'][0]['signed_convolution'], {(0,): 1, (8,): 1})
        self.assertEqual([x['signed_norm'] for x in result['cases']], [2, 2, 4, 2])

    def test_separate_fiber_endpoints_do_not_imply_union_endpoint(self):
        result = e.cross_fiber_example()
        self.assertEqual([x.ratio for x in result['separate_energies']], [Fraction(3, 4)] * 2)
        self.assertGreater(result['combined_energy'].ratio, Fraction(3, 4))
        self.assertEqual(result['signed_convolution'], {(1, 0): 24, (1, 2): -12, (1, 4): -12})
        self.assertEqual(result['difference_norm'], 864)

    def test_mass_balance_is_not_endpoint_sufficient(self):
        result = e.parity_sos(e.Group((4,)), {(0,): 1, (1,): 1})
        self.assertEqual(result['energy'].ratio, 1)
        self.assertNotEqual(result['ee'], result['oo'])
        self.assertFalse(e.local_structure(e.Group((4,)), {(0,): 1, (1,): 1})['parity_trivial_on_local_torsion'])


class LocalTorsionTests(unittest.TestCase):
    def test_full_integer_kernel_is_saturated(self):
        matrices = (((2, 3, 5),), ((2, 4, 6),), ((-2, 3, -5),),
                    ((2, 0, 1, 3), (0, 3, 1, -2)), ((0, 0, 0), (2, 3, 5)))
        for matrix in matrices:
            n = len(matrix[0])
            rank, basis = e.integer_kernel(matrix, n)
            self.assertEqual(len(basis), n - rank)
            for vector in product(range(-2, 3), repeat=n):
                if any(sum(a * b for a, b in zip(row, vector)) for row in matrix):
                    continue
                coordinates = coordinates_in_independent_basis(basis, vector)
                self.assertIsNotNone(coordinates)
                self.assertTrue(all(c.denominator == 1 for c in coordinates), (matrix, vector, coordinates))

    def test_zero_and_full_rank_kernels(self):
        self.assertEqual(e.integer_kernel((), 2), (0, ((1, 0), (0, 1))))
        self.assertEqual(e.integer_kernel((), 0), (0, ()))
        self.assertEqual(e.integer_kernel(((2, 0), (0, 3)), 2), (2, ()))

    def test_kernel_validation(self):
        for matrix, columns in (([], 1), (((1,),), True), (((1,),), -1), (((1,),), 129),
                                (((True,),), 1), (((1.0,),), 1), (((1, 2),), 1), (((8193,),), 1)):
            with self.subTest(matrix=matrix, columns=columns), self.assertRaises(ValueError):
                e.integer_kernel(matrix, columns)

    def test_diagonal_local_group_is_torsion_free(self):
        G = e.Group((2, 0))
        w = {(0, 0): 1, (1, 1): 2, (0, 2): 1}
        local = e.local_structure(G, w, (1, 0))
        self.assertEqual(local['free_rank'], 1)
        self.assertEqual(local['free_projection_size'], 3)
        self.assertEqual(local['torsion_generators'], ())
        self.assertTrue(local['parity_trivial_on_local_torsion'])
        self.assertGreater(e.local_gap_check(G, w, (1, 0))['energy'].defect, 0)

    def test_difference_group_ignores_basepoint_torsion(self):
        G = e.Group((2, 0))
        w = {(1, 0): 1, (1, 2): 2, (1, 4): 3}
        local = e.local_structure(G, w, (1, 0))
        self.assertEqual(local['torsion_generators'], ())
        self.assertEqual(e.local_gap_check(G, w, (1, 0))['energy'].ratio, 1)

    def test_local_parity_one_torsion_witness(self):
        G = e.Group((2, 0))
        # 3*(0,2)-2*(1,3) has parity zero; (1,5)-(0,2)-(1,3) is zero.
        # Change the last torsion coordinate to 0: the same free relation is now odd.
        w = {(0, 0): 1, (0, 2): 1, (1, 3): 1, (0, 5): 1}
        local = e.local_structure(G, w, (1, 0))
        self.assertFalse(local['parity_trivial_on_local_torsion'])
        self.assertIn((1, 0), local['parity_one_torsion_witnesses'])
        with self.assertRaisesRegex(ValueError, 'inapplicable'):
            e.local_gap_check(G, w, (1, 0))

    def test_projection_size_not_fiber_multiplicity(self):
        G = e.Group((0, 3))
        w = {(j, t): (j + 1) * (t + 1) for j in range(3) for t in range(3)}
        result = e.local_gap_check(G, w, (1, 0))
        self.assertEqual(result['local']['support_size'], 9)
        self.assertEqual(result['local']['free_projection_size'], 3)
        self.assertEqual(result['central_lower'], e.central_lower_bound(3))
        self.assertGreater(result['central_lower'], e.central_lower_bound(9))
        self.assertTrue(result['local']['torsion_generators'])

    def test_finite_parity_trivial_torsion_gives_ratio_one(self):
        G = e.Group((3,))
        result = e.local_gap_check(G, {(0,): 1, (1,): 2, (2,): 3}, (0,))
        self.assertEqual(result['local']['free_projection_size'], 1)
        self.assertEqual(result['central_lower'], Fraction(1, 4))
        self.assertEqual(result['energy'].ratio, 1)

    def test_local_structure_is_translation_invariant(self):
        G = e.Group((4, 0, 3))
        w = {(0, 0, 0): 1, (1, 1, 1): 2, (2, 2, 0): 3, (3, 3, 2): 1}
        one = e.local_structure(G, w, (1, 0, 0))
        two = e.local_structure(G, e.translate(G, w, (3, -9, 2)), (1, 0, 0))
        for key in ('support_size', 'free_rank', 'free_projection_size', 'parity_trivial_on_local_torsion'):
            self.assertEqual(one[key], two[key])


class BoundTests(unittest.TestCase):
    def test_central_and_clean_exact_values(self):
        self.assertEqual(e.central_lower_bound(1), Fraction(1, 4))
        self.assertEqual(e.central_lower_bound(2), Fraction(1, 32))
        self.assertEqual(e.central_lower_bound(3), Fraction(1, 384))
        for m in range(1, 33):
            self.assertGreaterEqual(e.central_lower_bound(m), e.clean_lower_bound(m))
            self.assertEqual(e.clean_lower_bound(m), Fraction(1, 4 * 16 ** (m - 1)))
            if m > 1:
                self.assertLess(e.central_lower_bound(m), e.central_lower_bound(m - 1))

    def test_bound_and_binomial_parameters(self):
        for function in (e.central_lower_bound, e.clean_lower_bound, e.binomial_weights,
                         e.binomial_defect, e.binomial_upper_bound):
            for value in (True, False, 0, -1, 129, 2.0, '2', None):
                with self.subTest(function=function.__name__, value=value), self.assertRaises(ValueError):
                    function(value)

    def test_binomial_exact_and_refined_strict_upper(self):
        for m in range(1, 13):
            result = e.parity_sos(e.Group((0,)), e.binomial_weights(m))
            self.assertEqual(result['energy'].ordinary, comb(8 * m, 4 * m))
            self.assertEqual(result['difference_norm'], comb(4 * m, 2 * m))
            self.assertEqual(result['correlation_asymmetry'], 0)
            self.assertEqual(result['energy'].defect, e.binomial_defect(m))
            self.assertLess(e.binomial_defect(m), Fraction(1, 2 * 16 ** m))
        self.assertEqual(e.binomial_defect(1), Fraction(3, 140))

    def test_no_indicator_only_bound_for_general_weights(self):
        m = 5
        self.assertLess(e.binomial_defect(m), Fraction(1, 4 * (2 * m + 1) ** 2))

    def test_log_free_support_rounding_at_boundaries(self):
        for m in range(1, 17):
            epsilon = e.binomial_upper_bound(m)
            result = e.support_window(epsilon)
            self.assertEqual(result['binomial_m'], m)
            self.assertEqual(result['constructive_support'], 2 * m + 1)
            self.assertLess(e.binomial_defect(m), epsilon)
            slightly_smaller = epsilon - epsilon / 100
            self.assertEqual(e.support_window(slightly_smaller)['binomial_m'], m + 1)
        for s in range(2, 17):
            epsilon = e.central_lower_bound(s)
            self.assertEqual(e.support_window(epsilon)['necessary_support'], s)
            self.assertEqual(e.support_window(epsilon - epsilon / 100)['necessary_support'], s + 1)

    def test_epsilon_validation_and_smallest_supported_scale(self):
        for epsilon in (True, False, 0, -1, 0.01, '1/10', None, Fraction(1, 4), 1, Fraction(1, 1 << 128)):
            with self.subTest(epsilon=epsilon), self.assertRaises(ValueError):
                e.support_window(epsilon)
        result = e.support_window(Fraction(1, (1 << 127) + 1))
        self.assertLessEqual(result['binomial_m'], 32)
        self.assertLessEqual(result['necessary_support'], result['constructive_support'])


class ThreePointTests(unittest.TestCase):
    def test_polynomial_certificate_coefficient_identity(self):
        result = e.three_point_polynomial_certificate()
        self.assertEqual(result['residual'], [])
        self.assertEqual(result['lhs_monomials'], 5)
        self.assertEqual(result['rhs_monomials'], 5)

    def test_three_point_energy_independent_count(self):
        G = e.Group((0,))
        for a, b, c in product((Fraction(1, 2), 1, 3), repeat=3):
            w = {(-3,): a, (0,): b, (3,): c}
            images = {x: (x[0] % 2,) for x in w}
            self.assertEqual(e.three_point_energy(a, b, c), direct_quadruples(G, G, w, images))
            certificate = e.three_point_slack(a * c, b * b, a * a + c * c)
            self.assertGreater(certificate['slack'], 0)
            self.assertGreater(certificate['ratio'], certificate['minimum'])

    def test_optimum_invariants_exact_without_fourth_root_approximation(self):
        root = e.Quadratic(0, 1, 6)
        result = e.three_point_slack(1, root, 2)
        self.assertEqual(result['slack'], 0)
        self.assertEqual(result['endpoint_imbalance'], 0)
        self.assertEqual(result['middle_imbalance'], 0)
        self.assertEqual(result['ratio'], (9 + root) / 15)
        self.assertEqual(result['ratio'] - Fraction(3, 4), (4 * root - 9) / 60)

    def test_equality_requires_both_imbalances_zero(self):
        root = e.Quadratic(0, 1, 6)
        for p, q, t in ((1, root, 3), (1, 2, 2), (2, 2 * root, 5)):
            result = e.three_point_slack(p, q, t)
            self.assertGreater(result['slack'], 0)
            self.assertGreater(result['ratio'], result['minimum'])
        self.assertEqual(e.three_point_slack(3, 3 * root, 6)['slack'], 0)

    def test_three_support_geometry_and_parity(self):
        G = e.Group((0,))
        for points in ((-2,), (-3, 2), (0, 1, 3), (0, 2, 4)):
            weights = {(x,): i + 1 for i, x in enumerate(points)}
            self.assertEqual(e.parity_sos(G, weights)['energy'].ratio, 1)
        self.assertLess(e.parity_sos(G, {(0,): 1, (1,): 1, (2,): 1})['energy'].ratio, 1)

    def test_invalid_three_point_inputs(self):
        for triple in ((0, 1, 1), (-1, 1, 1), (1.0, 1, 1), (True, 1, 1), (1 << 256, 1, 1), (Fraction(1, 1 << 128), 1, 1)):
            with self.subTest(triple=triple), self.assertRaises(ValueError):
                e.three_point_energy(*triple)
        for triple in ((0, 1, 2), (1, 0, 2), (1, 1, 1), (1.0, 1, 2), (1, e.Quadratic(0, 1, 2), 2), (1, 1, 1 << 256)):
            with self.subTest(triple=triple), self.assertRaises(ValueError):
                e.three_point_slack(*triple)


class ScopeAndCLITests(unittest.TestCase):
    def test_no_optimization_removable_guards_or_float_literals(self):
        source = (ROOT / 'companion/exact_checks.py').read_text()
        tree = ast.parse(source)
        self.assertFalse(any(isinstance(node, ast.Assert) for node in ast.walk(tree)))
        self.assertFalse(any(isinstance(node, ast.Constant) and type(node.value) is float for node in ast.walk(tree)))
        with self.assertRaisesRegex(RuntimeError, 'sentinel'):
            e.require(False, 'sentinel')

    def test_fixed_diagnostic_counts_are_honest(self):
        result = e.run_checks()
        self.assertEqual(result['index_two_sos']['cases'], 96)
        self.assertEqual(result['integer_lower_bounds']['cases'], 255)
        self.assertEqual(result['binomial']['cases'], 12)
        self.assertEqual(result['three_points']['rational_weight_cases'], 64)
        self.assertEqual(result['finite_torsion_indicators']['cases'], 16)
        self.assertEqual(result['local_examples']['cases'], 5)
        self.assertEqual(result['report'], 289)
        self.assertIn('not a proof-assistant certificate', result['scope'])

    def test_cli_help_and_bad_arguments_do_not_run_checks(self):
        with patch.object(e, 'run_checks') as run:
            with self.assertRaises(SystemExit) as error:
                e.main(['--unexpected'])
            self.assertEqual(error.exception.code, 2)
            run.assert_not_called()
        help_result = subprocess.run([sys.executable, '-B', str(ROOT / 'companion/exact_checks.py'), '--help'], capture_output=True, text=True)
        self.assertEqual(help_result.returncode, 0)
        self.assertIn('Report289', help_result.stdout)
        self.assertNotIn('index_two_sos', help_result.stdout)

    def test_normal_optimized_json_is_identical_and_exact(self):
        script = str(ROOT / 'companion/exact_checks.py')
        normal = subprocess.run([sys.executable, '-B', script], capture_output=True, text=True, check=True)
        optimized = subprocess.run([sys.executable, '-B', '-O', script], capture_output=True, text=True, check=True)
        self.assertEqual(normal.stdout, optimized.stdout)
        self.assertEqual(normal.stderr, '')
        summary = json.loads(normal.stdout)
        self.assertEqual(summary['c6']['ordinary'], '55728')
        self.assertEqual(summary['c6']['respected'], '41796')
        self.assertEqual(summary['c8']['ratio'], {'a': '3/4', 'b': '0', 'radicand': 2})
        self.assertEqual(summary['three_points']['minimum'], {'a': '3/5', 'b': '1/15', 'radicand': 6})

    def test_runtime_validation_survives_optimization(self):
        code = f"""import importlib.util,sys
s=importlib.util.spec_from_file_location('c', {str(ROOT / 'companion/exact_checks.py')!r})
m=importlib.util.module_from_spec(s);sys.modules[s.name]=m;s.loader.exec_module(m)
checks=[lambda:m.Group((True,)),lambda:m.parity_sos(m.Group((3,)),{{(0,):1}}),lambda:m.binomial_defect(0),lambda:m.local_gap_check(m.Group((2,)),{{(0,):1,(1,):1}})]
for check in checks:
 try: check()
 except ValueError: continue
 raise RuntimeError('validation disappeared')
try: m.require(False,'guard')
except RuntimeError: pass
else: raise RuntimeError('runtime guard disappeared')
print('validated')
"""
        result = subprocess.run([sys.executable, '-B', '-O', '-c', code], capture_output=True, text=True, check=True)
        self.assertEqual(result.stdout, 'validated\n')


if __name__ == '__main__':
    unittest.main()
