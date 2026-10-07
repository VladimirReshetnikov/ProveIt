#!/usr/bin/env python3
"""Exact arithmetic, input-boundary and optimized-mode regressions for Report291."""
import ast
from fractions import Fraction
from itertools import product
import json
from pathlib import Path
import random
import subprocess
import sys
import unittest

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
from companion import exact_checks as e


class PolynomialTests(unittest.TestCase):
    def test_all_c3_monomials_and_counts(self):
        data = e.cut_polynomial_counts(3)
        self.assertEqual(sum(data['ordinary'].values()), 27)
        self.assertEqual(sum(data['respected'].values()), 19)
        self.assertEqual(data['ordinary'][(2, 1, 1)], 4)
        self.assertEqual(data['ordinary'][(1, 1, 2)], 4)
        self.assertNotIn((2, 1, 1), data['respected'])
        self.assertNotIn((1, 1, 2), data['respected'])
        self.assertEqual(data['respected'], {(4, 0, 0): 1, (0, 4, 0): 1, (0, 0, 4): 1,
                         (2, 2, 0): 4, (0, 2, 2): 4, (2, 0, 2): 4, (1, 2, 1): 4})
        for weights in ((1, 0, 1), (0, 3, 1), (1, 3, 0), (0, 2, 0), (2, 3, 4),
                        (Fraction(1, 3), Fraction(2, 7), Fraction(3, 5))):
            a, b, c = weights
            respected = a ** 4 + c ** 4 + 4 * b ** 2 * (a ** 2 + c ** 2) + (2 * a * c + b ** 2) ** 2
            failed = 4 * a * b * c * (a + c)
            self.assertEqual(e.cyclic_energy(3, (0, 1, 2), weights), e.Energy(respected + failed, respected))

    def test_c3_symmetric_and_c4_polynomials(self):
        c3 = e.cut_polynomial_counts(3, (0, 1, 0))
        c4 = e.cut_polynomial_counts(4, (0, 1, 1, 0))
        self.assertEqual(c3, dict(ordinary={0: 6, 1: 8, 2: 12, 4: 1}, respected={0: 6, 2: 12, 4: 1}))
        self.assertEqual(c4, dict(ordinary={0: 6, 1: 8, 2: 36, 3: 8, 4: 6}, respected={0: 6, 2: 24, 3: 8, 4: 6}))
        self.assertEqual(sum(c4['ordinary'].values()), 64)
        self.assertEqual(sum(c4['respected'].values()), 44)
        for t in (0, Fraction(3, 5), 1, Fraction(7, 3)):
            expected = e.Energy(6 * t ** 4 + 8 * t ** 3 + 36 * t ** 2 + 8 * t + 6,
                                6 * t ** 4 + 8 * t ** 3 + 24 * t ** 2 + 6)
            self.assertEqual(e.cyclic_energy(4, (0, 1, 2, 3), (1, t, t, 1), method='triples'), expected)
        self.assertEqual(e.cyclic_energy(4, (0, 1, 2, 3), (5, 3, 3, 5)), e.Energy(16416, 10716))

    def test_minimizer_exact_quotient_ring(self):
        p = (-2, 0, 4, 0, 1)
        self.assertEqual(e.reduce_minimizer(p), (0,))
        self.assertEqual(e.reduce_minimizer((0, 0, 0, 0, 1)), (2, 0, -4))
        self.assertEqual(e.reduce_minimizer(e.polynomial_multiply((2, 0, 1), (2, 0, 1))), (6,))
        self.assertEqual(e.reduce_minimizer((6, 0, 12, 0, 1)), (8, 0, 8))
        self.assertEqual(e.reduce_minimizer((6, 0, -12, 0, -3)), (0,))
        self.assertEqual(e.polynomial_derivative((6, 0, 12, 0, 1)), (0, 24, 0, 4))
        self.assertLess(e.polynomial_evaluate(p, Fraction(2, 3)), 0)
        self.assertGreater(e.polynomial_evaluate(p, Fraction(7, 10)), 0)
        self.assertEqual(342 ** 2 - 6 * 139 ** 2, 1038)
        self.assertLess(25 ** 2, 11 ** 2 * 6)

    def test_polynomial_validation(self):
        for p in (None, [], (), (0,) * 26, (True,), (1.0,), ('1',), (1 << 64,), (Fraction(1, 1 << 32),)):
            for function in (e.reduce_minimizer, e.polynomial_derivative):
                with self.subTest(p=p, function=function), self.assertRaises(ValueError):
                    function(p)
        with self.assertRaises(ValueError):
            e.polynomial_multiply((0,) * 24 + (1,), (0, 1))
        for x in (True, 0.5, '1', 1 << 64):
            with self.subTest(x=x), self.assertRaises(ValueError):
                e.polynomial_evaluate((1, 2), x)
        for n in (True, 2, 5, 3.0, None):
            with self.subTest(n=n), self.assertRaises(ValueError):
                e.cut_polynomial_counts(n)
        for powers in ([0, 1, 0], (), (0, 1), (0, 1, 0, 1), (True, 1, 0), (-1, 1, 0), (7, 1, 0)):
            with self.subTest(powers=powers), self.assertRaises(ValueError):
                e.cut_polynomial_counts(3, powers)


class SmallCycleAndLiftTests(unittest.TestCase):
    def test_eight_c9_rows_and_realized_energies(self):
        data = e.check_c9()
        self.assertEqual([r['derivative_masses'] for r in data['rows']], list(e.C9_EXPECTED))
        self.assertEqual([r['energy'].respected for r in data['rows']], [505, 433, 449, 489, 393, 393, 441, 489])
        self.assertEqual(data['spike_energy'], e.Energy(162, 106))
        self.assertEqual(data['spike_energy'].ratio, Fraction(53, 81))
        self.assertEqual(data['spike_support'], (0, 1, 3, 4, 6, 7))
        for k, q in product(range(1, 5), (3, 4, 7, 4096)):
            self.assertEqual(e.c9_interval_row(k, q), e.c9_interval_row(k, None))

    def test_finite_lifts_all_pattern_multiplicities(self):
        for q, k, weights in ((1, 16, (2,)), (3, 1, (1, Fraction(3, 5), 1)),
                              (3, 7, (1, Fraction(3, 5), 1)), (4, 4, (1, 2, 0, 3)), (8, 6, (1,) * 8)):
            result = e.finite_quotient_lift(q, k, weights)
            self.assertEqual(len(result['patterns']), q ** 3)
            self.assertEqual(set(result['patterns'].values()), {k ** 3})
            self.assertTrue(all((i + j - r - s) % q == 0 for i, j, r, s in result['patterns']))
            self.assertEqual(result['lifted_energy'].ordinary, k ** 3 * result['quotient_energy'].ordinary)
            self.assertEqual(result['lifted_energy'].respected, k ** 3 * result['quotient_energy'].respected)

    def test_general_cyclic_pair_and_triple_oracles(self):
        rng = random.Random(291)
        for n in range(1, 10):
            values = tuple(rng.randrange(-20, 21) for _ in range(n))
            weights = tuple(Fraction(rng.randrange(1, 5), rng.randrange(1, 5)) for _ in range(n))
            for modulus in (None, 1, 2, 5, 4096):
                self.assertEqual(e.cyclic_energy(n, values, weights, modulus),
                                 e.cyclic_energy(n, values, weights, modulus, 'triples'))

    def test_cycle_and_lift_limits(self):
        for n in (0, -1, 49, True, 1.0, '1', None):
            with self.subTest(n=n), self.assertRaises(ValueError):
                e.cyclic_energy(n, (0,), (1,))
        for values in (None, [], (), (0, 1), (True,), (1.0,), (4097,), (-4097,)):
            with self.subTest(values=values), self.assertRaises(ValueError):
                e.cyclic_energy(1, values, (1,))
        for weights in (None, [], (), (1, 2), (0,), (-1,), (True,), (1.0,), ('1',),
                        (1 << 64,), (Fraction(1, 1 << 32),)):
            with self.subTest(weights=weights), self.assertRaises(ValueError):
                e.cyclic_energy(1, (0,), weights)
        for modulus in (0, -1, 4097, True, 1.0, '2'):
            with self.subTest(modulus=modulus), self.assertRaises(ValueError):
                e.cyclic_energy(1, (0,), (1,), modulus)
        for method in (None, True, 'quadruples', ''):
            with self.subTest(method=method), self.assertRaises(ValueError):
                e.cyclic_energy(1, (0,), (1,), method=method)
        for q, k in ((0, 1), (9, 1), (3, 0), (3, 17), (8, 7), (True, 1), (3, True)):
            with self.subTest(q=q, k=k), self.assertRaises(ValueError):
                e.finite_quotient_lift(q, k, (1,))
        for k in (0, 5, -1, True, 1.0, None):
            with self.subTest(k=k), self.assertRaises(ValueError):
                e.c9_interval_row(k, 2)
        for q in (0, 1, -1, 4097, True, 2.0):
            with self.subTest(q=q), self.assertRaises(ValueError):
                e.c9_interval_row(1, q)


class BranchTests(unittest.TestCase):
    def test_all_70_histograms_maxima_and_pattern_counts(self):
        slope_patterns = no_wrap_patterns = 0
        for row, column in product(range(1, 8), range(10)):
            modulus = 10 + column if column < 9 else None
            c, w = e.branch_data(row)
            result = e.branch_certificate(row, modulus)
            self.assertEqual(result['histogram'], e.coefficient_histogram(c, w, modulus, 'quadruples'))
            self.assertEqual(result['energy'].ratio, e.BRANCH_MAXIMA[row - 1][column])
            self.assertLess(result['energy'].ratio, Fraction(17, 25))
            m = result['M']
            self.assertEqual(result['symbolic_patterns'], 2 * m * (2 * m + 1) if m else 1)
            self.assertEqual(result['no_wrap_patterns'], 2 * m if m else 1)
            slope_patterns += result['symbolic_patterns']
            no_wrap_patterns += result['no_wrap_patterns']
            for h in (*range(-m, m + 1), None):
                for q in (2 * m + 1, 4096) if m else (2, 4096):
                    self.assertEqual(e.symbolic_numerator(result['histogram'], q, h),
                                     e.symbolic_numerator(result['histogram'], None, h))
        self.assertEqual((slope_patterns, no_wrap_patterns), (2338, 310))

    def test_corrected_across_order_maxima_and_witnesses(self):
        self.assertEqual(max(e.BRANCH_MAXIMA[5]), Fraction(323, 491))
        self.assertEqual(e.BRANCH_MAXIMA[5].index(Fraction(323, 491)), 6)
        self.assertEqual(max(e.BRANCH_MAXIMA[6]), Fraction(143, 215))
        self.assertEqual(e.BRANCH_MAXIMA[6].index(Fraction(143, 215)), 3)
        self.assertEqual(e.realized_pair_energy(*e.branch_data(6), 16, None, -6), e.Energy(491, 323))
        self.assertEqual(e.realized_pair_energy(*e.branch_data(7), 13, None, -3), e.Energy(215, 143))
        self.assertEqual(Fraction(323, 491) - Fraction(107, 163), Fraction(112, 80033))
        self.assertEqual(Fraction(143, 215) - Fraction(47, 71), Fraction(48, 15265))

    def test_row_three_histogram_wrap_counts_and_loose_bound(self):
        c, w = e.branch_data(3)
        self.assertEqual(e.coefficient_histogram(c, w), {(0, 0): 1935, (0, 1): 530, (0, -1): 530})
        expected = ({1: 22, 2: 65}, {1: 6, 2: 32}, {2: 14}, {2: 4}, {2: 1}, {})
        for n, positive in zip(range(10, 16), expected):
            hist = e.coefficient_histogram(c, w, n)
            self.assertEqual({t: count for (z, t), count in hist.items() if z == 1}, positive)
        self.assertEqual(tuple(e.branch_certificate(3, n)['energy'].ordinary for n in range(10, 16)),
                         (3169, 3071, 3023, 3003, 2997, 2995))
        self.assertLess(Fraction(2109, 3169), Fraction(25, 37))

    def test_no_wrap_cutoff_and_slope_is_retained(self):
        for row in range(1, 8):
            c, w = e.branch_data(row)
            c = c + (0,) * (19 - len(c))
            w = w + (0,) * (19 - len(w))
            for q in (None, 2, 3, 13):
                actual = e.cyclic_energy(19, c, w, q)
                hist = e.coefficient_histogram(*e.branch_data(row))
                self.assertEqual(actual.respected, e.symbolic_numerator(hist, q, 0))
                self.assertEqual(actual.ordinary, sum(hist.values()))
        c, w = e.branch_data(6)
        self.assertNotEqual(e.realized_pair_energy(c, w, 16, None, 0).respected,
                            e.realized_pair_energy(c, w, 16, None, -6).respected)

    def test_rational_weights_and_zero_defect_boundary(self):
        c, w = e.branch_data(3)
        scaled = tuple(Fraction(x, 7) for x in w)
        self.assertEqual(e.coefficient_histogram(c, scaled),
                         {key: Fraction(value, 7 ** 4) for key, value in e.coefficient_histogram(c, w).items()})
        self.assertEqual(e.coefficient_histogram(c, scaled), e.coefficient_histogram(c, scaled, method='quadruples'))
        zero = e.symbolic_maximum(e.coefficient_histogram((0, 0), (1, 1), 10))
        self.assertEqual((zero['M'], zero['symbolic_patterns'], zero['no_wrap_patterns']), (0, 1, 1))
        self.assertEqual(zero['energy'].ratio, 1)

    def test_branch_validation(self):
        for row in (0, 8, -1, True, 1.0, '1', None):
            with self.subTest(row=row), self.assertRaises(ValueError):
                e.branch_data(row)
        for c, w in ((None, (1,)), ([], (1,)), ((), (1,)), ((0,) * 11, (1,) * 11),
                     ((True,), (1,)), ((-1,), (1,)), ((4,), (1,)), ((0,), []), ((0,), ()),
                     ((0,), (1, 2)), ((0,), (0,)), ((0,), (-1,)), ((0,), (True,)), ((0,), (1.0,)),
                     ((0,), (1 << 64,)), ((0,), (Fraction(1, 1 << 32),))):
            with self.subTest(c=c, w=w), self.assertRaises(ValueError):
                e.coefficient_histogram(c, w)
        for n in (0, 1, 9, 19, True, 10.0, '10'):
            with self.subTest(n=n), self.assertRaises(ValueError):
                e.branch_certificate(1, n)
        for method in (None, True, 'direct', ''):
            with self.subTest(method=method), self.assertRaises(ValueError):
                e.coefficient_histogram((0,), (1,), method=method)

    def test_histogram_order_and_slope_validation(self):
        invalid = (None, {}, [], {(0, 0): True}, {(0, 0): 0}, {(0, 0): -1}, {(0, 0): 0.5},
                   {(0, 0): 1 << 4096}, {(0, 0): Fraction(1, 1 << 4096)}, {(False, 0): 1},
                   {(0, True): 1}, {(2, 0): 1}, {(0, 7): 1}, {(0, 0): 1, (1, 1): 1},
                   {(1, 0): 1, (-1, 0): 1}, {(0,): 1}, {'x': 1})
        for hist in invalid:
            with self.subTest(hist=hist), self.assertRaises(ValueError):
                e.symbolic_maximum(hist)
        hist = e.coefficient_histogram(*e.branch_data(1), 10)
        for q in (0, 1, True, 2.0, 'infinite', 4097):
            with self.subTest(q=q), self.assertRaises(ValueError):
                e.symbolic_numerator(hist, q, 0)
            with self.subTest(q=q), self.assertRaises(ValueError):
                e.realized_pair_energy(*e.branch_data(1), 10, q, 0)
        for h in (True, 0.0, '0', -3, 3):
            with self.subTest(h=h), self.assertRaises(ValueError):
                e.symbolic_numerator(hist, 2, h)
        for h in (True, 0.0, -7, 7):
            with self.subTest(h=h), self.assertRaises(ValueError):
                e.realized_pair_energy(*e.branch_data(1), 10, 2, h)


class StaircaseTests(unittest.TestCase):
    def test_negative_indices_and_missing_fibers(self):
        for f in ({-7: 2, -5: Fraction(1, 2), -1: 3, 2: 4, 3: 1},
                  {-6: 1, -3: 2, 0: 3}, {-2: 2}, {0: 0, 1: 4}):
            self.assertEqual(e.staircase_residue_energy(f), e.staircase_direct_energy(f, 'quadruples'))
        self.assertEqual(e.staircase_residue_energy({-6: 1, -3: 2, 0: 3}).ratio, 1)

    def test_finite_carry_formula(self):
        for m in (1, 2, 5, 16):
            weights = tuple(Fraction(1 + j % 5, 1 + j % 3) for j in range(3 * m))
            self.assertEqual(e.finite_cut_residue_energy(m, weights),
                             e.cyclic_energy(3 * m, tuple(j % 3 for j in range(3 * m)), weights))

    def test_triangle_formulas_and_finite_error(self):
        for m in (1, 2, 3, 16, 64, 128):
            data = e.finite_error_identity(m)
            self.assertEqual(data['H'], (2 * m ** 3 + m) // 3)
            self.assertEqual(data['J'], (2 * m ** 3 - 2 * m) // 3)
            self.assertEqual(data['H'] - data['J'], m)
            for t in (Fraction(2, 3), Fraction(3, 5)):
                n = t ** 4 + 12 * t ** 2 + 6
                rho = n / (n + 8 * t)
                actual = n * data['H'] / (n * data['H'] + 8 * t * data['J'])
                self.assertEqual(actual, rho / (1 - 3 * (1 - rho) / (2 * m ** 2 + 1)))
                self.assertEqual(actual - rho, 3 * rho * (1 - rho) / (2 * m ** 2 - 2 + 3 * rho))
                self.assertGreater(actual, rho)
        self.assertEqual(e.finite_error_identity(1)['ordinary_polynomial'], (6, 0, 12, 0, 1))

    def test_completed_attainment_identities(self):
        data = e.check_attainment_identities()
        self.assertEqual(data['finite_convolution_examples'], 32)
        self.assertTrue(data['spurious_B_only_triple_excluded'])

    def test_staircase_input_limits(self):
        invalid = (None, [], {}, {0: 0}, {0: -1}, {True: 1}, {0.0: 1}, {'0': 1}, {-97: 1}, {97: 1},
                   dict.fromkeys(range(49), 1), {0: True}, {0: 1.0}, {0: '1'}, {0: 1 << 64},
                   {0: Fraction(1, 1 << 32)})
        for f in invalid:
            for function in (e.staircase_residue_energy, e.staircase_direct_energy):
                with self.subTest(f=f, function=function), self.assertRaises(ValueError):
                    function(f)
        with self.assertRaises(ValueError):
            e.staircase_direct_energy(dict.fromkeys(range(9), 1), 'quadruples')
        for method in (None, True, 'triples', ''):
            with self.subTest(method=method), self.assertRaises(ValueError):
                e.staircase_direct_energy({0: 1}, method)
        for m in (0, -1, 129, True, 1.0, '1', None):
            with self.subTest(m=m), self.assertRaises(ValueError):
                e.triangle_counts(m)
        for m in (0, -1, 17, True, 1.0, '1', None):
            with self.subTest(m=m), self.assertRaises(ValueError):
                e.finite_cut_residue_energy(m, (1,))
        for w in (None, [], (1, 1), (1, True, 1), (0, 0, 0)):
            with self.subTest(w=w), self.assertRaises(ValueError):
                e.finite_cut_residue_energy(1, w)


class SummaryAndSafetyTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        script = str(ROOT / 'companion/exact_checks.py')
        cls.normal = subprocess.run([sys.executable, '-I', '-B', '-X', 'int_max_str_digits=640', script],
                                    capture_output=True, text=True, check=True, timeout=90)
        cls.optimized = subprocess.run([sys.executable, '-I', '-O', '-B', '-X', 'int_max_str_digits=640', script],
                                       capture_output=True, text=True, check=True, timeout=90)
        cls.summary = json.loads(cls.normal.stdout)

    def test_summary_and_optimized_output_identical(self):
        self.assertEqual(self.normal.stdout, self.optimized.stdout)
        self.assertEqual(self.normal.stderr, '')
        self.assertEqual(self.optimized.stderr, '')
        self.assertEqual((self.summary['report'], self.summary['schema_version'], self.summary['status']), (291, 1, 'passed'))
        b = self.summary['symbolic_certificates']
        self.assertEqual((b['certificate_count'], b['finite_wrap_cases'], b['no_wrap_cases']), (70, 63, 7))
        self.assertEqual((b['symbolic_pattern_evaluations'], b['no_wrap_pattern_evaluations'], b['actual_target_realizations']),
                         (2338, 310, 2648))
        self.assertEqual([r['maximum'] for r in b['rows']],
                         ['57/85', '25/37', '2065/3169', '25/37', '109/173', '323/491', '143/215'])
        self.assertEqual(b['rows'][5]['attaining_moduli'], [16])
        self.assertEqual(b['rows'][6]['attaining_moduli'], [13])

    def test_declared_finite_diagnostic_counts(self):
        self.assertEqual(self.summary['finite_lifts']['cases'], 28)
        s = self.summary['staircase']
        self.assertEqual(s['seed'], 683744248)
        self.assertEqual(s['random_exact_fiber_cases'], 256)
        self.assertEqual(s['literal_quadruple_cases'], 24)
        self.assertEqual(s['finite_index_three_cases'], 16)
        self.assertEqual(s['rational_finite_energy_cases'], 48)
        self.assertEqual(s['triangle_and_finite_error_cases'], 128)

    def test_no_assert_and_no_float_arithmetic(self):
        tree = ast.parse((ROOT / 'companion/exact_checks.py').read_text())
        self.assertFalse(any(isinstance(node, ast.Assert) for node in ast.walk(tree)))
        self.assertFalse(any(isinstance(node, ast.Constant) and type(node.value) is float for node in ast.walk(tree)))
        with self.assertRaises(RuntimeError):
            e.require(False, 'deliberate runtime guard test')
        for args in ((0, 0), (1, -1), (1, 2), (True, 0), (1.0, 0), (1, False)):
            with self.subTest(args=args), self.assertRaises(ValueError):
                e.Energy(*args)

    def test_optimized_invalid_inputs_still_rejected(self):
        script = '''
import sys
sys.path.insert(0, sys.argv[1])
from companion import exact_checks as e
bad = [lambda:e.cyclic_energy(True,(0,),(1,)), lambda:e.branch_certificate(8),
       lambda:e.coefficient_histogram((0,)*11,(1,)*11),
       lambda:e.coefficient_histogram((0,),(False,)),
       lambda:e.symbolic_numerator({(0,0):1},True,0),
       lambda:e.symbolic_maximum({(0,0):1,(1,1):1}),
       lambda:e.finite_quotient_lift(8,7,(1,)*8),
       lambda:e.staircase_direct_energy({97:1}),
       lambda:e.triangle_counts(129), lambda:e.reduce_minimizer((1.0,))]
for case in bad:
    try: case()
    except ValueError: pass
    else: raise RuntimeError('invalid input accepted under optimization')
try: e.require(False,'expected')
except RuntimeError: pass
else: raise RuntimeError('mathematical guard disabled')
print('passed')
'''
        result = subprocess.run([sys.executable, '-I', '-O', '-B', '-c', script, str(ROOT)],
                                capture_output=True, text=True, check=True, timeout=10)
        self.assertEqual(result.stdout, 'passed\n')

    def test_cli_unknown_arguments_rejected_before_checks(self):
        for arg in ('--quick', '--max-support=9999999999', 'extra'):
            result = subprocess.run([sys.executable, '-I', '-B', str(ROOT / 'companion/exact_checks.py'), arg],
                                    capture_output=True, text=True, timeout=10)
            self.assertEqual(result.returncode, 2)
            self.assertEqual(result.stdout, '')

    def test_json_exact_encoding_and_rejection(self):
        self.assertEqual(e.jsonable(Fraction(143, 215)), '143/215')
        self.assertEqual(e.jsonable({(0, 1): Fraction(3, 4)}), [{'key': [0, 1], 'value': '3/4'}])
        for value in (0.5, complex(1, 0), {1, 2}):
            with self.subTest(value=value), self.assertRaises(ValueError):
                e.jsonable(value)


if __name__ == '__main__':
    unittest.main()
