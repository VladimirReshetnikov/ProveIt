"""Exact identities, independent enumeration, strict boundaries and source pins."""
import sys
sys.dont_write_bytecode = True
import ast
import base64
from contextlib import redirect_stdout
from fractions import Fraction as Q
import hashlib
import importlib.util
from io import StringIO
from itertools import product
import json
from pathlib import Path
import subprocess
import unittest
from unittest.mock import patch

ROOT = Path(__file__).absolute().parents[1]
SPEC = importlib.util.spec_from_file_location('report287_exact', ROOT / 'companion/exact_checks.py')
c = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(c)


def independent_energies(N, values, weights):
    ordinary = Q(0); respected = Q(0)
    # Intentionally four independent indices, not convolution or x+y-z indexing.
    for x, y, z, t in product(range(N), repeat=4):
        if (x + y - z - t) % N == 0:
            term = weights[x] * weights[y] * weights[z] * weights[t]
            ordinary += term
            if (values[x] + values[y] - values[z] - values[t]) % N == 0:
                respected += term
    return ordinary, respected


def indicator_energies(N, values, support):
    ordinary = 0; respected = 0
    for x, y, z, t in product(support, repeat=4):
        if (x + y - z - t) % N == 0:
            ordinary += 1
            respected += (values[x] + values[y] - values[z] - values[t]) % N == 0
    return ordinary, respected


class InputTests(unittest.TestCase):
    def test_exact_rational_types_and_bit_boundaries(self):
        self.assertEqual(c.rational(-2), Q(-2))
        self.assertEqual(c.rational(Q(1, 3)), Q(1, 3))
        top = (1 << c.MAX_BITS) - 1
        self.assertEqual(c.rational(top), top)
        self.assertEqual(c.rational(Q(1, top)), Q(1, top))
        for bad in (True, False, '2', None, 2.0, 1j, 1 << c.MAX_BITS, Q(1, 1 << c.MAX_BITS)):
            with self.subTest(value_type=type(bad).__name__), self.assertRaises(ValueError):
                c.rational(bad)
        class IntegerSubclass(int):
            pass
        with self.assertRaises(ValueError): c.rational(IntegerSubclass(1))

    def test_fraction_ceiling_signed_endpoints(self):
        for value, expected in ((Q(-3, 2), -1), (Q(-2), -2), (Q(0), 0), (Q(1, 3), 1), (Q(3, 2), 2)):
            self.assertEqual(c.ceil_fraction(value), expected)
        with self.assertRaises(ValueError): c.ceil_fraction(True)

    def test_no_assert_float_random_or_unbounded_exponent_construction(self):
        source = (ROOT / 'companion/exact_checks.py').read_text()
        tree = ast.parse(source)
        self.assertFalse(any(isinstance(node, ast.Assert) for node in ast.walk(tree)))
        self.assertFalse(any(isinstance(node, ast.Constant) and type(node.value) in (float, complex)
                             for node in ast.walk(tree)))
        self.assertFalse(any(isinstance(node, ast.Name) and node.id in ('float', 'complex', 'random', 'eval', 'exec')
                             for node in ast.walk(tree)))
        self.assertNotIn('set_int_max_str_digits(', source)
        for bad in (False, 1, None, 'true'):
            with self.assertRaisesRegex(RuntimeError, 'live gate'): c.require(bad, 'live gate')
        c.require(True, 'okay')

    def test_cli_rejects_all_arguments_before_work(self):
        for argv in ('', ('x',), ['--help'], ['--size', '1000000000'], {}, 42, False):
            with self.subTest(argv=argv), patch.object(c, 'run_all') as run:
                with self.assertRaises(SystemExit): c.main(argv)
                run.assert_not_called()
        with patch.object(sys, 'argv', ['check', 'unexpected']), patch.object(c, 'run_all') as run:
            with self.assertRaises(SystemExit): c.main()
            run.assert_not_called()
        with patch.object(c, 'run_all', return_value={'status': 'sample'}):
            capture = StringIO()
            with redirect_stdout(capture): self.assertEqual(c.main([]), 0)
            self.assertEqual(json.loads(capture.getvalue()), {'status': 'sample'})

    def test_modulus_word_and_weight_guards(self):
        for N in (0, -1, c.MAX_N + 1, True, Q(2), 2.0, '2'):
            with self.assertRaises(ValueError): c.additive_energy(N, ())
        for values in ((0,), (0, 2), (0, -1), (0, True), (0, Q(1)), iter((0, 1)), None):
            with self.assertRaises(ValueError): c.respected_energy(2, values, (1, 1))
        for weights in ((1,), (1, -1), (True, 1), (1.0, 1), (Q(1, 1 << c.MAX_BITS), 1), iter((1, 1))):
            with self.assertRaises(ValueError): c.respected_energy(2, (0, 1), weights)
        with self.assertRaises(ValueError): c.energy_ratio(2, (0, 0), (0, 0))
        self.assertEqual(c.respected_energy(2, (0, 0), (0, 0)), 0)

    def test_subsets_reject_aliases_and_bad_shapes(self):
        for values in ((0, 0), (-1,), (2,), (True,), (Q(1),), iter((0,)), None, (0, 1, 2)):
            with self.assertRaises(ValueError): c.subset(2, values, 'subset')
        with self.assertRaises(ValueError): c.subset(2, (), 'subset', nonempty=True)
        with self.assertRaises(ValueError): c.subset(2, (0,), 'subset', nonempty=1)
        self.assertEqual(c.subset(2, (1, 0), 'subset'), (1, 0))


class EnergyTests(unittest.TestCase):
    def test_convolution_matches_exhaustive_ordered_quadruples(self):
        for N in (1, 2, 3, 4, 5, 6):
            for values in ((0,) * N, tuple(x * x % N for x in range(N)), tuple((2 * x + 1) % N for x in range(N))):
                for weights in ((1,) * N, tuple(Q(x + 1, x + 2) for x in range(N))):
                    ordinary, respected = independent_energies(N, values, weights)
                    self.assertEqual(c.additive_energy(N, weights), ordinary)
                    self.assertEqual(c.respected_energy(N, values, weights), respected)
                    self.assertEqual(c.energy_ratio(N, values, weights), respected / ordinary)

    def test_convolution_wrap_and_full_group_histogram(self):
        self.assertEqual(c.convolution(4, (0, 0, 0, 1), (0, 1, 0, 0)), (1, 0, 0, 0))
        for N in (1, 2, 3, 4, 6, 8):
            values = tuple(x * x % N for x in range(N))
            row = c.full_group_energy(N, values)
            self.assertEqual(row['energy'], c.respected_energy(N, values, (1,) * N))
            self.assertEqual(row['Qh'][0], N * N)
            self.assertEqual(row['Qh'], tuple(row['Qh'][-h % N] for h in range(N)))

    def test_affine_addition_invariance(self):
        N = 8; values = (0, 1, 3, 3, 2, 0, 7, 5)
        weights = tuple(Q(x + 1, x + 2) for x in range(N))
        original = c.respected_energy(N, values, weights)
        for alpha in range(N):
            for beta in range(N):
                shifted = tuple((values[x] + alpha * x + beta) % N for x in range(N))
                self.assertEqual(c.respected_energy(N, shifted, weights), original)

    def test_scaling_and_zero_weight(self):
        weights = (Q(1, 3), Q(2, 5), Q(4, 7)); values = (0, 1, 1)
        self.assertEqual(c.energy_ratio(3, values, weights),
                         c.energy_ratio(3, values, tuple(3 * w for w in weights)))
        self.assertEqual(c.respected_energy(3, values, tuple(3 * w for w in weights)),
                         81 * c.respected_energy(3, values, weights))


class RelativeThresholdTests(unittest.TestCase):
    def test_four_window_exhaustive_n7_n8(self):
        result = c.check_four_windows()
        self.assertEqual(result['windows'], 7 ** 4 + 8 ** 4)
        self.assertEqual(result['nonzero_M_windows'], 7 ** 4 - 7 ** 3 + 8 ** 4 - 8 ** 3)
        self.assertEqual(result['max_defective_energy'], 32)
        self.assertEqual(result['denominator'], 44)

    def test_four_window_independent_quadruples_and_wrap(self):
        for N in (7, 8, 16, 64):
            for local in ((0, 0, 0, 1), (0, 1, 2, 3), (0, 1, 0, 1), (N - 1, 1, 2, 0)):
                row = c.four_window_certificate(N, local)
                for start in (0, N - 2, N - 1):
                    support = tuple((start + j) % N for j in range(4))
                    values = [0] * N
                    for x, v in zip(support, local): values[x] = v
                    add, respected = indicator_energies(N, values, support)
                    self.assertEqual((row['additive'], row['respected']), (add, respected))

    def test_four_window_guards(self):
        for N in (6, 0, 65, True, Q(7), 7.0):
            with self.assertRaises(ValueError): c.four_window_certificate(N, (0, 0, 0, 1))
        for values in ((0, 1), (0, 0, 0, 7), (0, 0, 0, True), (0, 0, -1, 0), iter((0, 0, 0, 1))):
            with self.assertRaises(ValueError): c.four_window_certificate(7, values)

    def test_small_moduli_exhaustive_inventories(self):
        rows = [c.classify_small_words(N) for N in range(1, 6)]
        self.assertEqual([r['words'] for r in rows], [1, 4, 27, 256, 3125])
        self.assertEqual([r['affine'] for r in rows], [1, 4, 9, 16, 25])
        self.assertEqual([r['nonaffine_parity'] for r in rows], [0, 0, 0, 16, 0])
        self.assertEqual([r['max_other_full_weight_energy'] for r in rows], [0, 0, 15, 40, 69])
        six = c.classify_small_words(6, normalized=True)
        self.assertEqual((six['words'], six['affine'], six['nonaffine_parity'], six['other']),
                         (7776, 6, 12, 7758))
        self.assertEqual(six['max_other_full_weight_energy'], 152)

    def test_word_enumeration_guards_and_normalization(self):
        for N in (0, 7, True, Q(3), '3'):
            with self.assertRaises(ValueError): c.classify_small_words(N)
        for normalized in (1, None, 'yes'):
            with self.assertRaises(ValueError): c.classify_small_words(3, normalized)
        with patch.object(c, 'MAX_WORDS', 3):
            with self.assertRaises(ValueError): c.classify_small_words(2)
        for N in (3, 4, 5):
            normalized = c.classify_small_words(N, True); full = c.classify_small_words(N)
            for key in ('words', 'affine', 'nonaffine_parity', 'other'):
                self.assertEqual(full[key], N * normalized[key])

    def test_explicit_sparse_defect_is_an_upper_witness_only(self):
        row = c.check_sparse_witness()
        self.assertEqual((row['N'], row['additive'], row['respected'], row['ratio']), (8, 44, 32, Q(8, 11)))
        self.assertEqual(row['defect_support'], (3,))
        self.assertEqual(row['best_affine_agreement'], 7)
        self.assertNotIn('exact_r', row)
        values = (0, 0, 0, 1, 0, 0, 0, 0)
        self.assertEqual(indicator_energies(8, values, row['weight_support']), (44, 32))

    def test_sidon_partial_domain_caveat_has_no_affine_extension(self):
        row = c.check_partial_domain_caveat()
        self.assertEqual(row['support'], (0, 1, 3))
        self.assertEqual(row['partial_values'], (0, 0, 1))
        self.assertEqual(row['ordered_additive_quadruples'], 15)
        self.assertEqual(row['ambient_affine_extensions'], 0)
        self.assertEqual(row['indicator_ratio'], 1)
        for local in product(range(7), repeat=3):
            values = [0] * 7
            for x, value in zip(row['support'], local): values[x] = value
            add, respected = indicator_energies(7, values, row['support'])
            self.assertEqual((add, respected), (15, 15))

    def test_nonaffine_parity_sos_rational_and_uniform_weights(self):
        cases = c.check_parity()
        self.assertEqual(cases, {'identities': 132, 'full_weight_equalities': 44, 'affine_agreement_checked': 44})
        for N in (4, 6, 8):
            for weights in ((0,) * N, tuple(Q((2 * x + 1) % 7, x + 1) for x in range(N))):
                row = c.parity_identity(N, 1, 2, 1, weights)
                self.assertEqual(row['gap'], row['norm_square_term'] + row['correlation_square_term'])
                self.assertGreaterEqual(row['norm_square_term'], 0)
                self.assertGreaterEqual(row['correlation_square_term'], 0)
                values = tuple((x + 2 + x % 2) % N for x in range(N))
                self.assertEqual(independent_energies(N, values, weights), (row['additive'], row['respected']))

    def test_parity_guards_affine_endpoint_and_affine_agreement(self):
        for args in ((3, 0, 0, 1, (1,) * 3), (4, 0, 0, 0, (1,) * 4), (4, 0, 0, 2, (1,) * 4),
                     (4, True, 0, 1, (1,) * 4), (4, 0, 4, 1, (1,) * 4), (4, 0, 0, -1, (1,) * 4)):
            with self.assertRaises(ValueError): c.parity_identity(*args)
        self.assertIsNone(c.parity_parameters(5, (0, 1, 2, 3, 4)))
        for N in (2, 4, 6, 8):
            for delta in (0, N // 2):
                values = tuple((3 * x + 1 + delta * (x % 2)) % N for x in range(N))
                self.assertIsNotNone(c.affine_parameters(N, values))
                self.assertEqual(c.best_affine_agreement(N, values), N)
                self.assertEqual(c.energy_ratio(N, values, (1,) * N), 1)
        self.assertEqual(c.best_affine_agreement(8, tuple(x % 2 for x in range(8))), 4)


class CertificateTests(unittest.TestCase):
    def verify_witness(self, N, values, result):
        # Full enumeration is restricted to small N or to four-point supports.
        support = result['indicator_support']
        if len(support) <= 8:
            add, respected = indicator_energies(N, values, support)
            self.assertEqual((add, respected), (result['additive'], result['respected']))
        self.assertEqual(Q(result['respected'], result['additive']), result['upper_bound'])
        if result['kind'] == 'upper_bound':
            self.assertIsNone(result['exact_r'])
            self.assertLessEqual(result['upper_bound'], Q(8, 11))
        else:
            self.assertIn(result['exact_r'], (Q(1), Q(3, 4)))
            params = result['representation']
            alpha, beta = params[:2]; delta = params[2] if len(params) == 3 else 0
            self.assertEqual(tuple(values), tuple((alpha * x + beta + delta * (x % 2)) % N for x in range(N)))
        self.assertLessEqual(result['relation_checks'], N)

    def test_certificate_classifies_every_word_n1_through_n4(self):
        for N in range(1, 5):
            for values in product(range(N), repeat=N):
                row = c.relative_energy_certificate(N, values)
                self.verify_witness(N, values, row)
                expected = 'affine' if c.affine_parameters(N, values) is not None else 'parity' if c.parity_parameters(N, values) is not None else 'upper_bound'
                self.assertEqual(row['kind'], expected)

    def test_certificate_n5_n6_examples_use_uniform_witness(self):
        for N in (5, 6):
            for values in (tuple(x * x % N for x in range(N)), (0,) * (N - 1) + (1,)):
                row = c.relative_energy_certificate(N, values)
                self.assertEqual(row['kind'], 'upper_bound')
                self.assertEqual(row['indicator_support'], tuple(range(N)))
                self.verify_witness(N, values, row)

    def test_certificate_wrap_parity_representations_and_boundaries(self):
        for N in (7, 8, 15, 16, 63, 64):
            for values in (tuple((3 * x + 5) % N for x in range(N)), (0,) * (N - 1) + (1,)):
                row = c.relative_energy_certificate(N, values)
                self.verify_witness(N, values, row)
            if N % 2 == 0:
                for alpha, beta, delta in ((0, 0, 1), (N - 1, N - 2, N - 1), (3, 2, N // 2)):
                    values = tuple((alpha * x + beta + delta * (x % 2)) % N for x in range(N))
                    row = c.relative_energy_certificate(N, values)
                    self.verify_witness(N, values, row)
                    self.assertEqual(row['exact_r'], 1 if 2 * delta % N == 0 else Q(3, 4))
                    self.assertEqual(row['relation_checks'], N)
        # The first failure begins near the cyclic end, not in the first N-3 windows.
        values = tuple(x % 2 for x in range(9))
        row = c.relative_energy_certificate(9, values)
        self.assertEqual(row['failed_window_start'], 6)
        self.verify_witness(9, values, row)

    def test_certificate_guards_before_scan(self):
        for N in (0, 65, True, Q(8), 8.0, '8', 10 ** 100):
            with self.assertRaises(ValueError): c.relative_energy_certificate(N, ())
        for values in ((0,), (0,) * 7 + (8,), (0,) * 7 + (-1,), (0,) * 7 + (True,),
                       (0,) * 7 + (Q(0),), iter((0,) * 8), None):
            with self.assertRaises(ValueError): c.relative_energy_certificate(8, values)


class PositiveDeletionTests(unittest.TestCase):
    def test_graph_convolution_crossmultiplied_bounds(self):
        self.assertEqual(c.check_graph_convolution(), {'mass_certificates': 12, 'holder_equality': True})
        cases = ((8, (0, 1, 1, 0, 0, 0, 0, 0), (0, 1, 2), (0, 1), 2),
                 (9, (1, 0, 0, 2, 0, 0, 0, 0, 0), (0, 3), (1, 2), 2))
        for N, values, J, S, t in cases:
            weights = tuple(Q(x + 1, x + 2) for x in range(N))
            row = c.graph_convolution_certificate(N, values, weights, J, S, t)
            self.assertGreaterEqual(row['energy'], row['inside_energy'] + row['outside_energy'])
            self.assertGreaterEqual(row['inside_energy'] + row['outside_energy'], row['two_mass_lower'])
            self.assertGreaterEqual(row['two_mass_lower'], row['rational_holder_lower'])
            self.assertEqual(row['M'], len({(x + y) % N for x in J for y in J}) * len({(x + y) % N for x in S for y in S}))
            if row['intervals']: self.assertLessEqual(row['M'], row['interval_cap'])

    def test_graph_convolution_full_support_zero_masses_and_interval_wrap(self):
        for N in (1, 2, 4, 8):
            row = c.graph_convolution_certificate(N, (0,) * N, (1,) * N, tuple(range(N)), (0,), 1)
            self.assertEqual(row['A'], 0)
            self.assertEqual(row['energy'], N ** 3)
            self.assertEqual(row['M'], N)
            self.assertEqual(row['inside_energy'], row['energy'])
        row = c.graph_convolution_certificate(4, (0, 0, 0, 0), (0, 1, 1, 1), (0,), (0,), 1)
        self.assertEqual(row['B'], 0)
        self.assertEqual(row['inside_energy'], 0)
        row = c.graph_convolution_certificate(4, (0, 1, 2, 0), (1,) * 4, (0, 1, 2), (0, 1, 2), 2)
        self.assertEqual(row['M'], 16)
        self.assertEqual(row['interval_cap'], 25)

    def test_graph_convolution_hypothesis_guards(self):
        base = (4, (1, 0, 0, 0), (1,) * 4, (0,), (1,), 1)
        invalid = [base[:3] + ((),) + base[4:], base[:4] + ((),) + base[5:],
                   base[:3] + ((1,),) + base[4:], base[:4] + ((0,),) + base[5:],
                   base[:-1] + (0,), base[:-1] + (True,), base[:-1] + (Q(1, 4),),
                   base[:3] + ((0, 0),) + base[4:], base[:4] + ((True,),) + base[5:]]
        for args in invalid:
            with self.subTest(args=args), self.assertRaises(ValueError): c.graph_convolution_certificate(*args)

    def test_arbitrary_retained_domain_including_deleted_points(self):
        result = c.check_deletion_model()
        self.assertEqual(result['admissible_triples'], 1863)
        self.assertEqual(result['triples_with_kept_deleted_points'], 1842)
        witness = result['equality_witness']
        self.assertEqual((witness['deleted'], witness['kept_deleted'], witness['lower_deleted']), (3, 3, 3))
        self.assertGreater(witness['kept'], witness['covered'])
        self.assertEqual(c.deletion_certificate(4, (), (), (0, 1, 2, 3), Q(1, 2))['deleted'], 4)
        self.assertEqual(c.deletion_certificate(4, (0, 1, 2, 3), (0, 1, 2, 3), (0, 1, 2, 3), Q(1, 2))['lower_deleted'], 0)

    def test_deletion_hypotheses_and_size_guards(self):
        for size in (0, 9, True, Q(5)):
            with self.assertRaises(ValueError): c.deletion_certificate(size, (), (), (), Q(1, 2))
        for rho in (0, 1, -1, True, 0.5, Q(3, 2)):
            with self.assertRaises(ValueError): c.deletion_certificate(4, (), (), (0, 1, 2, 3), rho)
        with self.assertRaisesRegex(ValueError, 'density'): c.deletion_certificate(4, (), (), (), Q(1, 2))
        with self.assertRaisesRegex(ValueError, 'covered'): c.deletion_certificate(4, (0, 1), (), (0, 1), Q(1, 2))
        with self.assertRaises(ValueError): c.deletion_certificate(4, (True,), (), (0, 1), Q(1, 2))

    def test_finite_surrogate_rounded_inequalities_and_scope(self):
        for E in (8, 16, 32):
            for u in (Q(1, 2), Q(2, 3), Q(3, 4)):
                row = c.finite_surrogate(E, u)
                self.assertEqual(row['gamma'], u ** 3)
                self.assertEqual(row['eta'], (u ** -8 - 1) ** 3)
                self.assertEqual(row['rho'], Q(E, E + 2))
                self.assertGreaterEqual(row['beta'], Q(1, E + 2))
                self.assertLess(row['lambda'], Q(1, 2))
                self.assertGreaterEqual(row['continuous_surrogate'], row['rounded_surrogate'])
                self.assertGreaterEqual(row['rounded_lower'], row['positive_constant'])
                self.assertGreaterEqual(row['rounded_lower'], row['sharper_lower'])
                self.assertGreaterEqual(row['positive_constant'], row['weaker_rational_constant'])
                self.assertGreaterEqual(row['half_beta'], Q(3, 16))
                if E >= 16: self.assertGreater(row['three_fifths_beta'], Q(3, 8))
        self.assertLess(c.finite_surrogate(8, Q(2, 3))['three_fifths_beta'], Q(3, 8))

    def test_surrogates_reject_actual_huge_or_undocumented_exponents(self):
        for E in (0, 4, 7, 9, 33, 1024, 1 << 1024, True, Q(8), 8.0):
            with self.assertRaises(ValueError): c.finite_surrogate(E, Q(2, 3))
        for u in (0, 1, 2, -1, True, 0.5, Q(1, 256), Q(255, 256), Q(1, 1 << c.MAX_BITS)):
            with self.assertRaises(ValueError): c.finite_surrogate(8, u)



class AbelianTargetTests(unittest.TestCase):
    def test_target_energy_matches_independent_ordered_quadruples(self):
        for N in (2, 3, 4, 5):
            weights = tuple(Q(x + 1, x + 2) for x in range(N))
            for target in (None, 3, 4, 7):
                values = tuple(x * x - 2 for x in range(N))
                if target is not None: values = tuple(v % target for v in values)
                expected = Q(0)
                for x, y, z, t in product(range(N), repeat=4):
                    diff = values[x] + values[y] - values[z] - values[t]
                    respected = diff == 0 if target is None else diff % target == 0
                    if (x + y - z - t) % N == 0 and respected:
                        expected += weights[x] * weights[y] * weights[z] * weights[t]
                self.assertEqual(c.target_respected_energy(N, values, weights, target), expected)
                row = c.abelian_small_certificate(N, values, target)
                self.assertEqual(row['uniform_energy'], c.target_respected_energy(N, values, (1,) * N, target))
                self.assertLessEqual(row['uniform_ratio'], row['proved_upper_bound'])

    def test_arbitrary_target_exhaustive_finite_regressions(self):
        row = c.check_abelian_targets()
        self.assertEqual(row['small_words'], 5 * sum(3 ** N for N in range(1, 7)))
        self.assertEqual(row['parity_identities'], 40)
        self.assertEqual(row['N6_bounds_exercised'], (Q(148, 216), Q(152, 216)))
        self.assertEqual(row['N5_bound'], Q(93, 125))
        self.assertGreater(row['N5_bound'], Q(8, 11))
        self.assertLess(row['N5_bound'], Q(3, 4))
        self.assertFalse(row['arbitrary_target_8_over_11_classification_claimed'])

    def test_n2_integer_parity_is_nonaffine_unlike_same_cyclic_target(self):
        self.assertEqual(c.abelian_small_certificate(2, (0, 1), None)['exact_r'], Q(3, 4))
        self.assertEqual(c.abelian_small_certificate(2, (0, 1), 4)['exact_r'], Q(3, 4))
        self.assertEqual(c.abelian_small_certificate(2, (0, 1), 2)['exact_r'], 1)
        for target in (None, 3, 4, 7):
            row = c.abelian_parity_identity(2, (1, 1), target)
            self.assertEqual((row['ordinary'], row['respected'], row['gap']), (8, 6, 0))
            for weights in ((Q(1, 3), Q(2, 5)), (0, 1), (0, 0)):
                row = c.abelian_parity_identity(2, weights, target)
                self.assertGreaterEqual(row['gap'], 0)

    def test_division_free_even_form_and_both_n6_cases(self):
        # In Z/6Z the step d=3 is not divisible by 2. No alpha is chosen.
        row = c.abelian_small_certificate(4, (0, 1, 3, 4), 6)
        self.assertEqual(row['kind'], 'even_normal_form')
        self.assertEqual(row['representation'], (0, 3, 1))
        self.assertEqual(row['exact_r'], Q(3, 4))
        nonconstant = c.abelian_small_certificate(6, (0, 0, 0, 1, 1, 1), None)
        constant = c.abelian_small_certificate(6, (0, 0, 1, 0, 0, 1), None)
        self.assertEqual(nonconstant['proved_upper_bound'], Q(148, 216))
        self.assertEqual(constant['proved_upper_bound'], Q(152, 216))
        self.assertNotEqual(nonconstant['Qh'][3], 36)
        self.assertEqual(constant['Qh'][3], 36)
        self.assertIsNone(nonconstant['exact_r']); self.assertIsNone(constant['exact_r'])

    def test_target_input_guards_and_signed_integer_labels(self):
        for target in (True, 0, 33, -1, Q(3), '3'):
            with self.assertRaises(ValueError): c.target_respected_energy(2, (0, 1), (1, 1), target)
        for values in ((0, 3), (-1, 0), (True, 0), (Q(1), 0), iter((0, 1))):
            with self.assertRaises(ValueError): c.target_respected_energy(2, values, (1, 1), 3)
        for values in ((-257, 0), (0, 257), (False, 1)):
            with self.assertRaises(ValueError): c.target_respected_energy(2, values, (1, 1), None)
        self.assertEqual(c.target_respected_energy(2, (-256, 256), (1, 1), None), 6)
        for N in (0, 7, True):
            with self.assertRaises(ValueError): c.abelian_small_certificate(N, (), None)
        for target in (0, 1, 2, True, 33):
            with self.assertRaises(ValueError): c.abelian_parity_identity(2, (1, 1), target)
        with self.assertRaises(ValueError): c.abelian_parity_identity(3, (1, 1, 1), None)


class ReplayTests(unittest.TestCase):
    def test_normal_and_optimized_cli_are_identical(self):
        script = ROOT / 'companion/exact_checks.py'
        command = [sys.executable, '-I', '-B', '-X', 'int_max_str_digits=640']
        normal = subprocess.run(command + [str(script)], check=True, capture_output=True, timeout=60)
        optimized = subprocess.run(command + ['-O', str(script)], check=True, capture_output=True, timeout=60)
        self.assertEqual(normal.stdout, optimized.stdout)
        self.assertEqual(normal.stderr, b''); self.assertEqual(optimized.stderr, b'')
        row = json.loads(normal.stdout)
        self.assertEqual(row['status'], 'passed')
        self.assertFalse(row['actual_theorem_exponent_constructed'])
        self.assertEqual(row['finite_surrogates'][0]['E'], 8)
        self.assertEqual(sum(r['words'] for r in row['small_moduli']), 11189)
        self.assertIn('written proofs', row['scope'])

    def test_cli_bad_argument_fails_under_both_modes(self):
        for flags in ([], ['-O']):
            result = subprocess.run([sys.executable, '-I', '-B', *flags,
                str(ROOT / 'companion/exact_checks.py'), '--size=999999999'],
                capture_output=True, timeout=5)
            self.assertNotEqual(result.returncode, 0)
            self.assertEqual(result.stdout, b'')
            self.assertIn(b'takes no arguments', result.stderr)


# Exact records are hard-coded below; manifest edits cannot choose new sources.
EXPECTED_SOURCES = [{'bytes': 15504,
  'canonical_base64_sha256': 'dadc947fadc5d912095cbd58adf10d6565de7b4856cf49cdf7c98789626d3d9d',
  'commit': '17f048dfa919de04a1989035a2d680ec0865c774',
  'git_blob_sha1': '97113b7afa6925a2dd4b76641eeaeff09597ab6a',
  'kind': 'git_blob',
  'name': 'Definitions.lean',
  'repository': 'VladimirReshetnikov/ProveIt',
  'repository_path': 'Combinatorics/Ramsey/Lean/GowersSzemeredi/Definitions.lean',
  'sha256': '17241a9ffa53e2c6b335eb326920952a7f3da25e5e5a601a7aca5606462f5e4b',
  'url': 'https://github.com/VladimirReshetnikov/ProveIt/blob/17f048dfa919de04a1989035a2d680ec0865c774/Combinatorics/Ramsey/Lean/GowersSzemeredi/Definitions.lean'},
 {'bytes': 24924,
  'canonical_base64_sha256': '87c759a76c5af16c7f31e60a6c890fc267d0625df5f47d269cd173c453a7ab4a',
  'commit': '17f048dfa919de04a1989035a2d680ec0865c774',
  'git_blob_sha1': '302e8a223f56dcdabf29f30ca3c80ac62a7adbfc',
  'kind': 'git_blob',
  'name': 'Section10.lean',
  'repository': 'VladimirReshetnikov/ProveIt',
  'repository_path': 'Combinatorics/Ramsey/Lean/GowersSzemeredi/Section10.lean',
  'sha256': '8b63d784485ba8291b614a9153399cae216d2adaf37c9770344521083523cb2d',
  'url': 'https://github.com/VladimirReshetnikov/ProveIt/blob/17f048dfa919de04a1989035a2d680ec0865c774/Combinatorics/Ramsey/Lean/GowersSzemeredi/Section10.lean'},
 {'bytes': 20864,
  'canonical_base64_sha256': '5a0a45312addf2b9bbe353db3b2a4d6f9c88fea28a3b5e834ca576fa3c53bfd7',
  'commit': '17f048dfa919de04a1989035a2d680ec0865c774',
  'git_blob_sha1': '5d91dce37bbca59fc76dfd30ec3a485d72ba583c',
  'kind': 'git_blob',
  'name': 'Sections14_15.lean',
  'repository': 'VladimirReshetnikov/ProveIt',
  'repository_path': 'Combinatorics/Ramsey/Lean/GowersSzemeredi/Sections14_15.lean',
  'sha256': 'cc7782c87e1e6261b744f13b7fd62082efcb1b6b45a24a31e694a915ebe6c13b',
  'url': 'https://github.com/VladimirReshetnikov/ProveIt/blob/17f048dfa919de04a1989035a2d680ec0865c774/Combinatorics/Ramsey/Lean/GowersSzemeredi/Sections14_15.lean'},
 {'bytes': 43323,
  'canonical_base64_sha256': '1c9b91e9991683a9028c469772f8321bdd6f12589ba7cdb08d0766014eb7865a',
  'commit': '17f048dfa919de04a1989035a2d680ec0865c774',
  'git_blob_sha1': 'c5c7d2bee91bc589de1d3082429f7ee3597e99f9',
  'kind': 'git_blob',
  'name': 'Section16.lean',
  'repository': 'VladimirReshetnikov/ProveIt',
  'repository_path': 'Combinatorics/Ramsey/Lean/GowersSzemeredi/Section16.lean',
  'sha256': 'be20dcf52ba6cb0bc54a03c194ad9b64f486562be032eccf788f14e97e1e65ed',
  'url': 'https://github.com/VladimirReshetnikov/ProveIt/blob/17f048dfa919de04a1989035a2d680ec0865c774/Combinatorics/Ramsey/Lean/GowersSzemeredi/Section16.lean'}]


class ProvenanceTests(unittest.TestCase):
    def test_exact_four_bundled_records_and_pins(self):
        path = ROOT / 'provenance/source_manifest.json'
        self.assertLessEqual(path.stat().st_size, 1024 * 1024)
        def no_duplicate_keys(pairs):
            result = {}
            for key, value in pairs:
                if key in result: raise ValueError('duplicate JSON key')
                result[key] = value
            return result
        record = json.loads(path.read_text(), object_pairs_hook=no_duplicate_keys)
        self.assertIs(type(record), dict)
        self.assertEqual(set(record), {'sources', 'external_references'})
        self.assertIs(type(record['sources']), list)
        self.assertEqual(len(record['sources']), 4)
        self.assertEqual(record['sources'], EXPECTED_SOURCES)
        self.assertIs(type(record['external_references']), list)
        self.assertLessEqual(len(record['external_references']), 16)
        self.assertTrue(all(type(row) is dict for row in record['external_references']))
        source_dir = ROOT / 'provenance/sources'
        self.assertEqual({p.name for p in source_dir.iterdir()}, {r['name'] for r in EXPECTED_SOURCES})
        for row in EXPECTED_SOURCES:
            source = source_dir / row['name']
            self.assertFalse(source.is_symlink())
            self.assertEqual(source.stat().st_nlink, 1)
            self.assertEqual(source.stat().st_size, row['bytes'])
            raw = source.read_bytes()
            self.assertEqual(len(raw), row['bytes'])
            self.assertEqual(hashlib.sha256(raw).hexdigest(), row['sha256'])
            header = ('blob ' + str(len(raw)) + '\0').encode('ascii')
            self.assertEqual(hashlib.sha1(header + raw).hexdigest(), row['git_blob_sha1'])
            self.assertEqual(hashlib.sha256(base64.b64encode(raw)).hexdigest(), row['canonical_base64_sha256'])
            self.assertEqual(row['kind'], 'git_blob')
            self.assertEqual(row['commit'], '17f048dfa919de04a1989035a2d680ec0865c774')
            self.assertEqual(row['url'], 'https://github.com/' + row['repository'] + '/blob/' + row['commit'] + '/' + row['repository_path'])


if __name__ == '__main__':
    unittest.main()
