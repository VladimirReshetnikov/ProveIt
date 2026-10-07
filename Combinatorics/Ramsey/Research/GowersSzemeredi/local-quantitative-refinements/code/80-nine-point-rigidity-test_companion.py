#!/usr/bin/env python3
"""Exact public-companion regression and defensive-input tests."""
import sys
sys.dont_write_bytecode = True
import ast
from collections import Counter
from fractions import Fraction
from itertools import product
import json
from pathlib import Path
import random
import subprocess
import unittest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
from companion import exact_checks as e


class EnergyTests(unittest.TestCase):
    def test_zero_rank_and_singletons(self):
        self.assertEqual(e.points(0), ((),))
        self.assertEqual(e.energy(0, (123,), (Fraction(2, 3),)), e.Energy(Fraction(16, 81), Fraction(16, 81)))
        for rank in range(4):
            size = 3 ** rank
            self.assertEqual(e.indicator_energy(rank, (0,) * size, (size - 1,)), e.Energy(1, 1))

    def test_pair_and_triple_oracles(self):
        rng = random.Random(292)
        for rank in (0, 1, 1, 2, 2, 3):
            size = 3 ** rank
            values = tuple(rng.randrange(-10, 11) for _ in range(size))
            weights = tuple(Fraction(rng.randrange(1, 4), rng.randrange(1, 4)) for _ in range(size))
            for modulus in (None, 1, 2, 3, 6, 4096):
                with self.subTest(rank=rank, modulus=modulus):
                    self.assertEqual(e.energy(rank, values, weights, modulus),
                                     e.energy(rank, values, weights, modulus, 'triples'))

    def test_full_source_energy(self):
        for rank in range(4):
            size = 3 ** rank
            self.assertEqual(e.energy(rank, (0,) * size, (1,) * size), e.Energy(size ** 3, size ** 3))

    def test_scaling_and_translation(self):
        values = (0, 1, 3, -1, 0, 1, 2, 3, 4)
        weights = (1, 2, 0, 1, 3, 2, 4, 1, 1)
        actual = e.energy(2, values, weights, 6)
        self.assertEqual(e.energy(2, tuple(v + 12 for v in values), weights, 6), actual)
        self.assertEqual(e.energy(2, values, tuple(Fraction(w, 5) for w in weights), 6),
                         e.Energy(Fraction(actual.ordinary, 625), Fraction(actual.respected, 625)))
        domain = e.points(2)
        index = {p: i for i, p in enumerate(domain)}
        permutation = tuple(index[((x + 1) % 3, (y + 2) % 3)] for x, y in domain)
        self.assertEqual(e.energy(2, tuple(values[i] for i in permutation), tuple(weights[i] for i in permutation), 6), actual)
        affine_added = tuple(value + 2 * x + 4 * y for value, (x, y) in zip(values, domain))
        self.assertEqual(e.energy(2, affine_added, weights, 6), actual)

    def test_exact_derivative_energy_identity(self):
        domain = e.points(2)
        index = {p: i for i, p in enumerate(domain)}
        maps = ((1,) + (0,) * 8, tuple(y for _, y in domain), tuple(x + 3 * y for x, y in domain))
        for values, modulus in product(maps, (None, 2, 3, 6)):
            energies = []
            for h, k in domain:
                derivatives = [values[index[((x + h) % 3, (y + k) % 3)]] - values[i]
                               for i, (x, y) in enumerate(domain)]
                if modulus is not None:
                    derivatives = [value % modulus for value in derivatives]
                energies.append(sum(count * count for count in Counter(derivatives).values()))
            self.assertEqual(sum(energies), e.energy(2, values, (1,) * 9, modulus).respected)
            if values == maps[0] and modulus == 2:
                self.assertEqual(energies, [81] + [53] * 8)

    def test_maximum_accepted_bounds(self):
        self.assertEqual(e.energy(0, (-4096,), (Fraction(e.MAX_WEIGHT, e.MAX_WEIGHT - 1),), 4096).ratio, 1)
        self.assertEqual(e.support_weights(2, (0, 4, 8)), (1, 0, 0, 0, 1, 0, 0, 0, 1))
        self.assertEqual(e.energy(1, (0, 1, 2), (0, 1, 0)).ratio, 1)


class CertificateTests(unittest.TestCase):
    def test_line_formula(self):
        data = e.check_lines()
        self.assertEqual(data['cases'], 2150)
        self.assertEqual((data['ordinary'], data['automatic_respected'], data['per_midpoint_equality']), (27, 15, 4))
        self.assertEqual(e.energy(1, (0, 1, 3), (1, 1, 1)), e.Energy(27, 15))
        self.assertEqual(e.energy(1, (0, 1, 2), (1, 1, 1)), e.Energy(27, 19))

    def test_partitions_and_integer_relation_certificates(self):
        data = e.check_derivative_partitions()
        self.assertEqual(data['partitions_of_nine'], 30)
        self.assertEqual(data['nonconstant_above_45'], ((8, 1), (7, 2), (7, 1, 1)))
        self.assertEqual(len(data['certificate_rows']), 4)
        self.assertEqual(sum('forced_equal' in row for row in data['certificate_rows']), 3)
        for certificate in data['certificate_rows']:
            rows = certificate['cycle_rows']
            if 'forced_equal' in certificate:
                info = certificate['forced_equal']
                i, j = info['colors']
                expected = tuple(int(k == i) - int(k == j) for k in range(len(rows[0])))
                actual = tuple(sum(c * row[k] for c, row in zip(info['coefficients'], rows))
                               for k in range(len(expected)))
                self.assertEqual(actual, expected)
            else:
                for key, expected in (('majority_three_zero', (3, 0)), ('exceptional_difference_two_zero', (-2, 2))):
                    self.assertEqual(tuple(sum(c * row[k] for c, row in zip(certificate[key], rows)) for k in range(2)), expected)
        self.assertEqual(data['full_plane_bound'].ratio, Fraction(49, 81))

    def test_spike(self):
        data = e.check_spike()
        self.assertEqual(data['six_point'], e.Energy(162, 106))
        self.assertEqual(data['six_point'].ratio, Fraction(53, 81))
        self.assertEqual(data['full_plane'], e.Energy(729, 505))
        self.assertEqual(data['support'], (0, 1, 3, 4, 6, 7))
        self.assertEqual(data['ordinary_spike_polynomial'], (81, 56, 24, 0, 1))
        self.assertEqual(data['respected_spike_polynomial'], (81, 0, 24, 0, 1))
        self.assertEqual(data['weighted_six_point'], e.Energy(Fraction(149121, 625), Fraction(93121, 625)))
        self.assertLess(data['weighted_six_point'].ratio, Fraction(5, 8))

    def test_generic_row_constants_are_symbolic(self):
        data = e.check_generic_two_row_spike()
        self.assertEqual(data['source_sums'], 9)
        self.assertTrue(data['unique_row_constant_pair_at_each_source_sum'])
        self.assertEqual(data['ordinary_polynomial'], (81, 56, 24, 0, 1))
        self.assertEqual(data['respected_polynomial'], (81, 0, 24, 0, 1))

    def test_analytic_spike_formulas_and_table(self):
        data = e.check_spike_all_supports()
        self.assertEqual((data['supports_checked'], data['supports_omitting_spike'], data['supports_containing_spike']), (511, 255, 256))
        for name in ('formula_A_checks', 'formula_B_checks', 'formula_C_checks', 'formula_D_checks'):
            self.assertEqual(data[name], 256)
        self.assertEqual(data['minimizing_support_masks'], (63, 219, 245, 365, 371, 413, 427, 455))
        self.assertEqual(data['minimizing_support_count'], 8)
        self.assertEqual(data['minimum'], Fraction(53, 81))
        self.assertEqual([row['minimum'] for row in data['analytic_table']],
                         [1, 1, Fraction(19, 27), Fraction(7, 9), Fraction(19, 27),
                          Fraction(53, 81), Fraction(183, 271), Fraction(13, 19), Fraction(505, 729)])
        self.assertEqual(sum(case['supports'] for row in data['analytic_table'] for case in row['cases']), 256)
        six = data['analytic_table'][5]
        self.assertEqual([(case['ordinary'], case['T']) for case in six['cases']], [(150, 10), (150, 12), (162, 14)])
        self.assertEqual(six['cases'][-1]['supports'], 8)

    def test_improved_constants_and_integer_weights(self):
        data = e.check_improved_constants()
        self.assertEqual(data['increasing_constants'], (Fraction(5, 9), Fraction(49, 81), Fraction(13303, 21303), Fraction(5, 8), Fraction(53, 81)))
        self.assertEqual(data['integer_witness'], e.Energy(149121, 93121))
        self.assertEqual(data['integer_witness'].ratio, Fraction(13303, 21303))
        self.assertEqual(set(data['integer_weights']), {0, 5, 8})
        self.assertEqual(data['integer_weights'].count(8), 1)
        self.assertEqual(data['integer_weights'].count(5), 5)
        self.assertEqual(data['gamma_stationary_polynomial'], (-27, 0, 8, 0, 1))
        self.assertEqual(data['numerator_reduced_modulo_stationary_polynomial'], (108, 0, 16))
        self.assertEqual(data['gamma_rational_lower_bound'], Fraction(93, 149))
        self.assertEqual(e.check_derivative_partitions()['low_histogram_full_plane_bound'], e.Energy(729, 441))

    def test_exhaustive_c2_classification(self):
        data = e.check_c2_maps()
        self.assertEqual(data['families'], dict(constant=2, cut=24, outside=486))
        self.assertEqual(data['map_support_pairs'], 261632)
        self.assertEqual(data['maximum_full_indicator_outside'], Fraction(505, 729))
        self.assertEqual(data['maximum_hereditary_indicator_outside'], Fraction(53, 81))
        self.assertEqual(len(data['full_maximizing_maps']), 18)
        self.assertEqual(data['full_maximizing_maps'], data['hereditary_maximizing_maps'])
        self.assertEqual(sum(row['maps'] for row in data['outside_minimum_distribution']), 486)
        self.assertEqual(data['independent_pair_crosschecks'], 3066)
        self.assertEqual(data['all_map_full_plane_pair_crosschecks'], 512)

    def test_integer_cut_all_indicators(self):
        data = e.check_integer_cut_indicators()
        self.assertEqual(data['supports_checked'], 511)
        self.assertEqual(data['minimum'], Fraction(13, 19))
        self.assertEqual(data['attaining_support_masks'], (383, 495, 509))
        self.assertEqual(data['attaining_support_count'], 3)
        self.assertEqual(data['attaining_energy'], e.Energy(456, 312))
        self.assertEqual(data['full_plane'].ratio, Fraction(19, 27))
        self.assertLess(data['minimum'], data['full_plane'].ratio)

    def test_all_rank_three_candidates(self):
        data = e.check_rank_three_sections()
        self.assertEqual((data['candidate_subsets'], data['valid_subsets']), (26 ** 3, 80))
        self.assertEqual((data['empty'], data['full'], data['hyperplanes'], data['hyperplane_complements']), (1, 1, 39, 39))

    def test_symbolic_cut_polynomials(self):
        data = e.check_cut_polynomials()
        self.assertEqual([row['target'] for row in data['nonaffine_cases']], ['Z', 'C2', 'C4', 'C6', 'C9'])
        for row in data['nonaffine_cases']:
            self.assertEqual(row['ordinary'], (6, 8, 12, 0, 1))
            self.assertEqual(row['respected'], (6, 0, 12, 0, 1))
        self.assertEqual(data['affine_C3']['ordinary'], data['affine_C3']['respected'])
        self.assertEqual(data['positive_minimizer_polynomial'], (-2, 0, 4, 0, 1))
        self.assertEqual(data['threshold_difference'], Fraction(52, 2025))
        self.assertEqual(e.cut_polynomials(1)[0], e.cut_polynomials(1)[1])


class DefensiveInputTests(unittest.TestCase):
    def test_rank_validation(self):
        for rank in (None, True, False, -1, 4, 2.0, '2', 1 << 50):
            with self.subTest(rank=rank), self.assertRaises(ValueError):
                e.energy(rank, (0,), (1,))
            with self.subTest(rank=rank), self.assertRaises(ValueError):
                e.points(rank)

    def test_values_validation(self):
        for values in (None, [], [0], (), (0, 1), (True,), (1.0,), ('1',), (4097,), (-4097,), (Fraction(1),)):
            with self.subTest(values=values), self.assertRaises(ValueError):
                e.energy(0, values, (1,))

    def test_weights_validation(self):
        for weights in (None, [], [1], (), (1, 2), (0,), (-1,), (True,), (1.0,), ('1',),
                        (1 << 31,), (Fraction(1, 1 << 31),)):
            with self.subTest(weights=weights), self.assertRaises(ValueError):
                e.energy(0, (0,), weights)

    def test_modulus_and_method_validation(self):
        for modulus in (True, False, 0, -1, 4097, 2.0, '2', Fraction(2)):
            with self.subTest(modulus=modulus), self.assertRaises(ValueError):
                e.energy(0, (0,), (1,), modulus)
            with self.subTest(modulus=modulus), self.assertRaises(ValueError):
                e.cut_polynomials(modulus)
        for method in (None, True, '', 'quadruples', [], 1):
            with self.subTest(method=method), self.assertRaises(ValueError):
                e.energy(0, (0,), (1,), method=method)

    def test_support_validation(self):
        for support in (None, [], [0], (), (True,), (0.0,), ('0',), (-1,), (9,), (0, 0), (2, 1), tuple(range(10))):
            with self.subTest(support=support), self.assertRaises(ValueError):
                e.indicator_energy(2, (0,) * 9, support)

    def test_partition_validation(self):
        for total in (None, True, False, 0, -1, 10, 1.0, '1'):
            with self.subTest(total=total), self.assertRaises(ValueError):
                e.integer_partitions(total)
        for total in range(1, 10):
            partitions = e.integer_partitions(total)
            self.assertTrue(all(sum(p) == total and tuple(sorted(p, reverse=True)) == p for p in partitions))
            self.assertEqual(len(partitions), len(set(partitions)))

    def test_energy_and_guard_validation(self):
        for values in ((0, 0), (1, 2), (1, -1), (True, 1), (1, False), (1.0, 1), (1, Fraction(-1)), (1 << 4097, 0)):
            with self.subTest(values=values), self.assertRaises(ValueError):
                e.Energy(*values)
        with self.assertRaises(RuntimeError):
            e.require(False, 'deliberate failure')
        for condition, message in ((1, 'x'), (None, 'x'), (True, 1)):
            with self.assertRaises(ValueError):
                e.require(condition, message)

    def test_json_encoding(self):
        self.assertEqual(e.jsonable(Fraction(13, 19)), '13/19')
        self.assertEqual(e.jsonable(e.Energy(162, 106)), dict(ordinary=162, respected=106, ratio='53/81'))
        for value in (0.5, complex(1, 0), {1, 2}, {1: 2}, object()):
            with self.subTest(value=value), self.assertRaises(ValueError):
                e.jsonable(value)


class CommandLineTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.script = str(ROOT / 'companion/exact_checks.py')
        cls.normal = subprocess.run([sys.executable, '-I', '-B', '-X', 'int_max_str_digits=640', cls.script],
                                    capture_output=True, text=True, check=True, timeout=90)
        cls.optimized = subprocess.run([sys.executable, '-I', '-B', '-O', '-X', 'int_max_str_digits=640', cls.script],
                                       capture_output=True, text=True, check=True, timeout=90)
        cls.summary = json.loads(cls.normal.stdout)

    def test_deterministic_normal_and_optimized_receipt(self):
        self.assertEqual(self.normal.stdout, self.optimized.stdout)
        self.assertEqual(self.normal.stderr, '')
        self.assertEqual(self.optimized.stderr, '')
        self.assertEqual((self.summary['report'], self.summary['schema_version'], self.summary['status']), (292, 1, 'passed'))
        self.assertEqual(self.summary['integer_cut_indicators']['minimum'], '13/19')
        self.assertEqual(self.summary['rank_three_sections']['candidate_subsets'], 17576)
        self.assertEqual(self.summary['c2_maps']['map_support_pairs'], 261632)

    def test_unknown_arguments_rejected(self):
        for arg in ('--output-dir=/tmp/example', '--quick', '--max-rank=99', 'extra'):
            result = subprocess.run([sys.executable, '-I', '-B', self.script, arg], capture_output=True, text=True, timeout=10)
            self.assertEqual(result.returncode, 2)
            self.assertEqual(result.stdout, '')

    def test_no_assert_or_floating_point_constants(self):
        tree = ast.parse(Path(self.script).read_text())
        self.assertFalse(any(isinstance(node, ast.Assert) for node in ast.walk(tree)))
        self.assertFalse(any(isinstance(node, ast.Constant) and type(node.value) is float for node in ast.walk(tree)))

    def test_optimized_invalid_inputs_still_fail(self):
        source = '''
import sys
sys.path.insert(0, sys.argv[1])
from companion import exact_checks as e
cases = [lambda: e.energy(True, (0,), (1,)), lambda: e.energy(0, (False,), (1,)),
         lambda: e.energy(0, (0,), (True,)), lambda: e.energy(0, (0,), (1,), True),
         lambda: e.support_weights(2, (0, 0)), lambda: e.integer_partitions(10),
         lambda: e.cut_polynomials(0), lambda: e.Energy(1, 2)]
for case in cases:
    try: case()
    except ValueError: pass
    else: raise RuntimeError('invalid input accepted under optimization')
try: e.require(False, 'expected')
except RuntimeError: pass
else: raise RuntimeError('correctness guard disabled')
print('passed')
'''
        result = subprocess.run([sys.executable, '-I', '-O', '-B', '-c', source, str(ROOT)],
                                capture_output=True, text=True, check=True, timeout=10)
        self.assertEqual(result.stdout, 'passed\n')


if __name__ == '__main__':
    unittest.main()
