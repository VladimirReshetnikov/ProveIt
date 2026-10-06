"""Run unchanged under python and python -O. No disabled assert statements."""
from copy import deepcopy
from fractions import Fraction
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

COMPANION = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(COMPANION))
from exact import (VerificationError, require, recurrence, radical_coefficients,
                   interleave, algebraic_residuals, square_root_one, reciprocal,
                   inverse_identity_evidence, inverse_residual, Laurent)
from permutations import (COUNTEREXAMPLES, alternating, baxter_value, baxter_vincular,
                          classical_separable, inverse, involutions,
                          counterexample_evidence, structural_class)
from safeio import write_fresh, read_regular
from verify import (REFERENCE_PREFIX, _expected_bytes, canonical_bytes,
                    decode_evidence, validate_evidence)


class ExactAlgebraTests(unittest.TestCase):
    def test_reference_and_separate_implementations(self):
        even, odd = recurrence(60)
        self.assertEqual((even, odd), radical_coefficients(60))
        self.assertEqual(interleave(even, odd)[:25], REFERENCE_PREFIX)
        for values in algebraic_residuals(even, odd).values():
            self.assertEqual(values, [0]*61)

    def test_old_recurrence_discrepancy(self):
        new = interleave(*recurrence(25))
        old = interleave(*recurrence(25, corrected=False))
        self.assertEqual(new[:20], old[:20])
        self.assertEqual((new[20], old[20]), (2168, 2166))
        self.assertEqual(new[21:25], [5080, 6014, 14594, 17252])

    def test_small_series_independent_known_values(self):
        self.assertEqual(square_root_one([Fraction(1), Fraction(-4)], 4),
                         [1, -2, -2, -4, -10])
        self.assertEqual(reciprocal([Fraction(1), Fraction(-1)], 7), [1]*8)
        self.assertEqual(radical_coefficients(0), ([1], [1]))

    def test_bad_series_and_limits_rejected(self):
        with self.assertRaises(VerificationError):
            square_root_one([Fraction(-1)], 2)
        with self.assertRaises(VerificationError):
            reciprocal([Fraction(0)], 2)
        for bad in (-1, True, 1.5):
            for method in (recurrence, radical_coefficients):
                with self.subTest(bad=bad, method=method.__name__):
                    with self.assertRaises(ValueError):
                        method(bad)

    def test_runtime_checks_survive_optimization(self):
        with self.assertRaises(VerificationError):
            require(False, 'must always fail')
        e, o = recurrence(20)
        e[10] += 1
        with self.assertRaises(VerificationError):
            algebraic_residuals(e, o)

    def test_inverse_all_four_symbolic_coefficients(self):
        evidence = inverse_identity_evidence()
        self.assertEqual(evidence['residual_coefficients_epsilon_0_through_4'], [[], [], [], [], []])
        encoded = evidence['coefficients_v1_v2_v3_v4']
        coefficients = [Laurent({tuple(term['powers']): Fraction(term['coefficient'])
                                 for term in value}) for value in encoded]
        self.assertEqual(len(coefficients), 4)
        for index in range(4):
            altered = coefficients.copy()
            altered[index] = altered[index] + 1
            residual = inverse_residual(altered)
            self.assertTrue(any(residual))
            self.assertEqual(residual[index+1], Laurent.variable(0))
        # Expanded v3 independently records every term and power.
        self.assertEqual(coefficients[2].terms, {
            (-3,2,1,0,0,0): Fraction(-1),
            (-2,0,2,0,0,0): Fraction(-1),
            (-2,1,0,1,0,0): Fraction(-1),
            (-1,0,0,0,1,0): Fraction(-1)})


class PermutationTests(unittest.TestCase):
    def test_both_small_forbidden_patterns(self):
        for p in ((2,4,1,3), (3,1,4,2)):
            self.assertFalse(baxter_value(p))
            self.assertFalse(baxter_vincular(p))
        for p in ((), (1,), (1,2,3,4), (4,3,2,1)):
            self.assertTrue(baxter_value(p))
            self.assertTrue(baxter_vincular(p))

    def test_baxter_is_not_replaced_with_classical_avoidance(self):
        p = (2,5,3,1,4)
        self.assertTrue(baxter_value(p))
        self.assertTrue(baxter_vincular(p))
        self.assertFalse(classical_separable(p))

    def test_two_counterexamples_and_outer_blocks(self):
        records = counterexample_evidence()
        self.assertEqual(len(records), 2)
        for p, record in zip(COUNTEREXAMPLES, records):
            self.assertEqual(len(p), 20)
            self.assertTrue(alternating(p))
            self.assertEqual(inverse(p), p)
            self.assertTrue(all(record['properties'].values()))
            self.assertEqual(record['quadruples_examined_by_literal_predicate'], 4845)
            self.assertNotEqual(inverse(record['alpha']), tuple(record['alpha']))

    def test_generator_uniqueness_and_cardinality(self):
        objects = list(involutions(8))
        self.assertEqual(len(objects), 764)
        self.assertEqual(len(set(objects)), 764)
        self.assertTrue(all(inverse(p) == p for p in objects))
        self.assertEqual(list(involutions(0)), [()])
        for invalid in ((1,1), (0,), (True,)):
            with self.assertRaises(ValueError):
                inverse(invalid)

    def test_unrestricted_rb8_has_fourteen_two_noninvolutive(self):
        objects = structural_class(4, True)
        self.assertEqual(len(objects), 14)
        noninvolutions = [p for p in objects if inverse(p) != p]
        self.assertEqual(set(noninvolutions), {
            (8,4,6,5,7,2,3,1), (8,6,7,2,4,3,5,1)})
        self.assertEqual(inverse(noninvolutions[0]), noninvolutions[1])


class EvidenceTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.payload = _expected_bytes()
        cls.data = decode_evidence(cls.payload)

    def test_full_finite_checks(self):
        data = self.data
        self.assertTrue(validate_evidence(data))
        checks = data['finite_exhaustive_checks']
        self.assertEqual(checks['all_permutations_predicate_comparison']['inclusive_length_bound'], 8)
        self.assertEqual(checks['all_involutions_without_pruning']['inclusive_length_bound'], 12)
        last = checks['structural_grammar']['rows'][-1]
        self.assertEqual(last['unrestricted_B_2m'], 16796)
        self.assertEqual(last['even_involutions'], 2168)
        self.assertEqual(last['odd_involutions_via_initial_fixed_point'], 5080)

    def test_bundled_evidence_matches_fresh_recomputation(self):
        self.assertEqual(read_regular(COMPANION/'evidence.json'), self.payload)

    def test_tampering_rejected(self):
        def bad_coeff(d):
            d['exact_coefficients']['recurrence_even'][10] += 1
        def coordinated_bad_coeff(d):
            for key in ('recurrence_even', 'radical_even'):
                d['exact_coefficients'][key][10] += 1
        def bad_counterexample(d):
            d['counterexamples'][0]['permutation'][0] = 12
        def false_result(d):
            d['counterexamples'][0]['properties']['involution'] = False
        def bad_inverse(d):
            d['formal_inverse']['coefficients_v1_v2_v3_v4'][2][0]['coefficient'] = '0'
        def bad_schema(d):
            d['schema'] += '.forged'
        def bool_instead_of_integer(d):
            d['conventions']['empty_permutation'] = True
        def missing_key(d):
            del d['sources']
        def extra_key(d):
            d['untrusted_digest'] = '0000'
        def bad_bound(d):
            d['finite_exhaustive_checks']['all_involutions_without_pruning']['inclusive_length_bound'] = 20
        for mutate in (bad_coeff, coordinated_bad_coeff, bad_counterexample, false_result,
                       bad_inverse, bad_schema, bool_instead_of_integer, missing_key,
                       extra_key, bad_bound):
            with self.subTest(mutation=mutate.__name__):
                candidate = deepcopy(self.data)
                mutate(candidate)
                with self.assertRaises(VerificationError):
                    validate_evidence(candidate)

    def test_strict_json(self):
        for payload in (b'{"a":1,"a":2}', b'{"a":NaN}', b'{"a":Infinity}',
                        b'{"a":-Infinity}', b'\xff', b'{'):
            with self.subTest(payload=payload):
                with self.assertRaises(VerificationError):
                    decode_evidence(payload)
        with self.assertRaises(VerificationError):
            validate_evidence([])
        with self.assertRaises(VerificationError):
            validate_evidence({'a': float('nan')})

    def test_normal_and_optimized_cli_are_byte_identical(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            outputs = []
            for option, filename in (([], 'normal.json'), (['-O'], 'optimized.json')):
                output = root/filename
                process = subprocess.run([sys.executable, *option, str(COMPANION/'verify.py'),
                                          '--output', str(output)], capture_output=True, text=True)
                self.assertEqual(process.returncode, 0, process.stderr)
                outputs.append(read_regular(output))
            self.assertEqual(outputs, [self.payload, self.payload])
            # A same-path retry must fail and leave the existing bytes untouched.
            process = subprocess.run([sys.executable, '-O', str(COMPANION/'verify.py'),
                                      '--output', str(root/'normal.json')], capture_output=True)
            self.assertNotEqual(process.returncode, 0)
            self.assertEqual(read_regular(root/'normal.json'), self.payload)


class SafeIOTests(unittest.TestCase):
    def test_no_overwrite(self):
        with tempfile.TemporaryDirectory() as directory:
            destination = Path(directory)/'result.json'
            write_fresh(destination, b'original')
            with self.assertRaises(FileExistsError):
                write_fresh(destination, b'replacement')
            self.assertEqual(read_regular(destination), b'original')

    def test_output_symlink_refused_including_dangling(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            target = root/'real.json'
            target.write_bytes(b'original')
            for leaf, link_target in (('link.json', target), ('dangling.json', root/'absent.json')):
                link = root/leaf
                link.symlink_to(link_target)
                with self.assertRaises(OSError):
                    write_fresh(link, b'changed')
            self.assertEqual(target.read_bytes(), b'original')
            self.assertFalse((root/'absent.json').exists())

    def test_parent_symlink_refused_for_read_and_write(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            real = root/'real'
            real.mkdir()
            (real/'existing').write_bytes(b'original')
            link = root/'alias'
            link.symlink_to(real, target_is_directory=True)
            with self.assertRaises(OSError):
                write_fresh(link/'new', b'changed')
            with self.assertRaises(OSError):
                read_regular(link/'existing')
            self.assertFalse((real/'new').exists())

    def test_input_symlink_and_directory_refused(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            target = root/'input.json'
            target.write_bytes(b'{}')
            link = root/'link.json'
            link.symlink_to(target)
            with self.assertRaises(OSError):
                read_regular(link)
            with self.assertRaises(VerificationError):
                read_regular(root)

    def test_parent_traversal_and_oversize_refused(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            with self.assertRaises(ValueError):
                write_fresh(str(root)+'/../escape', b'no')
            large = root/'large'
            large.write_bytes(b'abcdef')
            with self.assertRaises(VerificationError):
                read_regular(large, maximum_bytes=5)


if __name__ == '__main__':
    unittest.main()
