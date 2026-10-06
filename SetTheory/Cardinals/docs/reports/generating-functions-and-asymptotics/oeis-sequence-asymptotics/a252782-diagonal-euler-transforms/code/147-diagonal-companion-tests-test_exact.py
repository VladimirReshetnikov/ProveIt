"""Tests use unittest's explicit failure methods, which remain active under -O."""
from dataclasses import fields, is_dataclass
from fractions import Fraction as F
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
import diagonal_euler as de
import certificate as cert
import fixtures as fx


class CoefficientTests(unittest.TestCase):
    def test_both_source_prefixes_three_independent_engines(self):
        for eps, expected in ((1, fx.PLUS_PREFIX), (-1, fx.MINUS_PREFIX)):
            for method in ("euler", "product", "atoms"):
                with self.subTest(epsilon=eps, engine=method):
                    self.assertEqual(tuple(de.diagonal(n, eps, method) for n in range(12)), expected)

    def test_full_rows_and_frozen_exponent(self):
        for exponent in (0, 1, 2, 3, 5, 9):
            for degree in range(13):
                for eps in (1, -1):
                    with self.subTest(exponent=exponent, degree=degree, epsilon=eps):
                        row = de.euler_row(exponent, degree, eps)
                        self.assertEqual(row, de.direct_product_row(exponent, degree, eps))
                        self.assertEqual(row, de.logarithmic_atom_row(exponent, degree, eps))
        self.assertNotEqual(de.euler_row(2, 3, 1)[3], de.diagonal(3, 1))

    def test_all_engines_through_24(self):
        for eps in (1, -1):
            for n in range(25):
                row = de.euler_row(n, n, eps)
                self.assertEqual(de.direct_product_row(n, n, eps), row)
                self.assertEqual(de.logarithmic_atom_row(n, n, eps), row)

    def test_literal_profile_identity_both_signs(self):
        for n in range(11):
            for eps in (1, -1):
                self.assertEqual(de.profile_identity(n, eps), de.diagonal(n, eps))

    def test_distinct_binomial_vanishing(self):
        self.assertEqual(de.direct_product_row(0, 8, -1), (1, 1, 1, 2, 2, 3, 4, 5, 6))

    def test_zero_degree(self):
        for engine in (de.euler_row, de.direct_product_row, de.logarithmic_atom_row):
            self.assertEqual(engine(0, 0, 1), (1,))
            self.assertEqual(engine(7, 0, -1), (1,))

    def test_sign_difference_nonnegative(self):
        for n in range(2, 25):
            self.assertGreater(de.diagonal(n, 1), de.diagonal(n, -1))

    def test_normalization_exact(self):
        self.assertEqual(de.normalization(6), F(3 ** 12, 2))
        self.assertEqual(de.normalization(0), F(1))
        self.assertIs(type(de.normalization(8)), F)

    def test_falling_polynomial_values(self):
        self.assertEqual(de.falling(5, 3), 60)
        self.assertEqual(de.falling(2, 3), 0)
        self.assertEqual(de.falling(-1, 3), -6)
        self.assertEqual(de.falling(F(3, 2), 2), F(3, 4))
        self.assertEqual(de.falling(0, 0), 1)

    def test_relative_coefficients_all_residues(self):
        cert.check_relative_coefficients()


class EnumerationTests(unittest.TestCase):
    def test_all_common_fixtures(self):
        for f in fx.COMMON:
            with self.subTest(residue=f.residue):
                result = cert.sector_certificate(f, False)
                self.assertEqual(result["profile_count"], f.profile_count)

    def test_all_difference_fixtures(self):
        for f in fx.DIFFERENCE:
            with self.subTest(residue=f.residue):
                result = cert.sector_certificate(f, True)
                self.assertEqual(result["profile_count"], f.profile_count)

    def test_exact_degree_bound_minimality(self):
        for f in fx.COMMON + fx.DIFFERENCE:
            d0 = de.degree_bound(f.residue, f.absolute_floor)
            self.assertLess(9 ** f.residue * de.Q6 ** d0, f.absolute_floor ** 6)
            self.assertGreaterEqual(9 ** f.residue * de.Q6 ** (d0 - 1), f.absolute_floor ** 6)

    def test_eligible_atoms_complete_necessary_condition(self):
        for f in fx.COMMON + fx.DIFFERENCE:
            expected = set(f.eligible_atoms)
            B = f.absolute_floor ** 6 / 9 ** f.residue
            for j in range(1, f.degree_exclusive):
                for k in range(1, (f.degree_exclusive - 1) // j + 1):
                    if (j, k) == (3, 1):
                        continue
                    self.assertEqual((j, k) in expected, de.Atom(j, k).loss6 >= B)

    def test_atom_inequality_finite_certificate_range(self):
        for j in range(1, 43):
            for k in range(1, 43 // j + 1):
                if (j, k) == (3, 1):
                    continue
                self.assertLessEqual(j ** 2, 2 ** (j * k))
                self.assertLess(de.Atom(j, k).loss6, 1)
                self.assertEqual(j ** 2 == 2 ** (j * k), (j, k) in ((2, 1), (4, 1)))

    def test_pruned_equals_unpruned_small_bound(self):
        # Chosen floors give D0 <= 10; compare complete profile sets, both parities.
        for r, floor in ((0, F(9, 10)), (1, F(7, 5)), (2, F(5, 2))):
            d0 = de.degree_bound(r, floor)
            self.assertLessEqual(d0, 10)
            all_small = de.all_profiles_through(max(0, d0 - 1))
            for odd in (False, True):
                expected = {p for p in all_small if p.degree < d0 and p.degree % 3 == r
                            and p.phase >= floor and (not odd or p.sign_exponent % 2)}
                self.assertEqual(set(de.enumerate_sectors(r, floor, odd).profiles), expected)

    def test_inclusive_cutoff(self):
        result = de.enumerate_sectors(0, F(8, 9))
        self.assertIn((F(8, 9), 2), de.grouped_terms(result))
        self.assertNotIn((F(8, 9), 2), de.grouped_terms(de.enumerate_sectors(0, F(8, 9) + F(1, 10000))))

    def test_above_maximal_phase_empty(self):
        for r in range(3):
            result = de.enumerate_sectors(r, 10)
            self.assertEqual(result.degree_exclusive, 0)
            self.assertEqual(result.atoms, ())
            self.assertEqual(result.profiles, ())

    def test_empty_profile(self):
        p = de.Profile(())
        self.assertEqual((p.degree, p.ell, p.sign_exponent), (0, 0, 0))
        self.assertEqual((p.coefficient, p.phase, p.loss6), (F(1), F(1), F(1)))
        self.assertEqual(de.enumerate_sectors(0, 1).profiles, (p,))

    def test_marked_atom_sign_and_factorial(self):
        p = de.Profile(((de.Atom(1, 2), 1), (de.Atom(2, 1), 2)))
        self.assertEqual(p.coefficient, F(1, 4))
        self.assertEqual(p.signed_coefficient(1), F(1, 4))
        self.assertEqual(p.signed_coefficient(-1), F(-1, 4))
        self.assertEqual(p.phase, F(4, 9))
        self.assertEqual(p.loss6, p.phase ** 6)

    def test_even_sign_exponent_and_subtraction(self):
        p = de.Profile(((de.Atom(1, 2), 2),))
        self.assertEqual(p.sign_exponent, 2)
        self.assertEqual(p.signed_coefficient(1), p.signed_coefficient(-1))
        for f in fx.DIFFERENCE:
            all_result = de.enumerate_sectors(f.residue, f.absolute_floor)
            odd_result = de.enumerate_sectors(f.residue, f.absolute_floor, True)
            self.assertEqual(de.grouped_terms(all_result, difference=True),
                             de.grouped_terms(odd_result, difference=True))
            plus, minus = de.grouped_terms(all_result, 1), de.grouped_terms(all_result, -1)
            subtraction = {k: plus.get(k, 0) - minus.get(k, 0) for k in set(plus) | set(minus)}
            self.assertEqual({k: v for k, v in subtraction.items() if v},
                             de.grouped_terms(odd_result, difference=True))

    def test_exact_profile_counts_without_parity_filter(self):
        self.assertEqual(tuple(len(de.enumerate_sectors(f.residue, f.absolute_floor).profiles)
                               for f in fx.DIFFERENCE), (114, 95, 79))


class InverseAlgebraTests(unittest.TestCase):
    def test_bernoulli_fixture(self):
        self.assertEqual(de.bernoulli_numbers(10), fx.BERNOULLI_PREFIX)

    def test_bernoulli_polynomial_difference_identity(self):
        for n in range(1, 11):
            for x in (F(-1, 3), F(0), F(1, 3), F(2)):
                self.assertEqual(de.bernoulli_polynomial(n, x + 1) - de.bernoulli_polynomial(n, x),
                                 n * x ** (n - 1))

    def test_shifted_stirling_rational_coefficients(self):
        self.assertEqual(tuple(de.shifted_stirling_coefficient(r, 1) for r in range(3)), fx.G_FIRST)
        self.assertEqual(de.shifted_stirling_coefficient(0, 2), 0)
        self.assertEqual(de.shifted_stirling_coefficient(0, 3), F(-3, 40))

    def test_leading_model_and_adjacent_ratios(self):
        cert.inverse_algebra_certificate()
        self.assertEqual(de.leading_model(4), 384)
        self.assertEqual(de.leading_model(2), 4)
        self.assertEqual(de.leading_model(0), 1)
        with self.assertRaises(ValueError):
            de.leading_model(1)

    def test_phase_collision(self):
        self.assertEqual(F(8, 9) ** 2, F(64, 81))

    def test_tail_onset_and_monotonicity(self):
        self.assertLess(de.tail_onset_sixth_power(192), 1)
        self.assertLess(de.Q6 ** 6, F(1, 2))
        for n in range(17, 210):
            self.assertLess(de.tail_onset_sixth_power(n + 1), de.tail_onset_sixth_power(n))
        self.assertGreater(de.tail_onset_sixth_power(16), 1)


class ValidationTests(unittest.TestCase):
    def test_noninteger_degrees_and_exponents_rejected(self):
        for engine in (de.euler_row, de.direct_product_row, de.logarithmic_atom_row):
            for bad in (True, False, 1.0, F(1), "1", None):
                with self.subTest(engine=engine.__name__, bad=bad):
                    with self.assertRaises(TypeError):
                        engine(bad, 1, 1)
                    with self.assertRaises(TypeError):
                        engine(1, bad, 1)
            with self.assertRaises(ValueError):
                engine(-1, 2, 1)
            with self.assertRaises(ValueError):
                engine(1, -1, 1)

    def test_bad_signs_rejected(self):
        for bad in (0, 2, -2):
            with self.assertRaises(ValueError):
                de.diagonal(2, bad)
        for bad in (True, 1.0, F(1), "-1", None):
            with self.assertRaises(TypeError):
                de.diagonal(2, bad)

    def test_bad_methods_rejected(self):
        with self.assertRaises(ValueError):
            de.diagonal(2, 1, "unknown")
        with self.assertRaises(TypeError):
            de.diagonal(2, 1, [])

    def test_bad_residues_rejected(self):
        for bad in (-1, 3):
            with self.assertRaises(ValueError):
                de.enumerate_sectors(bad, F(1))
        for bad in (True, F(1), 1.0, "1"):
            with self.assertRaises(TypeError):
                de.enumerate_sectors(bad, F(1))

    def test_bad_rational_cutoffs_rejected(self):
        for bad in (F(0), F(-1), 0):
            with self.assertRaises(ValueError):
                de.enumerate_sectors(0, bad)
        for bad in (0.7, True, "7/10", None):
            with self.assertRaises(TypeError):
                de.enumerate_sectors(0, bad)
        with self.assertRaises(TypeError):
            de.enumerate_sectors(0, F(1), 1)

    def test_bad_atoms_rejected(self):
        for pair in ((0, 1), (1, 0), (-1, 1), (3, 1)):
            with self.assertRaises(ValueError):
                de.Atom(*pair)
        for pair in ((True, 1), (2.0, 1), (1, F(2))):
            with self.assertRaises(TypeError):
                de.Atom(*pair)

    def test_bad_profiles_rejected(self):
        a, b = de.Atom(1, 1), de.Atom(2, 1)
        for entries in ([], ((a, 1.0),), ((a, True),), (("atom", 1),), ((a,),)):
            with self.assertRaises(TypeError):
                de.Profile(entries)
        for entries in (((a, 0),), ((a, -1),), ((a, 1), (a, 2)), ((b, 1), (a, 1))):
            with self.assertRaises(ValueError):
                de.Profile(entries)

    def test_bad_auxiliary_inputs(self):
        for func, args in ((de.falling, (1.0, 2)), (de.falling, (1, True)),
                           (de.bernoulli_polynomial, (2, 0.5)),
                           (de.grouped_terms, (None,))):
            with self.assertRaises(TypeError):
                func(*args)
        for func, args in ((de.falling, (1, -1)), (de.bernoulli_numbers, (-1,)),
                           (de.shifted_stirling_coefficient, (0, 0)),
                           (de.tail_onset_sixth_power, (0,)), (de.normalization, (-1,))):
            with self.assertRaises(ValueError):
                func(*args)

    def test_fixture_types_semantically_exact(self):
        cert.fixture_types()
        def visit(value):
            self.assertNotIsInstance(value, float)
            if is_dataclass(value):
                for field in fields(value):
                    visit(getattr(value, field.name))
            elif isinstance(value, tuple):
                for item in value:
                    visit(item)
        visit(fx.COMMON + fx.DIFFERENCE)

    def test_encoder_rejects_float_and_nonstring_key(self):
        for value in (0.5, {"x": 0.5}, {F(1): 1}, object()):
            with self.assertRaises(TypeError):
                cert.encode_exact(value)
        self.assertEqual(cert.encode_exact(F(2, 4)), {"numerator": 1, "denominator": 2})

    def test_failure_checks_are_live(self):
        with self.assertRaises(cert.CertificateError):
            cert.require(False, "intentional failure")
        with self.assertRaises(cert.CertificateError):
            cert.equal(F(1), F(2), "intentional mismatch")


class CLITests(unittest.TestCase):
    def run_cli(self, *arguments, optimized=False):
        command = [sys.executable] + (["-O"] if optimized else [])
        return subprocess.run(command + [str(ROOT / "certificate.py"), *arguments],
                              cwd=ROOT, text=True, capture_output=True, check=False)

    def test_deterministic_normal_vs_optimized_json(self):
        normal = self.run_cli("--max-n", "11")
        optimized = self.run_cli("--max-n", "11", optimized=True)
        self.assertEqual(normal.returncode, 0, normal.stderr)
        self.assertEqual(optimized.returncode, 0, optimized.stderr)
        self.assertEqual(normal.stdout, optimized.stdout)
        payload = json.loads(normal.stdout)
        self.assertEqual(payload["status"], "PASS")
        self.assertEqual([r["profile_count"] for r in payload["common_sectors"]], [14, 21, 17])
        self.assertEqual([r["profile_count"] for r in payload["first_difference_sectors"]], [3, 2, 1])
        self.assertNotIn(".0", normal.stdout)

    def test_cli_invalid_arguments(self):
        for args in (("--max-n", "10"), ("--max-n", "oops"), ("--unknown",),
                     ("--output", str(ROOT.parent / "forbidden-output.json"))):
            result = self.run_cli(*args)
            self.assertNotEqual(result.returncode, 0)
            self.assertEqual(result.stdout, "")

    def test_cli_file_replay(self):
        with tempfile.TemporaryDirectory(dir=ROOT) as temporary:
            path = Path(temporary) / "certificate.json"
            result = self.run_cli("--max-n", "11", "--output", str(path))
            self.assertEqual(result.returncode, 0, result.stderr)
            self.assertEqual(result.stdout, "")
            self.assertEqual(path.read_text(), cert.dumps_certificate(11))

    def test_cli_refuses_existing_files_unchanged(self):
        with tempfile.TemporaryDirectory(dir=ROOT) as temporary:
            target = Path(temporary) / "existing.json"
            target.write_text("sentinel\n")
            result = self.run_cli("--max-n", "11", "--output", str(target))
            self.assertNotEqual(result.returncode, 0)
            self.assertEqual(target.read_text(), "sentinel\n")
        result = self.run_cli("--output", str(ROOT / "fixtures.py"))
        self.assertNotEqual(result.returncode, 0)

    def test_cli_rejects_parent_traversal_even_inside_package(self):
        with tempfile.TemporaryDirectory(dir=ROOT) as temporary:
            target = Path(temporary) / ".." / "traversal-must-not-exist.json"
            result = self.run_cli("--output", str(target))
            self.assertNotEqual(result.returncode, 0)
            self.assertIn("traversal", result.stderr)
            self.assertFalse((ROOT / "traversal-must-not-exist.json").exists())

    def test_cli_rejects_symlink_components(self):
        with tempfile.TemporaryDirectory(dir=ROOT) as temporary:
            directory = Path(temporary)
            real = directory / "real"
            real.mkdir()
            link = directory / "link"
            link.symlink_to(real, target_is_directory=True)
            for target in (link / "new.json", directory / "dangling.json"):
                if target.name == "dangling.json":
                    target.symlink_to(directory / "missing.json")
                result = self.run_cli("--output", str(target))
                self.assertNotEqual(result.returncode, 0)
                self.assertIn("symlink", result.stderr)
            self.assertFalse((real / "new.json").exists())
            self.assertFalse((directory / "missing.json").exists())

    def test_optimized_explicit_failure_survives(self):
        result = subprocess.run([sys.executable, "-O", "-c",
                                 "import certificate; certificate.require(False, 'sentinel')"],
                                cwd=ROOT, text=True, capture_output=True, check=False)
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("CertificateError: sentinel", result.stderr)


if __name__ == "__main__":
    unittest.main()
