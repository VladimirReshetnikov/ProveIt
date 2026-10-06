#!/usr/bin/env python3
"""Exact and finite-diagnostic checks for Report151.

Uses unittest checks and explicit exceptions, never Python assert statements:
python -O executes the same checks.  Finite samples do not prove uniform
analytic bounds.  Build tests use a mock PDF; real TeX reproducibility is a
separate two-build comparison documented in README.txt.
"""
from __future__ import annotations

from fractions import Fraction as F
import hashlib
import io
from math import comb, factorial
import os
from pathlib import Path
import tempfile
import unittest
from unittest import mock
import zipfile

import build
import companion as c


def involutions(n):
    permutation = [-1] * n

    def visit():
        i = next((i for i, value in enumerate(permutation) if value < 0), n)
        if i == n:
            yield tuple(permutation)
            return
        permutation[i] = i
        yield from visit()
        permutation[i] = -1
        for j in range(i + 1, n):
            if permutation[j] < 0:
                permutation[i], permutation[j] = j, i
                yield from visit()
                permutation[i] = permutation[j] = -1

    yield from visit()


def is_baxter(p):
    # The forbidden patterns 2-41-3 and 3-14-2 have their middle positions adjacent.
    for j in range(1, len(p) - 2):
        for i in range(j):
            for k in range(j + 2, len(p)):
                if p[j + 1] < p[i] < p[k] < p[j] or p[j] < p[k] < p[i] < p[j + 1]:
                    return False
    return True


def is_alternating(p, ascent):
    return all((p[i] < p[i + 1]) == (ascent if i % 2 == 0 else not ascent)
               for i in range(len(p) - 1))


def multiply_bivariate(a, b, max_t):
    out = {}
    for (i, j), u in a.items():
        for (k, ell), v in b.items():
            if i + k <= max_t:
                key = (i + k, j + ell)
                out[key] = out.get(key, F(0)) + u * v
    return {key: value for key, value in out.items() if value}


class ExactChecks(unittest.TestCase):
    def test_recurrence_and_independent_closed_coefficients(self):
        e, r = c.recurrence_polynomials(32)
        for m in range(33):
            for s, row in (("E", e[m]), ("R", r[m])):
                self.assertEqual(row, c.closed_polynomial(s, m), (s, m))
                self.assertEqual(c.closed_coefficient(s, m, m + 2), 0)
                self.assertTrue(all(isinstance(x, int) and x >= 0 for x in row))
        self.assertEqual(e[6], (5, 10, 19, 10))
        self.assertEqual(r[6], (10, 35, 34, 5))
        # Corrected first-discrepancy fixtures, beyond the small brute-force run.
        self.assertEqual((sum(e[10]), sum(e[11])), (2168, 6014))
        self.assertEqual((sum(r[10]), sum(r[11])), (5080, 14594))

    def test_small_involutions_by_direct_enumeration(self):
        e, r = c.recurrence_polynomials(4)
        for n in range(1, 10):
            for s, ascent in (("E", True), ("R", False)):
                if n % 2 and s == "R":
                    continue
                actual = {}
                for p in involutions(n):
                    if is_alternating(p, ascent) and is_baxter(p):
                        fixed = sum(i == value for i, value in enumerate(p))
                        k = (fixed - n % 2) // 2
                        actual[k] = actual.get(k, 0) + 1
                expected = r[n // 2] if n % 2 or s == "R" else e[n // 2]
                self.assertEqual(tuple(actual.get(k, 0) for k in range(len(expected))), expected, (s, n))
                self.assertEqual(sum(actual.values()), sum(expected))

    def test_degree_positive_linear_and_exceptions(self):
        for m in range(1, 33):
            e = c.closed_polynomial("E", m)
            self.assertEqual(len(e) - 1, (m + 1) // 2)
            self.assertGreater(e[1], 0)
            self.assertEqual(e[1], 2**(m - 1) * c.h_coefficient(m))
            if m >= 2:
                r = c.closed_polynomial("R", m)
                self.assertEqual(len(r) - 1, m // 2)
                self.assertGreater(r[1], 0)
        self.assertEqual(c.closed_polynomial("R", 0), (1,))
        self.assertEqual(c.closed_polynomial("R", 1), (1,))

    def test_parity_identity_and_finite_support(self):
        for r in range(13):
            for n in range(-1, 36):
                self.assertEqual(c.h_convolution_coefficient(r, n), c.h_parity_coefficient(r, n), (r, n))
        self.assertEqual(c.h_parity_coefficient(10, 0), 1)

    def test_rational_falling_product(self):
        for m in range(2, 60):
            for r in range(1, m // 2 + 1):
                product = 1
                for h in range(r + 1, 2 * r):
                    product *= m - h
                self.assertEqual(F(product, factorial(r - 1)), comb(m - r - 1, r - 1))
                coefficients = [c.b_operator_value(ell, r) for ell in range(r)]
                self.assertEqual(sum(F(v, m**ell) for ell, v in enumerate(coefficients)),
                                 F(product, m**(r - 1)))

    def test_exact_global_majorants(self):
        for n in range(160):
            b = F(comb(2 * n, n), 4**n)
            self.assertLessEqual(c.h_coefficient(n), 2 * b)
            self.assertLessEqual(b * b * (n + 1), 1)
        for m in range(1, 40):
            for r in range(m // 2 + 1):
                n = m - 2 * r
                rising = F(1)
                for i in range(r):
                    rising *= F(1, 2) + i
                coefficient = c.h_convolution_coefficient(r, n)
                # Square the nonnegative inequality H-coefficient <=
                # 2 m^r / ((1/2)_r sqrt(n+1)); no floating square roots.
                self.assertLessEqual(coefficient**2 * rising**2 * (n + 1), 4 * m**(2 * r))

    def test_bernoulli_and_gamma_coefficients(self):
        self.assertEqual([c.bernoulli_number(n) for n in range(7)],
                         [F(1), F(-1, 2), F(1, 6), F(0), F(-1, 30), F(0), F(1, 42)])
        for a in (F(-3, 2), F(0), F(2, 3), F(7)):
            self.assertEqual(c.gamma_ratio_coefficients(7, a, a + 1), tuple((-a)**n for n in range(8)))
            self.assertEqual(c.gamma_ratio_coefficients(7, a, a), (F(1),) + (F(0),) * 7)

    def test_printed_integer_profile_tables(self):
        expected_p = [
            (F(1),), (F(0), F(3, 4), F(-3, 2)),
            (F(1, 32), F(-11, 96), F(31, 32), F(-55, 24), F(9, 8)),
            (F(0), F(15, 128), F(-61, 128), F(217, 128), F(-229, 64), F(83, 32), F(-9, 16)),
        ]
        expected_q = [(F(0),), (F(-1, 4),), (F(0), F(-1, 32)),
                      (F(5, 128), F(-9, 128), F(-1, 128))]
        for ell in range(4):
            self.assertEqual(c.p_polynomial(ell), expected_p[ell])
            self.assertEqual(c.q_polynomial(ell), expected_q[ell])
        for ell in range(5):
            for r in range(2 * ell + 1, 2 * ell + 6):
                self.assertEqual(c.polynomial_value(c.p_polynomial(ell), r), c.p_value(ell, r))
                self.assertEqual(c.alternating_p_value(ell, r), 0)

    def test_printed_half_power_and_catalan_tables(self):
        formulas = [lambda r: F(1), lambda r: F(-3 * r * (r - 1), 2),
                    lambda r: F(r * (r - 2) * (r - 1) * (27 * r - 1), 24),
                    lambda r: F(-r**2 * (r - 3) * (r - 2) * (r - 1) * (9 * r - 1), 16),
                    lambda r: F(r * (r - 4) * (r - 3) * (r - 2) * (r - 1)
                                * (1215 * r**3 - 270 * r**2 + 5 * r + 2), 5760)]
        for ell, formula in enumerate(formulas):
            for r in range(1, 18):
                self.assertEqual(c.b_operator_value(ell, r), formula(r))
                self.assertEqual(c.polynomial_value(c.b_operator_polynomial(ell), r), formula(r))
        self.assertEqual([c.catalan_profile_coefficient(ell) for ell in range(5)],
                         [F(1), F(-9, 4), F(145, 32), F(-1155, 128), F(36939, 2048)])

    def test_exact_finite_thresholds(self):
        for s in ("E", "R"):
            for m in range(2, 32):
                theta = c.exact_threshold(s, m)
                self.assertEqual(theta.radicand, m)
                self.assertEqual(theta.compare_factor(theta.factor), 0)
                self.assertEqual(theta.compare_factor(theta.factor + 1), 1)
                self.assertEqual(theta.compare_factor(theta.factor - 1), -1)
                expected = (F(m * c.catalan(m // 2), 2**m) if m % 2 == 0 else F(0)) if s == "E" else c.h_coefficient(m) / 2
                self.assertEqual(theta.factor, expected)

    def test_boundary_coefficients_exactly(self):
        # Ring Q[t,S], with t=m^(-1/2) and S=sqrt(2pi) left formal.
        # R's pi/16 is S^2/32. Vanishing is coefficient-exact, not a
        # numerical cancellation. These checks do not prove the remainder.
        cases = [("E", 5, {(2, 0): F(9), (4, 0): F(-451, 8), (5, 1): F(81, 8)}),
                 ("R", 4, {(2, 0): F(1, 2), (3, 1): F(-1, 8),
                            (4, 2): F(1, 32), (4, 0): F(11, 48)})]
        for s, degree, w in cases:
            residual = {}
            for kind in ("A", "B"):
                for ell in range(degree // 2 + 1):
                    offset = 2 * ell + (kind == "B")
                    power = {(0, 0): F(1)}
                    for k in range(degree // 2 + 1):
                        coefficient = c.exact_profile_coefficient(kind, s, ell, 1, k)
                        for (i, j), v in power.items():
                            key = (i + offset, j + (kind == "B"))
                            if key[0] <= degree:
                                residual[key] = residual.get(key, F(0)) + coefficient * v
                        power = multiply_bivariate(power, w, degree)
            residual[(0, 0)] -= 4 if s == "E" else 1
            self.assertEqual({key: value for key, value in residual.items() if value}, {}, s)

    def test_invalid_exact_inputs_raise_even_under_optimization(self):
        for function, args in [(c.catalan, (-1,)), (c.recurrence_polynomials, (True,)),
                               (c.closed_coefficient, ("X", 3, 1)), (c.p_polynomial, (-1,)),
                               (c.exact_threshold, ("R", 1)), (c.exact_threshold, ("E", 0))]:
            with self.assertRaises(ValueError):
                function(*args)


class NumericalDiagnostics(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        import mpmath as mp
        cls.mp = mp
        cls.old_dps = mp.mp.dps
        mp.mp.dps = 60

    @classmethod
    def tearDownClass(cls):
        cls.mp.mp.dps = cls.old_dps

    def close(self, a, b, tolerance="1e-52"):
        self.assertLess(abs(a - b), self.mp.mpf(tolerance))

    def test_displayed_profiles_and_derivatives(self):
        mp = self.mp
        for w in (mp.mpf(0), mp.mpf("0.5"), mp.mpc(1, "0.75")):
            f = mp.expm1(w) / w if w else mp.mpf(1)
            B = w / 8 * mp.hyp1f1(mp.mpf("1.5"), 3, w)
            for epsilon in (-1, 1):
                self.close(c.profile("A", "R", 0, epsilon, w), f / mp.sqrt(2 * mp.pi))
                self.close(c.profile("A", "E", 0, epsilon, w), (mp.exp(w) + 1 + 2 * epsilon) / mp.sqrt(2 * mp.pi))
                self.close(c.profile("B", "R", 0, epsilon, w), B)
                self.close(c.profile("B", "E", 0, epsilon, w), -w * B)
                ar1 = ((9 - 6 * w) * mp.exp(w) - 9 * f - epsilon) / (4 * mp.sqrt(2 * mp.pi))
                self.close(c.profile("A", "R", 1, epsilon, w), ar1)
                self.close(c.profile("A", "E", 1, epsilon, w),
                           w * ar1 - 9 * (1 + epsilon) / (2 * mp.sqrt(2 * mp.pi)))
                self.close(c.profile("B", "R", 1, epsilon, w),
                           -mp.mpf("1.5") * w**2 * c.profile("B", "R", 0, epsilon, w, 2))
        self.close(c.profile("A", "R", 0, 1, 0, 1), 1 / (2 * mp.sqrt(2 * mp.pi)))

    def test_model_inverse_branches(self):
        mp = self.mp
        for s in ("E", "R"):
            for epsilon in (-1, 1):
                for w0 in (mp.mpf("0.2"), mp.mpf(2)):
                    target = c.profile("A", s, 0, epsilon, w0)
                    self.close(c.model_root(s, epsilon, target), w0)
                    if s == "R":
                        h = mp.sqrt(2 * mp.pi) * target
                        self.close(-mp.lambertw(-mp.exp(-1 / h) / h, 0) - 1 / h, 0)

    def test_general_inverse_reversion_matches_first_two_terms(self):
        mp = self.mp
        w = mp.mpf("0.75")
        for s in ("E", "R"):
            for epsilon in (-1, 1):
                u = c.inverse_series(s, epsilon, w, 4)
                g1 = c.profile("A", s, 0, epsilon, w, 1)
                first = -c.profile("B", s, 0, epsilon, w) / g1
                second = -(c.profile("A", s, 1, epsilon, w)
                           + c.profile("B", s, 0, epsilon, w, 1) * first
                           + c.profile("A", s, 0, epsilon, w, 2) * first**2 / 2) / g1
                self.close(u[0], first)
                self.close(u[1], second)
                self.assertEqual(len(u), 4)

    def test_finite_endpoint_distinctions_and_odd_obstruction(self):
        mp = self.mp
        limit_r = 1 / mp.sqrt(2 * mp.pi)
        for m in (20, 21, 40, 41, 80, 81):
            finite = c.normalized_value("R", m, 0)
            self.assertEqual(c.numerical_exact_root("R", m, finite), 0)
            with self.assertRaises(ValueError):
                c.numerical_exact_root("R", m, finite / 2)
            if m % 2:
                self.assertGreater(finite, limit_r)
                with self.assertRaises(ValueError):
                    c.numerical_exact_root("R", m, limit_r)
                self.assertEqual(c.numerical_exact_root("E", m, 0), 0)
            else:
                self.assertLess(finite, limit_r)
                self.assertGreater(c.numerical_exact_root("R", m, limit_r), 0)
                self.assertLess(c.normalized_value("E", m, 0), 4 * limit_r)

    def test_complex_residual_and_inverse_samples(self):
        mp = self.mp
        for m in (40, 41, 80, 81):
            for s in ("E", "R"):
                for w in (mp.mpf("0.5"), mp.mpc(1, "0.75")):
                    residual = c.normalized_value(s, m, w) - c.asymptotic_value(s, m, w, 1)
                    self.assertLess(abs(m * m * residual), 50, (s, m, w))
                w0 = mp.mpf("0.75")
                target = c.profile("A", s, 0, (-1)**m, w0)
                u1, u2 = c.inverse_series(s, (-1)**m, w0, 2)
                approximation = w0 + u1 / mp.sqrt(m) + u2 / m
                root = c.numerical_exact_root(s, m, target)
                self.close(c.normalized_value(s, m, root), target, "1e-50")
                self.assertLess(abs(m * mp.sqrt(m) * (approximation - root)), 50)

    def test_boundary_residual_samples(self):
        mp = self.mp
        for m in (40, 80, 160):
            for s in ("E", "R"):
                target = (4 if s == "E" else 1) / mp.sqrt(2 * mp.pi)
                approximation = c.boundary_root_approximation(s, m)
                root = c.numerical_exact_root(s, m, target)
                scale = m**3 if s == "E" else m**2 * mp.sqrt(m)
                self.assertLess(abs(scale * (approximation - root)), 600)
                self.assertLess(abs(scale * (c.normalized_value(s, m, approximation) - target)), 300)

    def test_nonfinite_and_boundary_input_rejections(self):
        mp = self.mp
        for bad in (mp.inf, -mp.inf, mp.nan):
            for function, args in [(c.model_root, ("R", 1, bad)),
                                   (c.numerical_exact_root, ("E", 20, bad)),
                                   (c.inverse_series, ("R", 1, bad, 2)),
                                   (c.profile, ("A", "R", 0, 1, bad)),
                                   (c.normalized_value, ("R", 20, bad))]:
                with self.assertRaises(ValueError):
                    function(*args)
        for m in (0, 3):
            with self.assertRaises(ValueError):
                c.boundary_root_approximation("R", m)
        with self.assertRaises(ValueError):
            c.inverse_series("R", 1, 0)


class BuildSafetyChecks(unittest.TestCase):
    def test_source_foundation_and_allowlist(self):
        source = Path(__file__).absolute().parent
        snapshot = build.source_snapshot(source)
        self.assertEqual(set(snapshot), set(build.SOURCE_FILES))
        for name, expected in build.FOUNDATION_HASHES.items():
            self.assertEqual(hashlib.sha256(snapshot[name]).hexdigest(), expected)

    def test_source_symlinks_and_nonregular_files_rejected(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            (root / "regular").write_bytes(b"keep")
            (root / "link").symlink_to(root / "regular")
            (root / "directory").mkdir()
            os.mkfifo(root / "pipe")
            with build.secure_directory(root) as fd:
                self.assertEqual(build.read_regular(fd, "regular"), b"keep")
                for name in ("link", "directory", "pipe"):
                    with self.assertRaises((OSError, ValueError)):
                        build.read_regular(fd, name)
            (root / "linked-directory").symlink_to(root / "directory", target_is_directory=True)
            with self.assertRaises(OSError):
                with build.secure_directory(root / "linked-directory"):
                    self.fail("a symlink directory was accepted")

    def test_exclusive_atomic_file_publication(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            with build.secure_directory(root) as fd:
                build.publish_exclusive(fd, "result", b"original")
                with self.assertRaises(FileExistsError):
                    build.publish_exclusive(fd, "result", b"overwritten")
                (root / "link").symlink_to(root / "result")
                with self.assertRaises(FileExistsError):
                    build.publish_exclusive(fd, "link", b"overwritten")
            self.assertEqual((root / "result").read_bytes(), b"original")
            self.assertEqual(sorted(p.name for p in root.iterdir()), ["link", "result"])

    def test_existing_and_symlink_output_directory_rejected(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            (root / "existing").mkdir()
            (root / "dangling").symlink_to(root / "nonexistent")
            for name in ("existing", "dangling"):
                with self.assertRaises(FileExistsError):
                    build.build("irrelevant because output must be refused first", root / name)
            (root / "ancestor").symlink_to(root / "existing", target_is_directory=True)
            with self.assertRaises(OSError):
                build.build("irrelevant", root / "ancestor" / "output")

    def test_path_traversal_rejected(self):
        for bad in ("../escape", "a/../escape"):
            with self.assertRaises(ValueError):
                build._absolute_parts(bad)
        for bad in ("/absolute", "../escape", "a//b", "./relative"):
            with self.assertRaises(ValueError):
                build._relative_parts(bad)

    def test_zip_determinism_and_metadata(self):
        a = build.deterministic_zip({"z.txt": b"z", "a.txt": b"a"})
        b = build.deterministic_zip({"a.txt": b"a", "z.txt": b"z"})
        self.assertEqual(a, b)
        with zipfile.ZipFile(io.BytesIO(a)) as archive:
            self.assertEqual(archive.namelist(), ["a.txt", "z.txt"])
            for info in archive.infolist():
                self.assertEqual(info.compress_type, zipfile.ZIP_STORED)
                self.assertEqual(info.external_attr >> 16, 0o100644)
                self.assertEqual(info.create_system, 3)

    def test_complete_mock_build_and_no_overwrite(self):
        source = Path(__file__).absolute().parent
        with tempfile.TemporaryDirectory() as temporary:
            destination = Path(temporary) / "new"
            with mock.patch.object(build, "compile_pdf", return_value=b"%PDF-1.4\nmock\n"):
                digests = build.build(source, destination)
            self.assertEqual(set(digests), {"Report151.pdf", "Report151-source.zip"})
            with zipfile.ZipFile(destination / "Report151-source.zip") as archive:
                self.assertEqual(archive.namelist(), sorted((*build.SOURCE_FILES, "Report151.pdf")))
                self.assertEqual(archive.read("Report151.pdf"), (destination / "Report151.pdf").read_bytes())
            before = {p.name: p.read_bytes() for p in destination.iterdir()}
            with self.assertRaises(FileExistsError):
                build.build(source, destination)
            self.assertEqual(before, {p.name: p.read_bytes() for p in destination.iterdir()})


if __name__ == "__main__":
    unittest.main(verbosity=2)
