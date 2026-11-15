#!/usr/bin/env python3
"""Deterministic arithmetic validation, not a formal proof certificate."""

import itertools
import json
import math
from pathlib import Path
import platform
import sys
import unittest

from pell_reference import (
    cf_certificate, classify_negative, classify_norm_one, congruence_period,
    dirichlet_certificate, fundamental_by_scan, fundamental_unit,
    generalized_seeds, multiply, negative_seed_scan, norm, power,
    quadratic_sign, quotient_certificate, reduce_generalized,
    signature_code, sqrt_floor, sqrt_interval, sqrt_interval_at_precision,
    valid_discriminant,
)


COUNTS = {}


class PellTests(unittest.TestCase):
    def test_sqrt(self):
        values = list(range(10001))
        values += [(1 << k) + offset for k in range(1, 200) for offset in (-1, 0, 1)]
        for n in values:
            r = sqrt_floor(n)
            self.assertEqual(r, math.isqrt(n))
            self.assertTrue(r * r <= n < (r + 1) ** 2)
        COUNTS["integer_square_roots"] = len(values)

    def test_pair_algebra(self):
        count = 0
        for D in (2, 3, 5, 13, 61):
            for x, y, r, s in itertools.product(range(-2, 3), repeat=4):
                z, w = (x, y), (r, s)
                self.assertEqual(norm(D, multiply(D, z, w)), norm(D, z) * norm(D, w))
                self.assertEqual(multiply(D, z, w), multiply(D, w, z))
                count += 1
        COUNTS["quadratic_pair_products"] = count

    def test_known_units(self):
        known = {
            2: (1, (3, 2), (1, 1)),
            3: (2, (2, 1), None),
            7: (4, (8, 3), None),
            12: (2, (7, 2), None),
            13: (5, (649, 180), (18, 5)),
            34: (4, (35, 6), None),
            61: (11, (1766319049, 226153980), (29718, 3805)),
        }
        for D, (ell, unit, negative) in known.items():
            c = cf_certificate(D)
            self.assertEqual((c["period"], c["fundamental"], c["negative"]),
                             (ell, unit, negative))
        COUNTS["known_discriminants"] = len(known)

    def test_cf_finite_invariants(self):
        discriminants, states, convergents = 0, 0, 0
        for D in range(2, 501):
            if not valid_discriminant(D):
                continue
            c = cf_certificate(D)
            discriminants += 1
            states += len(c["states"])
            convergents += len(c["convergents"])
            self.assertLessEqual(c["period"], c["state_bound"])
            self.assertLessEqual(max(c["fundamental"]), c["coordinate_bound"])
            self.assertEqual(norm(D, c["fundamental"]), 1)
            for index, conv in enumerate(c["convergents"]):
                self.assertEqual(abs(conv["norm"]) == 1,
                                 (index + 1) % c["period"] == 0)
        COUNTS.update(cf_discriminants=discriminants,
                      reduced_period_states=states, verified_convergents=convergents)

    def test_bounded_minimality_crosscheck(self):
        cases, denominators = 0, 0
        for D in range(2, 151):
            if not valid_discriminant(D):
                continue
            unit = fundamental_unit(D)
            if unit[1] > 5000:
                continue
            self.assertEqual(fundamental_by_scan(D, unit), unit)
            smaller_solutions = []
            for y in range(1, unit[1] + 1):
                x = math.isqrt(D * y * y + 1)
                if x * x - D * y * y == 1:
                    smaller_solutions.append((x, y))
            self.assertEqual(smaller_solutions, [unit])
            cases += 1
            denominators += unit[1]
        COUNTS["brute_minimality_discriminants"] = cases
        COUNTS["brute_minimality_denominators"] = denominators

    def test_classification(self):
        count = 0
        for D in (2, 3, 5, 7, 12, 13, 34, 61):
            u = fundamental_unit(D)
            for n in range(9):
                z = power(D, u, n)
                self.assertEqual(norm(D, z), 1)
                self.assertEqual(classify_norm_one(D, u, z), n)
                count += 1
            for m in range(5):
                for n in range(5):
                    self.assertEqual(power(D, u, m + n),
                                     multiply(D, power(D, u, m), power(D, u, n)))
        with self.assertRaises(ValueError):
            classify_norm_one(2, (17, 12), (3, 2))
        COUNTS["norm_one_descent_roundtrips"] = count

    def test_negative(self):
        count, scans = 0, 0
        for D in (2, 3, 5, 7, 10, 12, 13, 20, 34, 61):
            c = cf_certificate(D)
            u, v = c["fundamental"], c["negative"]
            self.assertEqual(negative_seed_scan(D, u), v)
            scans += 1
            if v is not None:
                self.assertEqual(multiply(D, v, v), u)
                for n in range(6):
                    z = multiply(D, v, power(D, u, n))
                    self.assertEqual(classify_negative(D, u, v, z), n)
                    count += 1
        self.assertIsNone(cf_certificate(20)["negative"])
        COUNTS["negative_scan_crosschecks"] = scans
        COUNTS["negative_descent_roundtrips"] = count

    def test_generalized(self):
        families, seed_count, reductions, brute_solutions = 0, 0, 0, 0
        for D in (2, 3, 5, 6, 7, 12, 13):
            u = fundamental_unit(D)
            for N in range(-12, 13):
                seeds = generalized_seeds(D, N, u)
                seed_set = set(seeds)
                families += 1
                seed_count += len(seeds)
                for seed in seeds:
                    self.assertEqual(norm(D, seed), N)
                    for n in range(4):
                        z = multiply(D, seed, power(D, u, n))
                        returned, exponent = reduce_generalized(D, N, u, z)
                        self.assertIn(returned, seed_set)
                        self.assertEqual(multiply(D, returned, power(D, u, exponent)), z)
                        reductions += 1
                for y in range(101):
                    t = D * y * y + N
                    if t < 0:
                        continue
                    x = math.isqrt(t)
                    if x * x == t:
                        returned, exponent = reduce_generalized(D, N, u, (x, y))
                        self.assertIn(returned, seed_set)
                        self.assertEqual(multiply(D, returned, power(D, u, exponent)), (x, y))
                        brute_solutions += 1
        COUNTS.update(generalized_norm_families=families,
                      generalized_seeds=seed_count,
                      generalized_descent_roundtrips=reductions,
                      independently_enumerated_generalized_solutions=brute_solutions)

    def test_congruence_and_divisibility(self):
        periods, gcd_checks = 0, 0
        for D in (2, 3, 5, 7, 13, 61):
            u = fundamental_unit(D)
            for modulus in range(1, 31):
                t = congruence_period(D, u, modulus)
                self.assertTrue(1 <= t <= modulus * modulus)
                z = power(D, u, t)
                self.assertEqual((z[0] % modulus, z[1] % modulus), (1 % modulus, 0))
                periods += 1
            sequence = [power(D, u, n)[1] for n in range(13)]
            for m in range(13):
                for n in range(13):
                    self.assertEqual(math.gcd(sequence[m], sequence[n]),
                                     sequence[math.gcd(m, n)])
                    if m > 0:
                        self.assertEqual(sequence[n] % sequence[m] == 0, n % m == 0)
                    gcd_checks += 1
        COUNTS["bounded_modular_periods"] = periods
        COUNTS["strong_divisibility_pairs"] = gcd_checks

    def test_intervals(self):
        count = 0
        for D in (2, 3, 5, 7, 12, 13, 61):
            u = fundamental_unit(D)
            for k in range(11):
                low, high = sqrt_interval_at_precision(D, u, k)
                next_low, next_high = sqrt_interval(D, u, k + 2)
                self.assertTrue(low < next_low < next_high < high)
                count += 1
        COUNTS["rational_enclosures"] = count

    def test_dirichlet_and_quotient(self):
        count = 0
        for D in range(2, 31):
            if not valid_discriminant(D):
                continue
            for Q in range(1, 31):
                c = dirichlet_certificate(D, Q)
                p, q = c["p"], c["q"]
                # This independent check squares both positive endpoints of
                # the interval p/q +/- 1/(Qq), avoiding the sign routine.
                self.assertLess((Q * p - 1) ** 2, D * (Q * q) ** 2)
                self.assertLess(D * (Q * q) ** 2, (Q * p + 1) ** 2)
                self.assertLess(signature_code(D, p, q), 2 * (2 * D + 1) ** 3)
                count += 1
        first, second = dirichlet_certificate(2, 1), dirichlet_certificate(2, 5)
        quotient = quotient_certificate(2, (first["p"], first["q"]),
                                       (second["p"], second["q"]))
        self.assertEqual(quotient["positive_unit"], (3, 2))
        for D in (2, 3, 5, 13):
            u = fundamental_unit(D)
            # Powers of a unit provide distinct equal norm-one signatures.
            cert = quotient_certificate(D, u, power(D, u, 3))
            self.assertEqual(cert["positive_unit"], power(D, u, 2))
        self.assertEqual(quadratic_sign(2, 1, -1), -1)
        self.assertEqual(quadratic_sign(2, -1, 1), 1)
        COUNTS["finite_dirichlet_certificates"] = count
        COUNTS["integral_signature_quotients"] = 5

    def test_invalid_inputs(self):
        for D in (0, 1, 4, 9, 16):
            with self.assertRaises(ValueError):
                cf_certificate(D)
            with self.assertRaises(ValueError):
                reduce_generalized(D, 0, (1, 0), (0, 0))
        with self.assertRaises(ValueError):
            reduce_generalized(2, 0, (1, 0), (0, 0))
        with self.assertRaises(ValueError):
            quotient_certificate(2, (1, 1), (3, 2))
        with self.assertRaises(ValueError):
            congruence_period(2, (3, 2), 0)


if __name__ == "__main__":
    suite = unittest.defaultTestLoader.loadTestsFromTestCase(PellTests)
    result = unittest.TextTestRunner(verbosity=2).run(suite)
    report = {
        "status": "passed" if result.wasSuccessful() else "failed",
        "python_version": platform.python_version(),
        "test_methods": result.testsRun,
        "failures": len(result.failures),
        "errors": len(result.errors),
        "counts": COUNTS,
        "scope": "Deterministic finite arithmetic checks; not formal proof certificates.",
    }
    Path(__file__).with_name("test-results.json").write_text(
        json.dumps(report, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(json.dumps(report, indent=2, sort_keys=True))
    sys.exit(0 if result.wasSuccessful() else 1)
