#!/usr/bin/env python3
"""Independent finite checks; not a formal verification of the full solver."""

from fractions import Fraction
import json
from pathlib import Path
import unittest

from contraction_parameters import (
    active_nodes, exact_taper, grid, hermite_multiplier_exact,
    hermite_valuation_by_levels, hermite_valuation_direct,
    leading_constants, p_child, rational_v2, schedule_algebra,
    schedule_from_log, v2,
)


class ParameterValidation(unittest.TestCase):
    counts = {"taper_cases": 0, "active_node_cases": 0,
              "independent_rational_products": 0,
              "recovery_precision_cases": 0}

    def test_tapers_and_valuation_identity(self):
        # Every a=1,...,7 and every allowed u; M sampled across scales.
        for a in range(1, 8):
            for u in range(1, a + 1):
                for M in (1, 2, 3, 7, 16, 64):
                    taper = exact_taper(a, u, M)
                    direct_count = sum(taper.multiplicity(v2(t))
                                       for t in grid(taper) if t != 0)
                    self.assertEqual(direct_count, taper.total_multiplicity)
                    self.assertGreater(direct_count, taper.degree)
                    self.assertLessEqual((taper.h - 1)
                                         * taper.multiplicity_per_unit_h,
                                         taper.degree)
                    self.counts["taper_cases"] += 1
                    for t in active_nodes(taper):
                        direct = hermite_valuation_direct(taper, t)
                        self.assertEqual(direct,
                                         hermite_valuation_by_levels(taper, t))
                        D = taper.L >> v2(t)
                        self.assertGreaterEqual(direct, -6 * taper.h * D)
                        self.counts["active_node_cases"] += 1
                        # The highest retained power incurs the largest loss;
                        # checking it covers every lower power without a loop.
                        j = taper.multiplicity(v2(t)) - 1
                        for p in (1, 3, 17):
                            retained = (p_child(p, taper, t) + direct
                                        + j * (v2(t) - taper.a - 1))
                            self.assertGreaterEqual(retained, p + 1)
                            self.counts["recovery_precision_cases"] += 1

    def test_actual_rational_products(self):
        # Independently build E_t(0) as a Fraction, rather than using a
        # sum of valuations, in smaller instances.
        for a in range(1, 5):
            for u in range(1, a + 1):
                for M in (1, 3, 7):
                    taper = exact_taper(a, u, M)
                    alpha = 2 * taper.L
                    for t in active_nodes(taper):
                        E = hermite_multiplier_exact(taper, t)
                        self.assertEqual(rational_v2(E),
                                         hermite_valuation_by_levels(taper, t))
                        j = taper.multiplicity(v2(t)) - 1
                        # A unit-sized residue error at the prescribed child
                        # precision is still zero modulo 2^p after recovery.
                        p = 5
                        error = ((1 << p_child(p, taper, t))
                                 * E * Fraction(-t, alpha) ** j)
                        self.assertGreaterEqual(rational_v2(error), p + 1)
                        self.counts["independent_rational_products"] += 1

    def test_schedule_exact_exponents(self):
        algebra = schedule_algebra()
        self.assertEqual(algebra["L_exponent_upper_bound"], "1/330")
        self.assertEqual(algebra["D_array_exponent_upper_bound"], "8/165")
        self.assertEqual(algebra["degree_times_D_array_squared_exponent"],
                         "329/330")
        self.assertEqual(algebra["child_edge_ratio"], "3/128")
        for lam in (10**12, 10**15, 10**18):
            result = schedule_from_log(lam)
            self.assertTrue(result["a_bound_holds"])
            self.assertTrue(result["all_u_positive"])
            self.assertTrue(result["packing_inequalities_sufficiently_certified"])

    def test_leading_constant_display(self):
        constants = leading_constants()
        self.assertTrue(648.44 < constants["revised"] < 648.45)
        self.assertTrue(18534.75 < constants["source_schedule_tree"] < 18534.76)
        self.assertGreater(constants["revised_active_u_power"], Fraction(1, 3))

    def test_parameter_validation(self):
        for args in ((0, 1, 2), (2, 0, 2), (2, 3, 2), (2, 1, 0)):
            with self.assertRaises(ValueError):
                exact_taper(*args)
        with self.assertRaises(ValueError):
            v2(0)


if __name__ == "__main__":
    suite = unittest.defaultTestLoader.loadTestsFromTestCase(ParameterValidation)
    result = unittest.TextTestRunner(verbosity=2).run(suite)
    record = {
        "scope": "Finite exact arithmetic checks of the taper, Hermite valuations, recovery precision, and parameter algebra. No SAT or tensor contraction implementation; no formal proof-assistant verification.",
        "all_tests_passed": result.wasSuccessful(),
        "test_methods_run": result.testsRun,
        "failures": len(result.failures),
        "errors": len(result.errors),
        "cases": ParameterValidation.counts,
        "parameters_checked": {"a": "all integers 1 through 7",
                               "u": "all integers 1 through a",
                               "M_samples": [1, 2, 3, 7, 16, 64],
                               "parent_precision_samples": [1, 3, 17],
                               "independent_rational_products": "all a<=4, all u<=a, M in {1,3,7}"},
        "leading_constants": leading_constants(),
        "schedule_algebra": schedule_algebra(),
        "large_logarithm_sanity_checks":
            [schedule_from_log(z) for z in (10**12, 10**15, 10**18)],
    }
    output = Path(__file__).with_name("parameter_validation.json")
    output.write_text(json.dumps(record, indent=2) + "\n", encoding="utf-8")
    print("Validation record:", output)
    raise SystemExit(0 if result.wasSuccessful() else 1)
