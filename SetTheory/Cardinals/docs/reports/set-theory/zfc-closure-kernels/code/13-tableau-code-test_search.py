#!/usr/bin/env python3
"""Enumeration coverage and refutation-only acceptance regressions."""
import json
from pathlib import Path
import unittest

import refutation_search as s
from test_tableau import ui_certificate


class SearchTests(unittest.TestCase):
    def test_codec_inverses(self):
        for n in range(1000):
            self.assertEqual(s.encode_matrix(s.decode_matrix(n)), n)
            self.assertEqual(s.encode_proof(s.decode_proof(n)), n)
            self.assertEqual(s.encode_list(s.decode_list(n)), n)
            self.assertEqual(s.encode_certificate(s.decode_certificate(n)), n)

    def test_theorem_mode_cannot_enter_refutation_search(self):
        ui = ui_certificate()
        with self.assertRaises(ValueError):
            s.encode_certificate(ui)
        del ui['theorem']
        n = s.encode_certificate(ui)
        self.assertEqual(s.decode_certificate(n), ui)
        self.assertFalse(s.accepts(n))

    def test_diagnostic_prefix(self):
        self.assertFalse(any(s.accepts(n) for n in range(500)))
        for bad in (-1, True, 1.0):
            with self.assertRaises(ValueError):
                s.accepts(bad)


if __name__ == '__main__':
    result = unittest.TextTestRunner(verbosity=2).run(
        unittest.defaultTestLoader.loadTestsFromTestCase(SearchTests))
    evidence = {'tests_run': result.testsRun, 'passed': result.wasSuccessful(),
                'failures': len(result.failures), 'errors': len(result.errors),
                'codec_cases_per_type': 1000, 'diagnostic_prefix': 500,
                'scope': 'Finite encoding and target-guard checks; no consistency or compiled-TM result'}
    (Path(__file__).resolve().parents[1]/'results/search_tests.json').write_text(
        json.dumps(evidence, indent=2)+'\n')
    raise SystemExit(0 if result.wasSuccessful() else 1)
