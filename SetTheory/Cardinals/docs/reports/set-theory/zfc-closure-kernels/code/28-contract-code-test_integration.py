#!/usr/bin/env python3
"""Cross-check separately implemented logical and binary-stream interfaces."""
from pathlib import Path
import json
import unittest

import contraction_kernel as k
import fixed_theory_search as fixed
import stream_renaming as stream
from check_stream_renaming import run_table

ROOT = Path(__file__).resolve().parents[1]
MODE = {'up': 's', 'down': 'S', 'swap': 't', 'contract': 'k'}


class IntegrationTests(unittest.TestCase):
    def test_exact_collision_certificate_through_exported_tables(self):
        certificate = json.loads((ROOT / 'results/colliding_ui_certificate.json').read_text())
        tables = json.loads((ROOT / 'results/stream_transducers.json').read_text())
        lines = k.check_certificate(certificate)
        self.assertEqual(len(lines), 10)
        self.assertEqual(sum(i['op'] == 'contract' for i in certificate['instructions']), 1)
        for index, instruction in enumerate(certificate['instructions']):
            if instruction['op'] in MODE:
                before = stream.encode(lines[instruction['line']])
                actual, _ = run_table(tables[MODE[instruction['op']]], before)
                self.assertEqual(actual, stream.encode(lines[index]))
                self.assertEqual(stream.decode(actual), lines[index])

    def test_closed_fixed_axioms_unchanged_by_each_renamer(self):
        matrix = k.Imp(k.R(k.F(0), k.F(-8)),
                       k.All(k.Imp(k.R(k.B(0), k.F(1)), k.R(k.F(21), k.B(0)))))
        axioms = [fixed.CP, fixed.gic_axiom(matrix), fixed.gic_axiom(k.All(k.source19_body())),
                  fixed.epsc2_axiom(k.R(k.F(0), k.F(1)))]
        for axiom in axioms:
            self.assertTrue(k.scoped(axiom))
            self.assertFalse(k.free_names(axiom))
            bits = stream.encode(axiom)
            self.assertEqual(stream.decode(bits), axiom)
            for op, mode in MODE.items():
                self.assertEqual(k.rename_step(op, axiom), axiom)
                self.assertEqual(stream.transduce(mode, bits), bits)

    def test_independent_factorizations_and_total_support(self):
        cases = [{-3: 5, 5: 5}, {-2: 3, 0: 3, 3: 7, 7: 7},
                 {-5: -5}, {0: 1, 1: 0}, {-3: 0, 0: -3, 8: 0}]
        for mapping in cases:
            left = k.factor_on_support(mapping)
            right = stream.factor_names(mapping)
            for name, target in mapping.items():
                self.assertEqual(k.run_name_word(left, name), target)
                actual = name
                for mode in right:
                    actual = stream.scalar(mode, actual)
                self.assertEqual(actual, target)
            expected = len(mapping) - len(set(mapping.values()))
            self.assertEqual(left.count('contract'), expected)
            self.assertEqual(right.count('k'), expected)
            if set(mapping.values()) <= set(mapping):
                for name in set(range(-12, 13)) - set(mapping):
                    self.assertEqual(k.run_name_word(left, name), name)
                    actual = name
                    for mode in right:
                        actual = stream.scalar(mode, actual)
                    self.assertEqual(actual, name)

    def test_no_python_decimal_digit_cap_in_candidate_reader(self):
        # The mathematical proof-name space cannot depend on a host digit cap.
        # This does not start the infinite search or claim a refutation exists.
        digits = '1' + '0' * 5000
        value = fixed.decode_candidate(digits.encode('ascii'))
        self.assertEqual(value, 10 ** 5000)
        self.assertFalse(fixed.accepts_bytes(digits.encode('ascii')))


if __name__ == '__main__':
    unittest.main(verbosity=2)
