#!/usr/bin/env python3
"""Standalone regression checks for exact-natural evaluator inputs.

Run from the release root: python3 code/test_application_domain.py
Optional baseline comparison: --kernel /path/to/original/tree_kernel.py
Only the delivered kernel and this local regression code are executed.
"""
import argparse
import copy
import importlib.util
from pathlib import Path
import sys
import unittest

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--kernel', type=Path, default=Path(__file__).with_name('tree_kernel.py'))
args, unittest_args = parser.parse_known_args()
spec = importlib.util.spec_from_file_location('tree_kernel_domain_test', args.kernel)
k = importlib.util.module_from_spec(spec)
sys.modules[spec.name] = k
spec.loader.exec_module(k)


class IntSubclass(int):
    pass


BAD_CODES = (-1, -2, True, False, 1.0, 0.0, 1.5, None, '1', [], {}, IntSubclass(1), 1+0j)


def snapshot(ev):
    return copy.deepcopy((ev.records, ev.active, ev.budget, ev.max_bits))


class ApplicationDomainTests(unittest.TestCase):
    def test_invalid_inputs_before_cache_and_state_mutation(self):
        # 13 malformed values x 2 argument slots x cold/warm = 52 cases.
        for warm in (False, True):
            for slot in (0, 1):
                for bad in BAD_CODES:
                    with self.subTest(warm=warm, slot=slot, value=repr(bad), type=type(bad).__name__):
                        ev = k.Evaluation()
                        if warm:
                            for x in (0, 1):
                                for y in (0, 1):
                                    ev.app(x, y)
                        before = snapshot(ev)
                        values = [1, 1]
                        values[slot] = bad
                        with self.assertRaises(ValueError):
                            ev.app(*values)
                        self.assertEqual(snapshot(ev), before)
                        # Rejection must not spoil subsequent valid reuse.
                        self.assertEqual(ev.app(0, 1), 3)
                        rows = k.certificate(ev, (0, 1))
                        self.assertTrue(k.valid_domain(rows, 0, 1, 3))
                        self.assertEqual(k.polynomial(rows, 0, 1, 3)['value'], 0)

    def test_validation_precedes_budget_and_active_checks(self):
        # A domain error takes priority over exhausted fuel or a colliding active key.
        for mode in ('exhausted', 'active'):
            for slot in (0, 1):
                for bad in (-1, True, 1.0):
                    with self.subTest(mode=mode, slot=slot, value=repr(bad)):
                        ev = k.Evaluation(budget=0 if mode == 'exhausted' else 100)
                        if mode == 'active':
                            ev.active.add((1, 1))
                        before = snapshot(ev)
                        values = [1, 1]
                        values[slot] = bad
                        with self.assertRaises(ValueError):
                            ev.app(*values)
                        self.assertEqual(snapshot(ev), before)

    def test_boolean_cannot_poison_valid_certificate(self):
        for bad in (True, False):
            ev = k.Evaluation()
            with self.assertRaises(ValueError):
                ev.app(0, bad)
            y = int(bad)
            z = ev.app(0, y)
            self.assertIs(type(ev.records[(0, y)]['y']), int)
            self.assertEqual(k.polynomial(k.certificate(ev, (0, y)), 0, y, z)['value'], 0)

    def test_valid_natural_results_certificates_and_cache_reuse(self):
        tags = set()
        for x in range(20):
            for y in range(9):
                with self.subTest(x=x, y=y):
                    ev = k.Evaluation()
                    z = ev.app(x, y)
                    rows = k.certificate(ev, (x, y))
                    self.assertEqual(k.polynomial(rows, x, y, z)['value'], 0)
                    tree, height = k.structural_app(k.decode(x), k.decode(y), [10000])
                    self.assertEqual(k.encode(tree), z)
                    self.assertEqual(height, ev.records[(x, y)]['h'])
                    tags.update(record['tag'] for record in ev.records.values())
                    before = snapshot(ev)
                    self.assertEqual(ev.app(x, y), z)
                    self.assertEqual(snapshot(ev), before)
        self.assertEqual(tags, set(range(5)))

    def test_existing_polynomial_domain_remains_strict(self):
        ev = k.Evaluation()
        self.assertEqual(ev.app(10, 10), 10)
        original = k.certificate(ev, (10, 10))
        for field in k.SCALARS + ['t', 'pointers', 'public_p', 'public_n', 'public_o']:
            for bad in (-1, True, 1.0):
                with self.subTest(field=field, value=repr(bad)):
                    rows = copy.deepcopy(original)
                    public = [10, 10, 10]
                    if field in k.SCALARS:
                        rows[0][field] = bad
                    elif field == 't':
                        rows[0]['t'][0] = bad
                    elif field == 'pointers':
                        rows[0]['pointers'][0][0] = bad
                    else:
                        public[['public_p', 'public_n', 'public_o'].index(field)] = bad
                    self.assertFalse(k.valid_domain(rows, *public))
                    with self.assertRaises(ValueError):
                        k.polynomial(rows, *public)


if __name__ == '__main__':
    unittest.main(argv=[sys.argv[0]] + unittest_args)
