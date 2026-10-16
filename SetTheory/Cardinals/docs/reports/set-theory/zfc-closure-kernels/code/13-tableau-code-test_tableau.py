#!/usr/bin/env python3
"""Semantic and adversarial regressions for the environment tableau reference."""
from __future__ import annotations

import itertools
import json
from pathlib import Path
import unittest

import environment_tableau as t
import qpsc_syntax as ns

ROOT = Path(__file__).resolve().parents[1]


def value(formula, members, env=()):
    op = formula[0]
    if op == 'bot':
        return False
    if op == 'rel':
        return bool(members[env[formula[2]]] & (1 << env[formula[1]]))
    if op == 'imp':
        return not value(formula[1], members, env) or value(formula[2], members, env)
    return all(value(formula[1], members, (x,) + env) for x in range(len(members)))


def direct_psc(matrix, members, parameters):
    n = len(members)
    def mem(x, y):
        return bool(members[y] & (1 << x))
    def sub(x, y):
        return (members[x] & ~members[y]) == 0
    def rho(x, y):
        return ns.evaluate(matrix, members, parameters | {0: x, 1: y})
    locally_bounded = all(any(all(not rho(x, y) or sub(y, b) for y in range(n))
                              for b in range(n)) for x in range(n))
    if not locally_bounded:
        return True
    return all(any(
        all(not ((sub(x, a) or mem(x, c)) and rho(x, y)) or mem(y, c)
            for x in range(n) for y in range(n))
        and all(not mem(y, c) or any(rho(x, y) for x in range(n)) for y in range(n))
        for c in range(n)) for a in range(n))


def ui_certificate():
    # forall y forall z ((forall x R(x,y)) -> R(z,y))
    formula = ('all', ('all', ('imp', ('all', ('rel', 0, 2)), ('rel', 0, 1))))
    proof = ['all', 0, ['all', 1, ['imp', 2,
             ['all', 3, 2, ['close', 4, 5]]]]]
    return {'matrices': [], 'theorem': formula, 'proof': proof}


class TableauTests(unittest.TestCase):
    def test_missing_instantiation_witness_is_accepted(self):
        result = t.check_certificate(ui_certificate())
        self.assertTrue(result['valid'])
        self.assertFalse(result['refutation'])
        self.assertEqual(result['closed_branches'], 1)
        f = t.parse_formula(ui_certificate()['theorem'])
        for n in (1, 2, 3):
            for relation in range(1 << (n*n)):
                members = tuple((relation >> (n*y)) & ((1 << n)-1) for y in range(n))
                self.assertTrue(value(f, members))

    def test_wrong_parameter_does_not_close(self):
        certificate = ui_certificate()
        certificate['proof'][2][2][2][2] = 1
        with self.assertRaises(ValueError):
            t.check_certificate(certificate)

    def test_alpha_conversion_has_identical_debruijn_formula(self):
        a = ns.All([0, 1], ns.E(0, 1))
        b = ns.All([2, 1], ns.E(2, 1))
        self.assertEqual(t.from_named(a), t.from_named(b))

    def test_schema_identity_with_parameters_and_nested_binders(self):
        matrix = ns.I(ns.E(0, 2), ns.A(0, ns.I(ns.E(0, 1), ns.E(2, 0))))
        axiom = t.psc_axiom(matrix)
        certificate = {'matrices': [matrix], 'theorem': axiom,
                       'proof': t.identity_tree(axiom, 0, 1, 2)}
        result = t.check_certificate(certificate)
        self.assertTrue(result['valid'])
        self.assertFalse(result['refutation'])
        (ROOT/'examples/schema_identity.json').write_text(json.dumps(certificate, indent=2)+'\n')

    def test_template_against_direct_finite_semantics(self):
        matrices = [ns.B, ns.E(0, 1), ns.N(ns.E(1, 0)),
                    ns.I(ns.E(0, 2), ns.E(2, 1)),
                    ns.A(0, ns.I(ns.E(0, 1), ns.E(2, 0)))]
        checked = 0
        for matrix in matrices:
            generated = t.psc_axiom(matrix)
            params = sorted(ns.free(matrix)-{0, 1})
            for n in (1, 2):
                for relation in range(1 << (n*n)):
                    members = tuple((relation >> (n*y)) & ((1 << n)-1) for y in range(n))
                    expected = all(direct_psc(matrix, members, dict(zip(params, values)))
                                   for values in itertools.product(range(n), repeat=len(params)))
                    self.assertEqual(value(generated, members), expected)
                    checked += 1
        self.assertEqual(checked, 90)

    def test_boolean_tableau_branches_and_bottom(self):
        atom = ('rel', 0, 0)
        formulas = [t.BOT, atom, ('imp', atom, atom),
                    ('imp', ('imp', atom, t.BOT), atom)]
        for formula in formulas:
            env = (0,)
            result = t.check_tree([t.Entry(True, formula, env), t.Entry(False, formula, env)],
                                  t.identity_tree(formula, 0, 1, 2))
            self.assertTrue(result['valid'])
        with self.assertRaises(ValueError):
            t.check_tree([t.Entry(False, t.BOT)], ['bottom', 0])

    def test_strict_rejection(self):
        for raw in ([], ['eq', 0, 0], ['rel', True, 0], ['all'], ['top'], ['bot', 1]):
            with self.assertRaises(ValueError):
                t.parse_formula(raw)
        with self.assertRaises(ValueError):
            t.check_certificate({'matrices': [], 'proof': ['close', 0, 0]})
        with self.assertRaises(ValueError):
            t.check_certificate({'matrices': [], 'proof': ['bottom', -1]})
        with self.assertRaises(ValueError):
            t.check_certificate({'matrices': [], 'proof': ['bottom', 0], 'axiom': ['bot']})
        with self.assertRaises(ValueError):
            t.check_certificate({'matrices': [], 'theorem': ['rel', 0, 1], 'proof': []})
        with self.assertRaises(ValueError):
            t.check_certificate({'matrices': [['eq', 0, 0]], 'proof': []})
        with self.assertRaises(ValueError):
            t.check_tree([t.Entry(False, ('all', ('rel', 0, 0)))],
                         ['all', 0, 0, ['close', 0, 0]])


if __name__ == '__main__':
    (ROOT/'examples/ui.json').write_text(json.dumps(ui_certificate(), indent=2)+'\n')
    suite = unittest.defaultTestLoader.loadTestsFromTestCase(TableauTests)
    result = unittest.TextTestRunner(verbosity=2).run(suite)
    evidence = {'tests_run': result.testsRun, 'failures': len(result.failures),
                'errors': len(result.errors), 'passed': result.wasSuccessful(),
                'template_semantics_cases': 90, 'ui_semantics_relations': 530,
                'scope': 'Finite reference-checker regressions, not a formal proof or TM compilation'}
    (ROOT/'results/tableau_tests.json').write_text(json.dumps(evidence, indent=2)+'\n')
    raise SystemExit(0 if result.wasSuccessful() else 1)
