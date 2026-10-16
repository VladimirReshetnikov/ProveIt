#!/usr/bin/env python3
"""Independent finite checks for the contraction proposal, with audit JSON.

These checks exercise the syntactic implementation and concrete witnesses.
The manuscript's structural arguments, not the finite checks, prove general
soundness, completeness, and finite-map generation.
"""

from __future__ import annotations

from itertools import product
from pathlib import Path
import json
import random
import unittest

import contraction_kernel as k


class KernelTests(unittest.TestCase):
    def test_scope_and_sort_distinction(self):
        self.assertFalse(k.scoped(k.R(k.B(0), k.F(0))))
        self.assertTrue(k.scoped(k.All(k.R(k.B(0), k.F(0)))))
        self.assertFalse(k.scoped(k.All(k.R(k.B(1), k.F(0)))))
        a = k.All(k.R(k.B(0), k.F(0)))
        self.assertEqual(k.rename_step('contract', a),
                         k.All(k.R(k.B(0), k.F(1))))
        self.assertEqual(k.rename_step('up', a), k.All(k.R(k.B(0), k.F(1))))

    def test_nested_open_and_close(self):
        body = k.Imp(k.R(k.B(0), k.F(4)),
                     k.All(k.Imp(k.R(k.B(1), k.B(0)), k.R(k.F(4), k.B(1)))))
        self.assertTrue(k.scoped(body, 1))
        expected = k.Imp(k.R(k.F(4), k.F(4)),
                         k.All(k.Imp(k.R(k.F(4), k.B(0)), k.R(k.F(4), k.F(4)))))
        self.assertEqual(k.open_body(body, 4), expected)
        a = k.All(k.R(k.B(0), k.F(-3)))
        self.assertEqual(k.open_body(k.close_name(a, -3), -3), a)
        self.assertEqual(k.close_name(a, -3), k.All(k.R(k.B(0), k.B(1))))

    def test_fixed_swap_and_contraction_words(self):
        for a, b in product(range(-4, 5), repeat=2):
            swap = k.swap_word(a, b)
            contract = k.contract_name_word(a, b)
            for x in range(-7, 8):
                expected_swap = b if x == a else a if x == b else x
                self.assertEqual(k.run_name_word(swap, x), expected_swap)
                expected_contract = b if x == a else x
                self.assertEqual(k.run_name_word(contract, x), expected_contract)
            self.assertEqual(contract.count('contract'), int(a != b))

    def test_all_small_total_maps(self):
        count = 0
        for n in range(6):
            for values in product(range(n), repeat=n):
                mapping = dict(enumerate(values))
                word = k.factor_on_support(mapping)
                for a, b in mapping.items():
                    self.assertEqual(k.run_name_word(word, a), b)
                self.assertEqual(word.count('contract'), n - len(set(values)))
                # These maps are total and the construction fixes outside support.
                for outside in (-7, -1, n + 5):
                    self.assertEqual(k.run_name_word(word, outside), outside)
                count += 1
        self.assertEqual(count, 3414)

    def test_partial_maps_with_signed_images(self):
        rng = random.Random(20261016)
        for _ in range(400):
            sources = rng.sample(range(-12, 13), rng.randrange(1, 9))
            mapping = {s: rng.randrange(-12, 13) for s in sources}
            word = k.factor_on_support(mapping)
            for source, target in mapping.items():
                self.assertEqual(k.run_name_word(word, source), target)
            self.assertEqual(word.count('contract'), len(mapping) - len(set(mapping.values())))

    def test_total_signed_map_fixes_unused_generator_names(self):
        mapping = {-3: 5, 5: 5}
        word = k.factor_on_support(mapping)
        for name in range(-8, 9):
            self.assertEqual(k.run_name_word(word, name), mapping.get(name, name))

    def test_concrete_colliding_ui_certificates(self):
        bodies = [k.source19_body(),
                  k.All(k.R(k.B(1), k.F(0))),
                  k.Imp(k.R(k.B(0), k.F(4)),
                        k.All(k.Imp(k.R(k.B(1), k.B(0)), k.R(k.F(4), k.B(1))))) ]
        for body in bodies:
            for target in range(-2, 6):
                cert = k.make_ui_certificate(body, target)
                lines = k.check_certificate(cert)
                self.assertEqual(lines[-1], k.Imp(k.All(body), k.open_body(body, target)))
                expected = int(target in k.free_names(body))
                self.assertEqual(sum(i['op'] == 'contract' for i in cert['instructions']), expected)

    def test_source19_counterinterpretation_rejected(self):
        rows = k.source19_bad_semantics()
        self.assertEqual(len(rows), 8)
        self.assertTrue(all(row['body'] for row in rows))
        self.assertTrue(all(not row['identified_body'] for row in rows))
        self.assertTrue(all(not row['ui_instance'] for row in rows))
        self.assertTrue(k.check_certificate(k.make_ui_certificate(k.source19_body(), 0)))

    def test_semantic_renaming_and_ui(self):
        bodies = [k.source19_body(), k.R(k.B(0), k.F(-1)),
                  k.All(k.Imp(k.R(k.B(1), k.B(0)), k.R(k.F(0), k.B(1))))]
        domain = (0, 1)
        checks = 0
        for graph in range(16):
            relation = lambda a, b, graph=graph: bool(graph & (1 << (2 * a + b)))
            for body in bodies:
                for target in (-1, 0, 1, 2):
                    formula = k.check_certificate(k.make_ui_certificate(body, target))[-1]
                    names = sorted(k.free_names(formula))
                    for values in product(domain, repeat=len(names)):
                        assignment_dict = dict(zip(names, values))
                        assignment = lambda n: assignment_dict.get(n, n % 2)
                        self.assertTrue(k.evaluate(formula, domain, relation, assignment))
                        for op in k.RENAMINGS:
                            renamed = k.rename_step(op, formula)
                            rhs_assignment = lambda n, op=op: assignment(k.name_step(op, n))
                            self.assertEqual(k.evaluate(renamed, domain, relation, assignment),
                                             k.evaluate(formula, domain, relation, rhs_assignment))
                            checks += 1
        self.assertEqual(checks, 3328)

    def test_renaming_semantics_on_nontautologies(self):
        formulas = [k.All(k.R(k.B(0), k.F(0))),
                    k.R(k.F(0), k.F(1)), k.R(k.F(-2), k.F(3)),
                    k.All(k.source19_body())]
        domain = (0, 1)
        for formula in formulas:
            for op in k.RENAMINGS:
                names = sorted(k.free_names(formula) |
                               {k.name_step(op, n) for n in k.free_names(formula)})
                renamed = k.rename_step(op, formula)
                for graph in range(16):
                    relation = lambda a, b, graph=graph: bool(graph & (1 << (2 * a + b)))
                    for values in product(domain, repeat=len(names)):
                        eta = dict(zip(names, values))
                        assignment = lambda n: eta.get(n, 0)
                        transported = lambda n: assignment(k.name_step(op, n))
                        self.assertEqual(k.evaluate(renamed, domain, relation, assignment),
                                         k.evaluate(formula, domain, relation, transported))

    def test_generalization_closes_only_free_name(self):
        a = k.All(k.R(k.B(0), k.F(-1)))
        cert = {'instructions': [{'op': 'K', 'a': a, 'b': k.BOT},
                                 {'op': 'gen', 'line': 0, 'name': -1}]}
        lines = k.check_certificate(cert)
        self.assertFalse(k.free_names(lines[-1]))
        self.assertTrue(k.scoped(lines[-1]))

    def test_complete_propositional_core(self):
        a = k.R(k.F(3), k.F(4))
        # Standard K,S derivation of A -> A; all conclusions reconstructed.
        instructions = [
            {'op': 'K', 'a': a, 'b': k.Imp(a, a)},
            {'op': 'K', 'a': a, 'b': a},
            {'op': 'S', 'a': a, 'b': k.Imp(a, a), 'c': a},
            {'op': 'mp', 'implication': 2, 'antecedent': 0},
            {'op': 'mp', 'implication': 3, 'antecedent': 1},
        ]
        lines = k.check_certificate({'instructions': instructions,
                                     'conclusion': k.Imp(a, a)})
        self.assertEqual(lines[-1], k.Imp(a, a))

    def test_reject_unsafe_or_malformed_certificates(self):
        body = k.R(k.B(0), k.F(0))
        bad = [
            {'instructions': [{'op': 'fresh_ui', 'body': body, 'fresh': 0}]},
            {'instructions': [{'op': 'fresh_ui', 'body': k.R(k.B(1), k.F(0)), 'fresh': 1}]},
            {'instructions': [{'op': 'contract', 'line': 0}]},
            {'instructions': [{'op': 'assume', 'a': k.R(k.F(0), k.F(0))}]},
            {'instructions': [{'op': 'axiom', 'index': 0}]},
            {'instructions': [{'op': 'K', 'a': k.BOT, 'b': k.BOT, 'result': k.BOT}]},
            {'instructions': [{'op': 'K', 'a': k.BOT, 'b': k.BOT},
                              {'op': 'mp', 'implication': 0, 'antecedent': 0}]},
        ]
        for cert in bad:
            with self.assertRaises(ValueError):
                k.check_certificate(cert)
        with self.assertRaises(ValueError):
            k.check_certificate({'instructions': []}, [k.R(k.F(0), k.F(0))])


def write_audit():
    base = Path(__file__).resolve().parent
    cert = k.make_ui_certificate(k.source19_body(), 0)
    lines = k.check_certificate(cert)
    (base / 'colliding_ui_certificate.json').write_text(json.dumps(cert, indent=2) + '\n')
    (base / 'counterinterpretation_rows.json').write_text(
        json.dumps(k.source19_bad_semantics(), indent=2) + '\n')
    summary = {
        'status': 'reference implementation verified by finite checks',
        'primitive_free_name_maps': ['up', 'down', 'swap', 'contract'],
        'contract': '0 -> 1; all other free names fixed; bound indices copied',
        'source19_ui_certificate_lines': len(lines),
        'source19_ui_contractions': sum(i['op'] == 'contract' for i in cert['instructions']),
        'exhaustive_total_maps_through_n5': 3414,
        'seeded_signed_partial_maps': 400,
        'source19_counterinterpretation_rows_falsifying_ui': 8,
        'limitations': [
            'No literal Turing machine is generated.',
            'No machine-state upper bound is claimed.',
            'The general proof is mathematical, not proof-assistant checked.',
            'Fresh UI and generalization retain bound-variable open/close operations.',
            'Finite tests do not prove consistency of any set theory.',
        ],
    }
    (base / 'verification.json').write_text(json.dumps(summary, indent=2) + '\n')


if __name__ == '__main__':
    suite = unittest.defaultTestLoader.loadTestsFromTestCase(KernelTests)
    result = unittest.TextTestRunner(verbosity=2).run(suite)
    if not result.wasSuccessful():
        raise SystemExit(1)
    write_audit()
