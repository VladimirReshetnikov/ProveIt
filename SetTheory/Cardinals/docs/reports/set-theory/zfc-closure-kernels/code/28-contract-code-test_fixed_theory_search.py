#!/usr/bin/env python3
"""Check exact schema emitters, public refutation boundaries, and enumeration."""

from itertools import product
from pathlib import Path
import json
import unittest

import contraction_kernel as k
import fixed_theory_search as f


def matrices():
    atoms = [k.R(k.F(i), k.F(j)) for i, j in product(range(4), repeat=2)]
    return [k.BOT] + atoms + [k.Not(a) for a in atoms] + [
        k.Imp(k.R(k.F(0), k.F(i)), k.All(k.R(k.B(0), k.F(i))))
        for i in range(4)] + [
        k.All(k.R(k.B(0), k.F(1))),
        k.All(k.Imp(k.R(k.B(0), k.F(2)), k.All(k.R(k.B(1), k.F(3))))),
        k.All(k.source19_body()),
    ]


class FixedTheoryTests(unittest.TestCase):
    def test_cp_exact_literal_semantics(self):
        self.assertTrue(k.scoped(f.CP))
        self.assertFalse(k.free_names(f.CP))
        for n in (1, 2):
            domain = tuple(range(n))
            for graph in range(1 << (n * n)):
                rel = lambda a, b, graph=graph: bool(graph & (1 << (n * a + b)))
                self.assertEqual(k.evaluate(f.CP, domain, rel, lambda _: 0),
                                 f.direct_cp(domain, rel))

    def test_both_schema_emitters_against_literal_semantics(self):
        pool = matrices()
        self.assertEqual(len(pool), 40)
        comparisons = 0
        for n in (1, 2):
            domain = tuple(range(n))
            for graph in range(1 << (n * n)):
                rel = lambda a, b, graph=graph: bool(graph & (1 << (n * a + b)))
                for matrix in pool:
                    for emit, literal in ((f.gic_axiom, f.direct_gic),
                                          (f.epsc2_axiom, f.direct_epsc2)):
                        axiom = emit(matrix)
                        self.assertTrue(k.scoped(axiom))
                        self.assertFalse(k.free_names(axiom))
                        self.assertEqual(k.evaluate(axiom, domain, rel, lambda _: 0),
                                         literal(matrix, domain, rel))
                        comparisons += 1
        self.assertEqual(comparisons, 1440)

    def test_gic_arbitrary_signed_parameters(self):
        matrix = k.Imp(k.R(k.F(0), k.F(-8)),
                       k.All(k.Imp(k.R(k.B(0), k.F(1)), k.R(k.F(21), k.B(0)))))
        axiom = f.gic_axiom(matrix)
        self.assertTrue(k.scoped(axiom))
        self.assertFalse(k.free_names(axiom))
        for graph in range(16):
            rel = lambda a, b, graph=graph: bool(graph & (1 << (2 * a + b)))
            self.assertEqual(k.evaluate(axiom, (0, 1), rel, lambda _: 0),
                             f.direct_gic(matrix, (0, 1), rel))
        with self.assertRaises(ValueError):
            f.epsc2_axiom(matrix)

    def test_profile_relation_is_congruence(self):
        o = f.observational_equality(k.F(0), k.F(1))
        for graph in range(16):
            rel = lambda a, b, graph=graph: bool(graph & (1 << (2 * a + b)))
            def eq(a, b):
                return k.evaluate(o, (0, 1), rel, {0: a, 1: b}.__getitem__)
            for a, b, c in product((0, 1), repeat=3):
                self.assertTrue(eq(a, a))
                self.assertEqual(eq(a, b), eq(b, a))
                self.assertTrue(not (eq(a, b) and eq(b, c)) or eq(a, c))
                if eq(a, b):
                    self.assertEqual(rel(a, c), rel(b, c))
                    self.assertEqual(rel(c, a), rel(c, b))
        translated = f.erase_equality(k.All(('eq', k.B(0), k.F(2))))
        self.assertTrue(k.scoped(translated))
        self.assertEqual(k.free_names(translated), {2})

    def test_boundary_does_not_accept_custom_theory_or_target(self):
        p = k.All(k.R(k.B(0), k.B(0)))
        proof = [{'op': 'axiom', 'index': 0}, {'op': 'axiom', 'index': 1},
                 {'op': 'mp', 'implication': 1, 'antecedent': 0}]
        # Generic logic correctly refutes P, not P.
        self.assertEqual(k.check_certificate({'instructions': proof}, [p, k.Not(p)])[-1], k.BOT)
        candidate = {'matrices': [p, k.Not(p)], 'proof': proof}
        for check in (f.check_refutation, f.check_epsc2_refutation):
            with self.assertRaises(ValueError):
                check(candidate)
            with self.assertRaises(ValueError):
                check(candidate | {'theory': [p, k.Not(p)]})
            with self.assertRaises(ValueError):
                check(candidate | {'target': p})
            with self.assertRaises(ValueError):
                check({'matrices': [k.BOT], 'proof': [{'op': 'axiom', 'index': 0}]})
            with self.assertRaises(ValueError):
                check({'matrices': [], 'proof': k.make_ui_certificate(k.R(k.B(0), k.F(0)), 0)['instructions']})

    def test_illscoped_matrices_rejected(self):
        for matrix in (k.R(k.B(0), k.F(0)), k.R(k.B(-1), k.F(0)),
                       k.R(k.F(True), k.F(1))):
            for emit in (f.gic_axiom, f.epsc2_axiom):
                with self.assertRaises(ValueError):
                    emit(matrix)
        with self.assertRaises(ValueError):
            f.epsc2_axiom(k.R(k.F(0), k.F(4)))

    def test_shortlex_inverse_and_boundaries(self):
        samples = list(range(66000)) + [256 ** 20 + 9, 256 ** 80 - 1]
        for n in samples:
            data = f.shortlex_bytes_at(n)
            self.assertEqual(f.index_of_bytes(data), n)
        self.assertEqual(f.shortlex_bytes_at(0), b'')
        self.assertEqual(f.shortlex_bytes_at(1), b'\x00')
        self.assertEqual(f.shortlex_bytes_at(256), b'\xff')
        self.assertEqual(f.shortlex_bytes_at(257), b'\x00\x00')
        samples = [b'', b'\x00', b'\xff', b'{}', b'{"matrices":[],"proof":[]}']
        for data in samples:
            self.assertEqual(f.shortlex_bytes_at(f.index_of_bytes(data)), data)

    def test_decoding_and_invalid_candidates(self):
        invalid = [b'', b'\xff', b'null', b'0', b'{}', b'[]',
                   b'{"matrices": [], "proof": []}',
                   b'{"matrices": [NaN], "proof": []}',
                   b'{"matrices": [], "proof": [{"op": "assume"}]}']
        for data in invalid:
            self.assertFalse(f.accepts_bytes(data))
            self.assertFalse(f.accepts_bytes(data, alternative=True))


if __name__ == '__main__':
    suite = unittest.defaultTestLoader.loadTestsFromTestCase(FixedTheoryTests)
    result = unittest.TextTestRunner(verbosity=2).run(suite)
    if not result.wasSuccessful():
        raise SystemExit(1)
    base = Path(__file__).resolve().parent
    summary = {
        'fixed_public_entries': ['CP+GIC, without IR', 'EPSC2'],
        'candidate_supplied_axioms': False,
        'candidate_supplied_target': False,
        'acceptance_target': 'genuine BOT',
        'schema_semantic_comparisons': 1440,
        'cp_semantic_comparisons': 18,
        'arbitrary_signed_parameter_gic_comparisons': 16,
        'shortlex_index_roundtrips': 66002,
        'public_boundary_controls': 'reject custom theories, targets, and accepted non-refutation theorems',
        'scope': 'finite implementation checks; general calibration is a mathematical proof',
    }
    (base / 'fixed_theory_verification.json').write_text(json.dumps(summary, indent=2) + '\n')
    (base / 'example_axioms.json').write_text(json.dumps({
        'CP': f.CP, 'GIC_false': f.gic_axiom(k.BOT),
        'EPSC2_false': f.epsc2_axiom(k.BOT),
        'GIC_membership': f.gic_axiom(k.R(k.F(0), k.F(1))),
    }, indent=2) + '\n')
