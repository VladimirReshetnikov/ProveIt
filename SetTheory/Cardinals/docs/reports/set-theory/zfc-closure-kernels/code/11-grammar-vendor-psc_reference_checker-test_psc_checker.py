#!/usr/bin/env python3
"""Regression tests for the reference format, not a consistency proof."""
import itertools
import random
import unittest
from unittest.mock import patch

import psc_checker as p


def evaluate(arena, formula, membership, env, domain=2):
    """Independent simple semantics for shallow test formulas only."""
    node = arena.nodes[formula]
    if node[0] == p.BOT:
        return False
    if node[0] == p.MEM:
        return bool(membership & (1 << (env[node[1]] * domain + env[node[2]])))
    if node[0] == p.IMP:
        return (not evaluate(arena, node[1], membership, env, domain)
                or evaluate(arena, node[2], membership, env, domain))
    return all(evaluate(arena, node[2], membership, env | {node[1]: x}, domain)
               for x in range(domain))


class CheckerTests(unittest.TestCase):
    def setUp(self):
        self.a = p.Arena()

    def derive(self, *lines):
        return p.check_derivation(p.encode_certificate(self.a, lines))

    def test_formula_roundtrip_and_interning(self):
        a = self.a
        rng = random.Random(20261016)
        formulas = [a.bottom] + [a.mem(x, y) for x in range(4) for y in range(4)]
        for _ in range(200):
            if rng.randrange(2):
                formulas.append(a.imp(rng.choice(formulas), rng.choice(formulas)))
            else:
                formulas.append(a.all(rng.randrange(4), rng.choice(formulas)))
        for formula in formulas:
            bits = p.encode_formula(a, formula)
            self.assertEqual(formula, p.decode_formula(a, bits))
            b = p.Arena()
            decoded = p.decode_formula(b, bits)
            self.assertEqual(bits, p.encode_formula(b, decoded))
        self.assertEqual(a.mem(0, 1), a.mem(0, 1))
        self.assertNotEqual(a.all(0, a.mem(0, 1)), a.all(2, a.mem(2, 1)))

    def test_primitive_bottom_distinct_from_self_membership(self):
        self.assertEqual(p.encode_formula(self.a, self.a.bottom), "00")
        self.assertEqual(p.encode_formula(self.a, self.a.mem(0, 0)), "0111")
        self.assertNotEqual(self.a.bottom, self.a.mem(0, 0))

    def test_nat_and_formula_validation(self):
        for bad in (-1, True, False, 1.0, "1", None):
            with self.assertRaises(p.CertificateError):
                self.a.mem(bad, 0)
            with self.assertRaises(p.CertificateError):
                self.a.substitute(self.a.bottom, {bad: bad})
        for bad in ("", "0", "01", "010", "10", "110", "001", "00\n", "2"):
            with self.assertRaises(p.CertificateError):
                p.decode_formula(self.a, bad)

    def test_capture_avoiding_substitution(self):
        a = self.a
        original = a.all(1, a.mem(0, 1))
        renamed = a.substitute(original, {0: 1})
        self.assertEqual(renamed, a.all(2, a.mem(1, 2)))
        self.assertEqual(a.free[renamed], {1})
        self.assertNotEqual(renamed, a.all(1, a.mem(1, 1)))
        self.assertEqual(a.substitute(a.all(0, a.mem(0, 1)), {0: 1}),
                         a.all(0, a.mem(0, 1)))
        self.assertEqual(a.substitute(a.mem(0, 1), {0: 1, 1: 0}), a.mem(1, 0))
        nested = a.all(1, a.imp(a.mem(0, 1), a.all(1, a.mem(0, 1))))
        expected = a.all(2, a.imp(a.mem(1, 2), a.all(3, a.mem(1, 3))))
        self.assertEqual(a.substitute(nested, {0: 1}), expected)

    def test_substitution_semantics_in_finite_graphs(self):
        a = self.a
        rng = random.Random(87654)

        def small(depth):
            choice = rng.randrange(4) if depth else rng.randrange(2)
            if choice == 0:
                return a.bottom
            if choice == 1:
                return a.mem(rng.randrange(3), rng.randrange(3))
            if choice == 2:
                return a.imp(small(depth - 1), small(depth - 1))
            return a.all(rng.randrange(3), small(depth - 1))

        maps = ({0: 1}, {0: 1, 1: 0}, {0: 2, 2: 1}, {0: 1, 2: 1},
                {0: 3, 1: 2, 2: 0}, {0: 0})
        for _ in range(100):
            formula = small(4)
            for sigma in maps:
                substituted = a.substitute(formula, sigma)
                for _ in range(20):
                    graph = rng.randrange(16)
                    env = {v: rng.randrange(2) for v in range(4)}
                    original_env = env | {v: env[w] for v, w in sigma.items()}
                    self.assertEqual(evaluate(a, substituted, graph, env),
                                     evaluate(a, formula, graph, original_env))

    def test_deep_iterative_paths(self):
        a = self.a
        formula = a.mem(0, 1)
        for _ in range(5000):
            formula = a.all(1, formula)
        bits = p.encode_formula(a, formula)
        self.assertEqual(p.decode_formula(a, bits), formula)
        result = a.substitute(formula, {0: 2})
        self.assertEqual(a.free[result], {2})
        self.assertEqual(len(p.encode_formula(a, result)), len(bits) + 2)
        # Certificate parsing, UI generation, and output encoding also traverse
        # the deep tree, without borrowing the shallow test evaluator.
        derivation = self.derive(p.Line(p.UI, (0, 2, formula)))
        self.assertFalse(derivation.is_refutation)
        p.encode_formula(derivation.arena, derivation.conclusion)

    def test_identity_certificate(self):
        bits, arena, expected = p.identity_certificate()
        derivation = p.check_derivation(bits)
        self.assertEqual(len(derivation.lines), 5)
        self.assertEqual(p.encode_formula(derivation.arena, derivation.conclusion),
                         p.encode_formula(arena, expected))
        self.assertFalse(derivation.is_refutation)
        self.assertFalse(p.accepts_refutation(bits))
        self.assertEqual(len(bits), 80)

    def test_logical_axioms_and_generalization(self):
        a = self.a
        atom, b = a.mem(0, 1), a.mem(1, 0)
        closed = a.all(0, a.all(1, atom))
        lines = (p.Line(p.K, (atom, b)), p.Line(p.S, (atom, b, a.bottom)),
                 p.Line(p.C, (atom, b)), p.Line(p.UI, (0, 1, a.all(1, atom))),
                 p.Line(p.UD, (0, closed, atom)), p.Line(p.GEN, (0, 0)))
        result = self.derive(*lines)
        for graph in range(16):
            for x, y in itertools.product(range(2), repeat=2):
                for formula in result.lines:
                    self.assertTrue(evaluate(result.arena, formula, graph, {0: x, 1: y}))
        # The precise A3 is full classical contraposition with genuine Bottom.
        expected = a.imp(a.imp(a.neg(atom), a.neg(b)), a.imp(b, atom))
        self.assertEqual(p.encode_formula(result.arena, result.lines[2]),
                         p.encode_formula(a, expected))

    def test_psc_parameters_shadowing_and_closure(self):
        a = self.a
        matrices = (a.bottom, a.mem(0, 1), a.mem(5, 7),
                    a.all(1, a.imp(a.mem(0, 1), a.mem(7, 2))),
                    a.all(0, a.mem(0, 1)),
                    a.neg(a.mem(0, 1)))
        for matrix in matrices:
            schema = a.psc(matrix)
            self.assertEqual(a.free[schema], set())
            self.assertTrue(all(node[0] in (p.BOT, p.MEM, p.IMP, p.ALL)
                                for node in a.nodes))
            result = self.derive(p.Line(p.PSC, (matrix,)))
            self.assertEqual(p.encode_formula(result.arena, result.conclusion),
                             p.encode_formula(a, schema))
            self.assertFalse(result.is_refutation)
        # Matrices with no occurrence of one or both distinguished variables
        # are deliberately permitted by the full schema.

    def test_mp_and_gen_reject_nonprior_or_mismatched_references(self):
        a = self.a
        atom = a.mem(0, 1)
        k = p.Line(p.K, (atom, atom))
        cases = ((p.Line(p.MP, (0, 0)),), (p.Line(p.GEN, (0, 0)),),
                 (k, p.Line(p.MP, (1, 0))), (k, p.Line(p.GEN, (1, 0))),
                 (k, p.Line(p.MP, (0, 0))))
        for lines in cases:
            with self.assertRaises(p.CertificateError):
                self.derive(*lines)
        with self.assertRaises(p.CertificateError):
            self.derive(p.Line(p.UD, (0, atom, atom)))

    def test_invalid_truncations_and_suffixes(self):
        identity, _, _ = p.identity_certificate()
        for size in range(len(identity)):
            with self.assertRaises(p.CertificateError):
                p.check_derivation(identity[:size])
        for suffix in ("0", "1", "00", "\n", " "):
            with self.assertRaises(p.CertificateError):
                p.check_derivation(identity + suffix)
        for bad in ("", "0", "000", "2", "01", "01xxx", "11"):
            self.assertFalse(p.accepts_refutation(bad))
        empty = p.check_derivation("1")
        self.assertIsNone(empty.conclusion)
        self.assertFalse(empty.is_refutation)

    def test_resource_failures_propagate(self):
        with patch.object(p, "check_derivation", side_effect=MemoryError("test")):
            with self.assertRaises(MemoryError):
                p.accepts_refutation("1")


if __name__ == "__main__":
    unittest.main(verbosity=2)
