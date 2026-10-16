"""Regression tests for BIC syntax and the unverified reference checker."""
import itertools
import json
import unittest
from logic import (E, Eq, Hole, Not, Imp, All, Ex, And, free_variables,
                   alpha_key, substitute, evaluate, erase_equality)
from bic import (bic, inhabited, from_data, to_data, bottom, check,
                 identity_certificate, normalize_double_negation)


class Tests(unittest.TestCase):
    def test_identity_and_generalization(self):
        p = E(0, 0)
        proof = identity_certificate(p) + [['GEN', 0, 4]]
        self.assertEqual(check(proof)[-1], All(0, Imp(p, p)))
        self.assertNotEqual(alpha_key(check(proof)[-1]), alpha_key(bottom()))

    def test_axiom_generators_are_closed(self):
        matrix = And(E(0, 3), All(5, Imp(E(5, 1), E(2, 5))))
        for rec in [['N'], ['CG'], ['BIC', to_data(matrix)]]:
            self.assertFalse(free_variables(check([rec])[0]))

    def test_capture_avoidance(self):
        a = Ex(1, E(0, 1))
        got = check([['Q1', 0, 1, to_data(a)]])[0]
        expected = Imp(All(0, a), Ex(2, E(1, 2)))
        self.assertEqual(alpha_key(got), alpha_key(expected))
        self.assertNotEqual(alpha_key(substitute(a, 0, 1)), alpha_key(Ex(1, E(1, 1))))

    def test_bad_side_condition(self):
        with self.assertRaises(ValueError):
            check([['Q2', 0, to_data(E(0, 1)), to_data(E(2, 1))]])

    def test_bad_proof_references(self):
        for proof in [[['MP', 0, 0]], [['GEN', 0, 0]],
                      [['N'], ['CG'], ['MP', 0, 1]], [['admit', to_data(bottom())]]]:
            with self.assertRaises(ValueError):
                check(proof)

    def test_alpha_rule(self):
        c = identity_certificate(E(0, 0)) + [['GEN', 0, 4]]
        good = All(1, Imp(E(1, 1), E(1, 1)))
        self.assertEqual(check(c + [['ALPHA', 5, to_data(good)]])[-1], good)
        with self.assertRaises(ValueError):
            check(c + [['ALPHA', 5, to_data(bottom())]])

    def test_strict_parser(self):
        for bad in [['=', 0, 1], ['phi', 0, 1], ['E', True, 0], ['E', -1, 0],
                    ['not'], ['all', 0, ['E', 0, 1], 2], {'E': [0, 1]}]:
            with self.assertRaises(ValueError):
                from_data(bad)
        f = All(0, Imp(E(0, 2), Ex(1, E(1, 0))))
        self.assertEqual(from_data(to_data(f)), f)

    def test_equality_erasure_commutes_with_bic(self):
        matrices = [Eq(0, 1), And(E(0, 2), Eq(1, 2)),
                    All(1, Imp(Eq(0, 1), E(1, 3)))]
        for f in matrices:
            self.assertEqual(alpha_key(erase_equality(bic(f))),
                             alpha_key(bic(erase_equality(f))))

    def test_singleton_ablation_models(self):
        for bit in [False, True]:
            phi = lambda x, y, bit=bit: bit
            empty = lambda x, y: False
            universal = lambda x, y: True
            self.assertTrue(evaluate(bic(), 1, empty, phi=phi))
            self.assertTrue(evaluate(bic(pure=False), 1, universal, phi=phi))
        self.assertFalse(evaluate(inhabited(), 1, empty))
        self.assertTrue(evaluate(inhabited(), 1, universal))
        self.assertFalse(evaluate(bic(), 1, universal, phi=lambda x, y: False))

    def test_logical_axioms_on_small_structures(self):
        a, b, c = E(0, 1), All(0, E(0, 1)), Ex(1, E(1, 0))
        records = [['L1', to_data(a), to_data(b)],
                   ['L2', to_data(a), to_data(b), to_data(c)],
                   ['L3', to_data(a), to_data(b)],
                   ['Q1', 0, 1, to_data(c)],
                   ['Q2', 2, to_data(a), to_data(c)]]
        forms = check(records)
        for n in [1, 2]:
            for mask in range(1 << (n*n)):
                mem = lambda x, y, mask=mask: bool(mask & (1 << (x*n+y)))
                for vals in itertools.product(range(n), repeat=3):
                    env = dict(enumerate(vals))
                    for f in forms:
                        self.assertTrue(evaluate(f, n, mem, env))

    def test_normalization_semantics(self):
        for mem_bit, phi_bit in itertools.product([False, True], repeat=2):
            m = lambda x, y: mem_bit
            p = lambda x, y: phi_bit
            self.assertEqual(evaluate(bic(), 1, m, phi=p),
                             evaluate(normalize_double_negation(bic()), 1, m, phi=p))

    def test_schema_has_no_accidental_free_variables(self):
        for k in range(2, 20):
            f = All(k, Imp(E(0, k), Ex(0, E(0, 1))))
            self.assertFalse(free_variables(bic(f)))


if __name__ == '__main__':
    unittest.main(verbosity=2)
