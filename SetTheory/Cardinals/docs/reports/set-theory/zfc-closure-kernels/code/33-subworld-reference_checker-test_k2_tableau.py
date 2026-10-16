"""Regression checks, including independent exhaustive finite interpretations.

No test claims to refute K2+.  Accepted certificates have synthetic,
independently recognizable contradictory roots, not the kernel sentence.
"""
import unittest
from itertools import product

from k2_tableau import (
    ALL, BOT, EQ, IMP, MEM, CLOSE, F_ALL, F_IMP, T_ALL, T_IMP,
    Branch, InvalidMatrix, Syntax, candidate_code, check_code, clash,
    decode_list, instruction, kernel_components, kernel_sentence,
    list_code, pair, refutes, unpair,
)


def evaluate(s, f, size, relation, env):
    """Independent, straightforward finite semantics; equality is identity."""
    op, x, y = s.nodes[f]
    if op == BOT: return False
    if op == MEM: return (env[x], env[y]) in relation
    if op == EQ: return env[x] == env[y]
    if op == IMP:
        return not evaluate(s, x, size, relation, env) or evaluate(s, y, size, relation, env)
    return all(evaluate(s, y, size, relation, env | {x: a}) for a in range(size))


def relations(size):
    pairs = list(product(range(size), repeat=2))
    for mask in range(1 << len(pairs)):
        yield {p for k, p in enumerate(pairs) if mask & (1 << k)}


def ins(rule, index=0, parameter=0):
    return instruction(rule, index, parameter)


# Hand-written proof: three existential witnesses, two conjunctions, a negation.
CONGRUENCE_CERT = [
    ins(T_IMP), ins(F_ALL), ins(F_IMP),
    ins(T_IMP), ins(F_ALL, 1), ins(F_IMP, 1),
    ins(T_IMP, 1), ins(F_ALL, 2), ins(F_IMP, 2),
    ins(T_IMP, 2), ins(F_IMP, 3), ins(F_IMP, 4),
    ins(T_IMP, 4), ins(F_IMP, 5), ins(F_IMP, 6), ins(T_IMP, 6),
] + [ins(CLOSE)] * 7


class ReferenceTests(unittest.TestCase):
    def test_natural_code_roundtrips(self):
        s = Syntax()
        for n in range(5000):
            self.assertEqual(pair(*unpair(n)), n)
            self.assertEqual(list_code(decode_list(n)), n)
            self.assertEqual(s.code(s.decode(n)), n)
            if n:
                self.assertTrue(all(k < n for k in unpair(n - 1)))
        self.assertFalse(check_code(0))
        self.assertFalse(check_code(candidate_code([], [])))
        self.assertFalse(check_code(candidate_code([s.code(s.mem(0, 5))], [])))

    def test_synthetic_logical_roots_and_invalid_instructions(self):
        s = Syntax()
        contradiction = s.neg(s.imp(s.bot, s.bot))
        proof = [ins(T_IMP), ins(F_IMP), ins(CLOSE), ins(CLOSE)]
        self.assertTrue(refutes(s, contradiction, proof))
        for invalid in (proof[:-1], proof + [ins(CLOSE)], [ins(999)],
                        [ins(T_IMP, 99)], [ins(F_IMP)], [ins(T_IMP, parameter=1)]):
            self.assertFalse(refutes(s, contradiction, invalid))
        self.assertFalse(refutes(s, s.imp(s.bot, s.bot), proof))
        self.assertTrue(refutes(s, s.bot, [ins(CLOSE)]))

    def test_equality_congruence_in_both_membership_positions(self):
        for position in (0, 1):
            for real_equality in (True, False):
                s = Syntax()
                eq = s.eq(0, 1) if real_equality else s.eq(0, 0)
                p, q = ((s.mem(0, 2), s.mem(1, 2)) if position == 0
                        else (s.mem(2, 0), s.mem(2, 1)))
                f = s.ex(0, s.ex(1, s.ex(2, s.conj(eq, s.conj(p, s.neg(q))))))
                self.assertEqual(refutes(s, f, CONGRUENCE_CERT), real_equality)
                has_model = any(evaluate(s, f, 2, rel, {}) for rel in relations(2))
                self.assertEqual(has_model, not real_equality)
        s = Syntax()
        env = {0: 0, 1: 1, 2: 2}
        b = Branch([(True, s.eq(1, 0), env), (True, s.eq(1, 2), env),
                    (False, s.eq(0, 2), env)], 3)
        self.assertTrue(clash(s, b))

    def test_gamma_retention_and_dynamic_parameter_allocation(self):
        s = Syntax()
        f = s.conj(s.all(0, s.mem(0, 0)), s.ex(0, s.neg(s.mem(0, 0))))
        proof = [ins(T_IMP), ins(F_IMP), ins(F_IMP, 1), ins(T_ALL, 0, 0),
                 ins(T_IMP, 1), ins(F_ALL, 3), ins(F_IMP, 3), ins(T_IMP, 3),
                 ins(T_ALL, 0, 1)] + [ins(CLOSE)] * 4
        self.assertTrue(refutes(s, f, proof))
        self.assertFalse(refutes(s, s.all(0, s.bot), [ins(T_ALL, 0, 1), ins(CLOSE)]))
        # This sentence has a two-element model. Reusing parameter 0 as the
        # existential witness would produce a bogus equality contradiction.
        g = s.all(0, s.ex(1, s.neg(s.eq(0, 1))))
        attempt = [ins(T_ALL), ins(T_IMP, 1), ins(F_ALL, 1), ins(F_IMP, 1),
                   ins(T_IMP, 1)] + [ins(CLOSE)] * 3
        self.assertTrue(evaluate(s, g, 2, set(), {}))
        self.assertFalse(refutes(s, g, attempt))

    def test_deep_checker_does_not_use_python_recursion(self):
        s = Syntax()
        f = s.neg(s.eq(0, 0))
        depth = 3000
        for _ in range(depth):
            f = s.all(0, f)
        proof = [ins(T_ALL, i) for i in range(depth)]
        proof += [ins(T_IMP, depth), ins(CLOSE), ins(CLOSE)]
        self.assertTrue(refutes(s, f, proof))

    def test_scope_and_literal_matrix_multiplicity(self):
        s = Syntax()
        phi = s.all(5, s.mem(0, 5))
        self.assertEqual(s.free[phi], {0})
        for w in (0, 1):
            self.assertFalse(evaluate(s, phi, 2, {(0, 0)}, {0: 0, 5: w}))
        f = kernel_sentence(s, [phi])
        self.assertEqual(s.free[f], set())
        self.assertEqual(s.free[kernel_sentence(s, [phi], True)], set())
        count_phi, todo = 0, [f]
        while todo:
            j = todo.pop()
            if j == phi:
                count_phi += 1
                continue
            op, x, y = s.nodes[j]
            if op == IMP: todo.extend((x, y))
            elif op == ALL: todo.append(y)
        self.assertEqual(count_phi, 4)
        with self.assertRaises(InvalidMatrix):
            kernel_sentence(s, [s.mem(0, 5)])
        # Sparse arbitrary variable labels must not allocate 2**label bits.
        huge = 10**100
        closed = s.all(huge, s.eq(huge, huge))
        self.assertEqual(s.free[closed], set())

    def test_finite_structure_template_equivalences(self):
        s = Syntax()
        matrices = [s.eq(2, 0), s.mem(2, 1),
                    s.imp(s.mem(0, 2), s.eq(2, 1)),
                    s.all(5, s.mem(0, 5)), s.all(0, s.eq(0, 1))]
        comparisons = 0
        for phi in matrices:
            ss_plus, red_curried = kernel_components(s, phi)
            inhabited = s.ex(2, s.mem(2, 5))
            original_ss = s.imp(s.mem(3, 5), s.ex(4, s.conj(s.mem(4, 5),
                s.all(2, s.iff(s.mem(2, 4), s.conj(s.mem(2, 3), phi))))))
            original_red = s.imp(s.conj(s.mem(0, 5), s.mem(1, 5)),
                s.imp(s.ex(2, phi), s.ex(2, s.conj(s.mem(2, 5), phi))))
            for size in (1, 2):
                for relation in relations(size):
                    for a, b, x, w in product(range(size), repeat=4):
                        env = {0: a, 1: b, 3: x, 5: w}
                        truth = lambda f: evaluate(s, f, size, relation, env)
                        self.assertEqual(truth(ss_plus), truth(s.conj(inhabited, original_ss)))
                        self.assertEqual(truth(s.all(2, red_curried)), truth(original_red))
                        comparisons += 2
        self.assertEqual(comparisons, 2580)


if __name__ == "__main__":
    unittest.main()
