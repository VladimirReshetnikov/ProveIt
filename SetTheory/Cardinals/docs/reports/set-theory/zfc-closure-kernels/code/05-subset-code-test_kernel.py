from __future__ import annotations
import random
import unittest
from kernel import *
from codec import encode, decode, index, decode_index


def identity(a: F) -> list:
    A = dump_formula(a); AA = dump_formula(Imp(a, a))
    return [[0, A, AA], [0, A, A], [1, A, AA, A], [5, 0, 2], [5, 1, 3]]

class KernelTests(unittest.TestCase):
    def test_identity(self):
        a = M(0, 0); p = identity(a)
        self.assertTrue(check(p).valid); self.assertFalse(check(p).refutation)
        self.assertTrue(same(derive(p)[-1], Imp(a, a)))
    def test_bottom_identity_is_not_bottom(self):
        self.assertFalse(check(identity(Bot())).refutation)
    def test_empty_rejected(self): self.assertFalse(check([]).valid)
    def test_unchecked_bottom_rejected(self): self.assertFalse(check([[99, [0]]]).valid)
    def test_forward_reference(self): self.assertFalse(check([[5, 0, 0]]).valid)
    def test_mp_mismatch(self): self.assertFalse(check([[0, [0], [0]], [5, 0, 0]]).valid)
    def test_negative_variable(self): self.assertFalse(check([[3, -1, 0, [0]]]).valid)
    def test_boolean_variable(self): self.assertFalse(check([[3, True, 0, [0]]]).valid)
    def test_boolean_tag(self): self.assertFalse(check([[True, [0], [0]]]).valid)
    def test_bad_arity(self): self.assertFalse(check([[7, 123]]).valid)
    def test_equality_rejected(self): self.assertFalse(check([[8, [4, 0, 1]]]).valid)
    def test_q2_side_condition(self): self.assertFalse(check([[4, 0, [1, 0, 1], [0]]]).valid)
    def test_q2_valid(self): self.assertTrue(check([[4, 0, [1, 1, 1], [1, 0, 0]]]).valid)
    def test_gen(self):
        p = identity(M(0, 1)); p.append([6, 0, 4]); self.assertTrue(check(p).valid)
    def test_congruence(self):
        p = [[7]]; self.assertTrue(check(p).valid); self.assertEqual(fv(derive(p)[0]), set())
    def test_schema_with_parameters(self):
        a = Imp(M(0, 2), All(1, M(1, 0)))
        p = [[8, dump_formula(a)]]
        self.assertTrue(check(p).valid); self.assertFalse(check(p).refutation)
        self.assertEqual(fv(derive(p)[0]), set())
    def test_capture_avoidance(self):
        a = All(1, M(0, 1)); result = subst(a, 0, 1)
        self.assertTrue(same(result, All(2, M(1, 2))))
        self.assertEqual(fv(result), {1})
    def test_nested_shadowing(self):
        a = All(1, Imp(M(0, 1), All(1, M(0, 1))))
        b = subst(a, 0, 1)
        self.assertTrue(same(b, All(2, Imp(M(1, 2), All(3, M(1, 3))))))
    def test_bound_slot_unchanged(self):
        a = All(0, M(0, 1)); self.assertEqual(subst(a, 0, 4), a)
    def test_alpha(self):
        self.assertTrue(same(All(1, M(1, 0)), All(2, M(2, 0))))
        self.assertFalse(same(All(1, M(1, 0)), All(0, M(0, 0))))
    def test_dump_roundtrip(self):
        a = closure(Imp(M(0, 2), All(1, M(1, 0))))
        self.assertEqual(parse_formula(dump_formula(a)), a)
    def test_codec_roundtrip(self):
        rng = random.Random(20261016)
        def tree(d):
            return rng.randrange(10) if d == 0 or rng.randrange(2) else [tree(d-1) for _ in range(rng.randrange(5))]
        for _ in range(1000):
            t = tree(4); self.assertEqual(decode(encode(t)), t); self.assertEqual(decode_index(index(t)), t)
    def test_codec_malformed(self):
        for bits in ('', '0', '1', '000', '101', '2', '011'):
            with self.assertRaises(ValueError): decode(bits)
    def test_codec_no_boolean(self):
        with self.assertRaises(ValueError): encode([True])
    def test_codec_deep(self):
        # The wire parser itself is iterative.
        t = 0
        for _ in range(3000): t = [t]
        decoded = decode(encode(t))
        for _ in range(3000): decoded = decoded[0]
        self.assertEqual(decoded, 0)
    def test_enumeration_on_examples(self):
        p = identity(M(0, 0))
        self.assertTrue(check(decode_index(index(p))).valid)
    def test_substitution_semantics(self):
        rng = random.Random(99)
        def f(d):
            if not d: return M(rng.randrange(4), rng.randrange(4))
            k = rng.randrange(4)
            return Bot() if k == 0 else M(rng.randrange(4), rng.randrange(4)) if k == 1 else Imp(f(d-1), f(d-1)) if k == 2 else All(rng.randrange(4), f(d-1))
        for _ in range(1200):
            a = f(4); x, y = rng.randrange(4), rng.randrange(4)
            member = [rng.randrange(8) for _ in range(3)]
            env = {i: rng.randrange(3) for i in range(4)}
            self.assertEqual(evaluate(subst(a, x, y), member, env), evaluate(a, member, env | {x: env[y]}))
    def test_logical_axiom_semantics(self):
        rng = random.Random(101)
        for _ in range(300):
            a, b, c = [M(rng.randrange(3), rng.randrange(3)) for _ in range(3)]
            rows = [[0,dump_formula(a),dump_formula(b)], [1,dump_formula(a),dump_formula(b),dump_formula(c)],
                    [2,dump_formula(a),dump_formula(b)], [3,0,1,dump_formula(All(1, a))]]
            member = [rng.randrange(8) for _ in range(3)]
            for ax in derive(rows):
                for n in range(27):
                    env = {0:n%3,1:(n//3)%3,2:n//9}
                    self.assertTrue(evaluate(ax,member,env))

if __name__ == '__main__': unittest.main(verbosity=2)
