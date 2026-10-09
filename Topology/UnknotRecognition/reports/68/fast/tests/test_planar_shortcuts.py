"""Typed shortcut checks against the unchanged compiled-cobordism evaluator."""
import itertools
import random
import unittest

from fastunknot.planar import Planar, evaluate
from test_acceleration import matchings


def compiled_product(algebra, a, b, c, f, g):
    plan = algebra.compose_plan(a, b, c)
    if plan is None:
        return 0
    answer = 0
    for i in range(f.bit_length()):
        if f >> i & 1:
            for j in range(g.bit_length()):
                if g >> j & 1:
                    answer ^= evaluate(plan[0], i, j)
    return answer


class PlanarShortcutTests(unittest.TestCase):
    def test_all_three_arc_scalars_and_typed_identities(self):
        algebra = Planar()
        ids = [algebra.intern(tuple(sorted(tuple(sorted(arc)) for arc in matching)))
               for matching in matchings(list(range(6)))]
        for a in ids:
            for f in range(256):
                self.assertEqual(algebra.compose(a, a, a, f, f),
                                 compiled_product(algebra, a, a, a, f, f))
            for b in ids:
                _, circles = algebra.basis(a, b)
                for f in range(1 << (1 << circles)):
                    for x, y, z, left, right in ((a, a, b, 1, f), (a, b, b, f, 1),
                                                (a, b, a, 0, f), (a, b, a, f, 0)):
                        self.assertEqual(algebra.compose(x, y, z, left, right),
                                         compiled_product(algebra, x, y, z, left, right))

    def test_equal_coefficients_in_different_types_use_full_composition(self):
        algebra = Planar()
        ids = [algebra.intern(tuple(sorted(tuple(sorted(arc)) for arc in matching)))
               for matching in matchings(list(range(6)))]
        counterexamples = 0
        for a, b, c in itertools.product(ids, repeat=3):
            left = algebra.basis(a, b)[1]
            right = algebra.basis(b, c)[1]
            for f in range(1 << (1 << min(left, right))):
                expected = compiled_product(algebra, a, b, c, f, f)
                self.assertEqual(algebra.compose(a, b, c, f, f), expected)
                counterexamples += expected != (f & 1)
        self.assertGreater(counterexamples, 0)

    def test_random_general_compositions_still_agree(self):
        rng = random.Random(2026100714)
        algebra = Planar()
        ids = [algebra.intern(tuple(sorted(tuple(sorted(arc)) for arc in matching)))
               for matching in matchings(list(range(8)))]
        for _ in range(1000):
            a, b, c = (rng.choice(ids) for _ in range(3))
            f = rng.getrandbits(1 << algebra.basis(a, b)[1])
            g = rng.getrandbits(1 << algebra.basis(b, c)[1])
            self.assertEqual(algebra.compose(a, b, c, f, g),
                             compiled_product(algebra, a, b, c, f, g))


if __name__ == "__main__":
    unittest.main()
