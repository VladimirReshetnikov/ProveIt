import unittest
from fractions import Fraction as F
from itertools import combinations

from sign_cells import (ONE, attainable_signs, multiply, polynomial, sign,
                        signs_at_roots, squarefree, tarski_query)


def factored(roots):
    f = ONE
    for root in roots:
        f = multiply(f, polynomial([-root, 1]))
    return f


def evaluate(f, t):
    value = F(0)
    for c in reversed(f):
        value = value * t + c
    return value


class TestSigns(unittest.TestCase):
    def test_constants_and_empty(self):
        self.assertEqual(attainable_signs([]), {()})
        self.assertEqual(attainable_signs([[0], [-7], [2]]), {(0, -1, 1)})

    def test_tangent_secant_disjoint(self):
        for height, wanted in [(F(3, 5), {-1, 1}), (1, {0}), (2, set())]:
            eq = [height ** 2 - 1, 0, 1]
            signs = attainable_signs([eq, [0, 1]])
            self.assertEqual({s for v, s in signs if v == 0}, wanted)

    def test_irrational_and_cubic_roots(self):
        d = polynomial([-2, 0, 1])
        self.assertEqual(signs_at_roots(d, [polynomial([0, 1])]),
                         {(-1,): 1, (1,): 1})
        signs = attainable_signs([[-2, 0, 0, 1], [0, 1]])
        self.assertIn((0, 1), signs)
        self.assertNotIn((0, -1), signs)

    def test_signed_queries_and_shared_zeros(self):
        roots = [-3, -1, 0, 2, 4]
        d = squarefree(factored(roots + roots[:3]))
        for deg in range(4):
            for choice in combinations(roots, deg):
                w = factored(choice)
                self.assertEqual(tarski_query(d, w),
                                 sum(sign(evaluate(w, x)) for x in roots))

    def test_all_sign_cells_against_independent_rational_samples(self):
        roots = [F(-11, 7), F(0), F(2, 5), F(13, 19)]
        endpoint_samples = roots + [roots[0] - 1, roots[-1] + 1]
        samples = endpoint_samples + [(a + b)/2 for a, b in zip(roots, roots[1:])]
        for left, right in combinations(range(4), 2):
            f = factored([roots[left], roots[left], roots[right]])
            g = factored([r for i, r in enumerate(roots) if i != left])
            expected = {(sign(evaluate(f, t)), sign(evaluate(g, t))) for t in samples}
            self.assertEqual(attainable_signs([f, g]), expected)


if __name__ == "__main__":
    unittest.main()
