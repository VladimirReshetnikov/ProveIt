"""Regressions for symbolic coefficient branching and nested quantifiers."""
from itertools import product
import unittest

import sympy as sp
from quantifier_elimination import qe

a, b, c, x, y = sp.symbols('a b c x y', real=True)


class QuantifierEliminationTests(unittest.TestCase):
    def test_quadratic_degree_drops_and_discriminant(self):
        formula = qe([('exists', x)], sp.Eq(a*x**2+b*x+c, 0))
        for aa, bb, cc in product(range(-2, 3), repeat=3):
            expected = (bb**2 >= 4*aa*cc if aa else bb != 0 or cc == 0)
            self.assertEqual(bool(formula.subs({a: aa, b: bb, c: cc})), expected)

    def test_circle_projection(self):
        formula = qe([('exists', y)], sp.Eq(x**2+y**2, 1))
        # All sign cells of x-1 and x+1, including both endpoints.
        for v in [-2, -1, 0, 1, 2]:
            self.assertEqual(bool(formula.subs(x, v)), -1 <= v <= 1)

    def test_nested_with_parameter(self):
        formula = qe([('forall', y), ('exists', x)], sp.Eq(x**2, y**2+a))
        self.assertEqual(sp.simplify(formula), a >= 0)

    def test_closed_quantifier_order(self):
        matrix = sp.Eq(y**2, x**2)
        self.assertEqual(qe([('forall', x), ('exists', y)], matrix), sp.true)
        self.assertEqual(qe([('exists', y), ('forall', x)], matrix), sp.false)
        self.assertEqual(qe([('forall', x), ('exists', y)], sp.Eq(y**2, x)), sp.false)

    def test_strict_joint_constraints(self):
        formula = qe([('exists', x)], sp.And(sp.Eq(x**2, a), x > 0))
        self.assertEqual(sp.simplify(formula), a > 0)

    def test_pure_open_cell(self):
        formula = qe([('exists', x)], sp.And(x > 0, x < a))
        self.assertEqual(sp.simplify(formula), a > 0)

    def test_multiple_root_and_nullification(self):
        formula = qe([('exists', x)], sp.And(sp.Eq(a*(x-1)**2, 0), x < 0))
        self.assertEqual(sp.simplify(formula), sp.Eq(a, 0))


if __name__ == '__main__':
    unittest.main(verbosity=2)
