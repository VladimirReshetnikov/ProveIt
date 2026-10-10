#!/usr/bin/env python3
"""Regression tests of the integer interval primitives; no floating point."""
from fractions import Fraction as F
from random import Random
import unittest
from certified import Context, Real, Evaluator, shifted_chebyshev


class IntervalTests(unittest.TestCase):
    def setUp(self):
        self.c = Context(50)

    def contains(self, interval, value):
        self.assertLessEqual(F(interval.lo, self.c.scale), value)
        self.assertLessEqual(value, F(interval.hi, self.c.scale))

    def test_rational_embedding(self):
        for n in range(-40,41):
            for d in (1,3,7,19):
                self.contains(self.c.real(F(n,d)), F(n,d))

    def test_arithmetic_on_rationals(self):
        rng = Random(1987)
        for _ in range(300):
            a = F(rng.randint(-1000,1000), rng.randint(1,100))
            b = F(rng.randint(-1000,1000), rng.randint(1,100))
            aa, bb = self.c.real(a), self.c.real(b)
            self.contains(aa+bb, a+b)
            self.contains(aa-bb, a-b)
            self.contains(aa*bb, a*b)
            if b:
                self.contains(aa/bb, a/b)
            self.contains(aa**4, a**4)

    def test_interval_product(self):
        q = self.c.scale
        for a,b in [(-3,2),(-5,-2),(1,4),(0,0)]:
            for c,d in [(-7,-2),(-1,5),(2,3)]:
                aa,bb = Real(self.c,a*q,b*q),Real(self.c,c*q,d*q)
                cc = aa*bb
                for v in (a*c,a*d,b*c,b*d):
                    self.contains(cc,F(v))

    def test_reciprocal(self):
        q=self.c.scale
        for a,b in [(-7,-2),(2,11)]:
            inv=Real(self.c,a*q,b*q).reciprocal()
            self.contains(inv,F(1,a));self.contains(inv,F(1,b))
        with self.assertRaises(ZeroDivisionError):
            Real(self.c,-q,q).reciprocal()

    def test_square(self):
        q=self.c.scale
        sq=Real(self.c,-3*q,2*q).square()
        self.contains(sq,F(0));self.contains(sq,F(9))
        self.assertEqual(sq.lo,0)

    def test_square_root(self):
        for n in range(101):
            value=F(n,7);out=self.c.real(value).sqrt()
            self.assertLessEqual(F(out.lo,self.c.scale)**2,value)
            self.assertLessEqual(value,F(out.hi,self.c.scale)**2)
        with self.assertRaises(ValueError):
            self.c.real(-1).sqrt()

    def test_complex_reciprocal(self):
        for a,b in [(F(1,3),F(2,7)),(F(-5),F(4)),(F(0),F(-3))]:
            z=self.c.complex(a,b).reciprocal();den=a*a+b*b
            self.contains(z.re,a/den);self.contains(z.im,-b/den)

    def test_unsupported_domain(self):
        ev=Evaluator(5,4)
        with self.assertRaises(ValueError):
            ev.double(1,1,4,0,1)
        with self.assertRaises(ValueError):
            ev.root(5,1)
        with self.assertRaises(ValueError):
            self.c.real(1)+Context(30).real(1)

    def test_chebyshev_initial_conditions(self):
        self.assertEqual(shifted_chebyshev(0),(1,))
        self.assertEqual(shifted_chebyshev(1),(-1,2))
        self.assertEqual(shifted_chebyshev(2),(1,-8,8))
        self.assertEqual(shifted_chebyshev(3),(-1,18,-48,32))


if __name__ == '__main__':
    unittest.main(verbosity=2)
