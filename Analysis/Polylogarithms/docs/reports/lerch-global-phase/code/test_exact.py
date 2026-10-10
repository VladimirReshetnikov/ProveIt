#!/usr/bin/env python3
"""Regression tests for the exact certificate engine (standard library only)."""
from fractions import Fraction as Q
from math import factorial
import random
import unittest
import verify_exact as v

class IntervalTests(unittest.TestCase):
    def test_arithmetic_against_exact_rationals(self):
        rng=random.Random(20261009)
        for _ in range(1000):
            a,b=sorted(Q(rng.randint(-100,100),rng.randint(1,37)) for _ in range(2))
            c,d=sorted(Q(rng.randint(-100,100),rng.randint(1,37)) for _ in range(2))
            X,Y=v.I.bounds(a,b),v.I.bounds(c,d)
            Z=X+Y
            self.assertLessEqual(Q(Z.lo,v.SCALE),a+c)
            self.assertGreaterEqual(Q(Z.hi,v.SCALE),b+d)
            Z=X*Y; ps=[a*c,a*d,b*c,b*d]
            self.assertLessEqual(Q(Z.lo,v.SCALE),min(ps))
            self.assertGreaterEqual(Q(Z.hi,v.SCALE),max(ps))
            if a>0 or b<0:
                Z=X.reciprocal()
                self.assertLessEqual(Q(Z.lo,v.SCALE),1/b)
                self.assertGreaterEqual(Q(Z.hi,v.SCALE),1/a)
    def test_zero_division_guard(self):
        with self.assertRaises(ZeroDivisionError):v.I.bounds(Q(-1),Q(1)).reciprocal()
        with self.assertRaises(ValueError):v.log_q(Q(0))
    def test_logarithm_inversion(self):
        for q in [Q(1),Q(2),Q(3,7),Q(65,8),Q(193,27)]:
            Z=v.log_q(q)+v.log_q(1/q)
            self.assertLessEqual(Z.lo,0);self.assertGreaterEqual(Z.hi,0)
    def test_logarithm_special_values(self):
        Z=v.log_q(Q(1));self.assertLessEqual(Z.lo,0);self.assertGreaterEqual(Z.hi,0)
        self.assertGreater(v.log_q(Q(2)).lo,0)
        self.assertLess(v.log_q(Q(1,2)).hi,0)
    def test_bernoulli(self):
        known={0:Q(1),1:Q(-1,2),2:Q(1,6),4:Q(-1,30),6:Q(1,42),
               8:Q(-1,30),10:Q(5,66),12:Q(-691,2730)}
        for n,x in known.items():self.assertEqual(v.bernoulli(n),x)
    def test_derivatives_by_independent_power_series(self):
        degree=10
        def mul(a,b):return [sum(a[j]*b[k-j] for j in range(k+1)) for k in range(degree+1)]
        log=[Q(0)]+[Q((-1)**(k+1),k) for k in range(1,degree+1)]
        log2=mul(log,log);log3=mul(log2,log)
        h=[3*a-b for a,b in zip(log2,log3)]
        inv2=[Q((-1)**k*(k+1)) for k in range(degree+1)]
        coeff=mul(h,inv2)
        P=v.P0[:]
        for k in range(degree+1):
            self.assertEqual(P[0],factorial(k)*coeff[k])
            P=v.poly_derivative_step(P,k+2)
    def test_sharp_barrier_second_derivative_polynomial(self):
        # Exact endpoint values of the quadratic used to prove strict convexity.
        for n in range(2,101):
            q=lambda t:-t*t+(n+4)*t-2*n-2
            self.assertEqual(q(Q(n+1,2)),Q(n*n-1,4))
            self.assertEqual(q(Q(n)),2*(n-1))
            self.assertGreater(q(Q(n+1,2)),0)
    def test_anchor_sign_regression(self):
        for a,sgn in [(Q(4,5),1),(Q(1),-1),(Q(3,2),1),(Q(9,5),1)]:
            x,_=v.em_anchor(a,N=40,p=5) # different truncation from main certificate
            self.assertTrue(x.positive() if sgn>0 else x.negative())

if __name__=='__main__':unittest.main(verbosity=2)
