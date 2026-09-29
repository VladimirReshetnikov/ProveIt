#!/usr/bin/env python3
"""Independent low-order regression checks, including the finite-prefix formulas.

These test exact algebra, not the analytic remainder theorem. Run without -O,
which would disable Python assertions.
"""
from __future__ import annotations
import unittest
import sympy as sp
from coefficients import compute

x, e, A, B, C, alpha = sp.symbols('x epsilon A B C alpha')

def eg(expr: sp.Expr) -> sp.Expr:
    """Exact Gaussian polynomial expectation, independently of coefficients.py."""
    result = sp.S.Zero
    for (n,), coeff in sp.Poly(sp.expand(expr), x).terms():
        if n % 2 == 0:
            result += coeff * sp.factorial2(n - 1) if n else coeff
    return sp.expand(result)

class ExactTests(unittest.TestCase):
    def test_minimal_supported_order(self):
        result = compute(2)
        self.assertEqual(result['kl'], {'2': '3/100'})
        with self.assertRaises(ValueError):
            compute(1)
        with self.assertRaises(ValueError):
            compute(15)

    def test_hermite_moments(self):
        H = lambda n: sp.hermite_prob(n, x)
        self.assertEqual(eg(H(4)**3), 1728)
        self.assertEqual(eg(H(4)**2*H(6)), 11520)
        self.assertEqual(eg(H(4)**2*H(8)), 40320)
        self.assertEqual(eg(H(4)**4), 368064)
        self.assertEqual(sp.expand(H(4)**2-H(8)-16*H(6)-72*H(4)-96*H(2)-24), 0)

    def test_finite_prefix_through_four(self):
        # Construct the low-weight density expansion directly in cumulants;
        # this does not use the recurrence implemented in coefficients.py.
        q = 1-e
        lam = {}
        for r, tau in [(2,A),(3,B),(4,C)]:
            c = sp.Rational(3**r * 2**(2*r),2*r)*sp.bernoulli(2*r)
            rat = c*(1-q*q)**(r-1)/sum(q**(2*j) for j in range(r))
            lam[2*r] = tau*sp.series(rat,e,0,4).removeO()
        a, b, c = lam[4]/24, lam[6]/720, lam[8]/40320
        H = lambda n: sp.hermite_prob(n,x)
        u = sp.expand(a*H(4)+b*H(6)+(c+a*a/2)*H(8)+a*b*H(10)+a**3*H(12)/6)
        poly = sp.Poly(u,e)
        P1, P2, P3 = (poly.nth(j) for j in [1,2,3])
        d2=eg(P1**2)/2
        d3=eg(P1*P2)-eg(P1**3)/6
        d4=eg(P1*P3)+eg(P2**2)/2-eg(P1**2*P2)/2+eg(P1**4)/12
        expected4=(sp.Rational(3,400)*A**2+sp.Rational(27,500)*A**3
                   +sp.Rational(128,2205)*B**2-sp.Rational(32,175)*A**2*B
                   +sp.Rational(801,5000)*A**4)
        self.assertEqual(sp.expand(d2-sp.Rational(3,100)*A**2),0)
        self.assertEqual(sp.expand(d3-sp.Rational(3,100)*A**2-sp.Rational(9,250)*A**3),0)
        self.assertEqual(sp.expand(d4-expected4),0)
        self.assertEqual(d4.subs({A:1,B:1,C:1}),sp.Rational(427297,4410000))
        # Direct binomial/log coefficient check for Renyi order alpha.
        r2=sp.cancel(alpha*(alpha-1)/2*eg(P1**2)/(alpha-1))
        r3=sp.cancel((alpha*(alpha-1)*eg(P1*P2)
                 +alpha*(alpha-1)*(alpha-2)*eg(P1**3)/6)/(alpha-1))
        expected3=sp.Rational(3,100)*alpha*A**2+sp.Rational(9,250)*alpha*(2-alpha)*A**3
        self.assertEqual(sp.expand(r2-sp.Rational(3,100)*alpha*A**2),0)
        self.assertEqual(sp.expand(r3-expected3),0)

    def test_quartic_renyi_specialization(self):
        result=compute(4)
        d4=sp.sympify(result['renyi']['4'],locals={'alpha':alpha})
        expected=sp.Rational(477,5000)*alpha**3-sp.Rational(10043,35000)*alpha**2+sp.Rational(1272001,4410000)*alpha
        self.assertEqual(sp.expand(d4-expected),0)

if __name__=='__main__':
    unittest.main(verbosity=2)
