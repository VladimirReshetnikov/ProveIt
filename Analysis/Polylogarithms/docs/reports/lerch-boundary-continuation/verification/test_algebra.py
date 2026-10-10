#!/usr/bin/env python3
"""Standard-library regression tests for exact algebra and saved certificates.

These test implementations; all infinite-series and zero-count claims still
require the analytic proofs in article.tex. No floating-point arithmetic is used.
"""
from __future__ import annotations
from fractions import Fraction as Q
from pathlib import Path
from math import factorial
import json
import unittest
from certify import I, outward, elementary, polynomial, logq, bernoulli

ROOT = Path(__file__).resolve().parent.parent

def add(a, b):
    out = [Q(0)] * max(len(a), len(b))
    for i, x in enumerate(a): out[i] += x
    for i, x in enumerate(b): out[i] += x
    return out

def scale(a, c): return [c*x for x in a]
def derivative(a): return [i*a[i] for i in range(1,len(a))] or [Q(0)]
def multiply(a,b):
    out=[Q(0)]*(len(a)+len(b)-1)
    for i,x in enumerate(a):
        for j,y in enumerate(b):out[i+j]+=x*y
    return out

def read_interval(v):
    return I(Q(v['lower_rational']),Q(v['upper_rational']))

class ExactTests(unittest.TestCase):
    def test_interval_operations(self):
        a=I(Q(-2),Q(3)); b=I(Q(-4),Q(-1))
        self.assertEqual(a*b,I(Q(-12),Q(8)))
        self.assertEqual(a**2,I(Q(0),Q(9)))
        self.assertEqual(a**3,I(Q(-8),Q(27)))
        self.assertEqual(b/2,I(Q(-2),Q(-1,2)))
        with self.assertRaises(ZeroDivisionError): _=a/I(Q(-1),Q(1))
        with self.assertRaises(ValueError): _=I(Q(2),Q(1))
        for v in (I(Q(-1,3),Q(7,11)),I(Q(1,7),Q(1,7))):
            w=outward(v)
            self.assertLessEqual(w.lo,v.lo)
            self.assertGreaterEqual(w.hi,v.hi)

    def test_logarithms(self):
        self.assertEqual(logq(Q(1)),I.point(0))
        L=logq(Q(2))
        self.assertGreater(L.lo,Q('0.69314718055994530941'))
        self.assertLess(L.hi,Q('0.69314718055994530942'))
        inv=logq(Q(1,2))
        self.assertLessEqual(inv.lo,-L.hi)
        self.assertGreaterEqual(inv.hi,-L.lo)
        with self.assertRaises(ValueError): logq(Q(0))
        with self.assertRaises(ValueError): logq(Q(-1))

    def test_bernoulli_values(self):
        expected={0:Q(1),1:Q(-1,2),2:Q(1,6),4:Q(-1,30),6:Q(1,42),8:Q(-1,30),10:Q(5,66)}
        for n,x in expected.items():self.assertEqual(bernoulli(n),x)
        for n in range(3,20,2):self.assertEqual(bernoulli(n),0)

    def test_kernel_derivative_recurrence(self):
        # ((k+1) B_{n,k} + B'_{n,k}) = (k+1) B_{n,k+1}.
        for n in range(17):
            for k in range(17):
                b=polynomial(n,k)
                lhs=add(scale(b,k+1),derivative(b))
                rhs=scale(polynomial(n,k+1),k+1)
                self.assertEqual(lhs,rhs,(n,k))

    def test_finite_deformation_jets(self):
        count=0
        for k in range(1,13):
            for r in range(k):
                q=[Q(1)]
                for d in range(k-r+1,k+1):q=multiply(q,[Q(d),Q(1)])
                for n in range(13):
                    rhs=[Q(0)]*(n+1)
                    for j in range(min(n,r)+1):
                        c=Q(factorial(n),factorial(n-j))*q[j]*factorial(k-r)
                        rhs=add(rhs,scale(polynomial(n-j,k-r),c))
                    self.assertEqual(rhs,scale(polynomial(n,k),factorial(k)),(n,k,r))
                    count+=1
        self.assertEqual(count,1014)

    def test_elementary_and_weak_coefficients(self):
        for n in range(2,17):
            self.assertEqual(polynomial(n,1),tuple([Q(0)]*(n-1)+[Q(n),Q(1)]))
            for k in range(1,n):
                b=polynomial(n,k);r=n-k
                self.assertTrue(all(x==0 for x in b[:r]))
                self.assertEqual(b[r],Q(factorial(n),factorial(r)*factorial(k)))
        for k in range(17):
            self.assertEqual(elementary(k)[0],Q(1))
            self.assertEqual(elementary(k)[-1],Q(1,factorial(k)))

    def test_saved_endpoint_certificates(self):
        rows=json.loads((ROOT/'data/endpoint_sign_certificates.json').read_text())['certificates']
        self.assertEqual(len(rows),14)
        for row in rows:
            a=Q(row['a']);F=read_interval(row['F']);V=read_interval(row['normalized_V'])
            self.assertNotEqual(F.sign,0)
            self.assertEqual(F.sign,row['F']['sign'])
            self.assertLessEqual(V.lo,a*a*F.lo)
            self.assertGreaterEqual(V.hi,a*a*F.hi)
            self.assertGreater(Q(row['remainder_bound']),0)

    def test_saved_weak_certificates(self):
        rows=json.loads((ROOT/'data/weak_deformation_certificates.json').read_text())['certificates']
        self.assertEqual(len(rows),120)
        seen=set()
        for row in rows:
            n,k,r=row['n'],row['k'],row['r'];C=read_interval(row['C'])
            self.assertNotEqual(C.sign,0)
            self.assertEqual(r,n-k)
            self.assertNotIn((n,k),seen);seen.add((n,k))
            count=k+(1 if r%2 else (2 if C.sign<0 else 0))
            self.assertEqual(row['eventual_small_rho_real_zero_count'],count)
            self.assertLessEqual(count,n)

    def test_saved_minimum_certificate(self):
        data=json.loads((ROOT/'data/minimum_location_certificate.json').read_text())
        self.assertEqual(data['minimum_rho_open_interval'],['0.91560506','0.91560508'])
        for row,sgn in zip(data['certificates'],[-1,1]):
            self.assertEqual(read_interval(row['F_at_lower_a']).sign,1)
            self.assertEqual(read_interval(row['F_at_upper_a']).sign,-1)
            self.assertEqual(read_interval(row['F_rho_on_a_bracket']).sign,sgn)

if __name__=='__main__':unittest.main(verbosity=2)
