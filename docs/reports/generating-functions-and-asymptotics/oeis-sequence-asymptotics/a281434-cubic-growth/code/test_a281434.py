#!/usr/bin/env python3
"""Exact regression tests. Run: python -m unittest -v test_a281434.py"""
import unittest
from math import comb
from pathlib import Path

from a281434 import (CoefficientOracle, a, a_modular, log_range, lower_bound,
                     next_polynomial, polynomial, terms, upper_bound)

OEIS_A281434 = [
    1,3,12,30,64,113,188,285,415,577,780,1017,1312,1648,2044,2489,3008,
    3583,4236,4953,5760,6638,7611,8664,9822,11069,12426,13880,15455,
    17131,18940,20855,22912,25083,27404,29844,32448,35178,38075,41109,
    44320,47672,51212]
OEIS_A352697 = [
    0,0,1,0,2,0,2,1,2,0,6,0,3,0,6,0,4,0,6,0,5,1,7,2,6,2,7,1,8,0,
    8,0,8,0,11,0,9,1,10,0,11,0,11,0,11,0,14,3,12,0,13,0,13,0,15,0,
    15,0,15,0,16,0,18,0,16,0,17,0,17,0,19,0,18,2,19,0,19,0,20,2]


def multiplicity_at_minus_one(coefficients):
    p=list(coefficients)
    while len(p)>1 and not p[-1]: p.pop()
    answer=0
    while len(p)>1 and sum(c*(-1)**i for i,c in enumerate(p))==0:
        q=[0]*(len(p)-1)
        q[-1]=p[-1]
        for i in range(len(q)-2,-1,-1):q[i]=p[i+1]-q[i+1]
        assert q[0]==p[0]
        p=q
        answer+=1
    return answer


class Tests(unittest.TestCase):
    def test_published_terms(self):
        self.assertEqual(list(terms(42)),OEIS_A281434)

    def test_published_deficits_against_b_file(self):
        path=Path(__file__).resolve().parents[1]/'data'/'b281434.txt'
        values=dict(map(int,line.split()) for line in path.read_text().splitlines())
        self.assertEqual([upper_bound(n)-values[n] for n in range(1,81)],
                         OEIS_A352697)

    def test_independent_coefficient_formula(self):
        oracle=CoefficientOracle()
        p={(0,0,0):1}
        for n in range(1,13):
            p=next_polynomial(p)
            for k in range(1,n+1):
                for j in range(n+1):
                    for ell in log_range(n,k,j):
                        self.assertEqual(oracle.coefficient(n,k,j,ell),
                                         p.get((k,j,ell),0),(n,k,j,ell))

    def test_modular_small_moduli(self):
        values=list(terms(12))
        for modulus in (2,7,12,1_000_000_007):
            for n in range(13):
                self.assertEqual(a_modular(n,modulus),values[n],(n,modulus))

    def test_support_and_multiplicity(self):
        p={(0,0,0):1}
        for n in range(1,13):
            p=next_polynomial(p)
            for (k,j,ell) in p:
                self.assertIn(ell,log_range(n,k,j))
            for k in range(1,n+1):
                for j in range(n+1):
                    rr=log_range(n,k,j)
                    self.assertIn((k,j,rr.stop-1),p)
                    row=[p.get((k,j,ell),0) for ell in range(rr.stop)]
                    self.assertGreaterEqual(multiplicity_at_minus_one(row),
                                             max(n-2*j,k-j,0))
            self.assertLessEqual(lower_bound(n),len(p))
            self.assertLessEqual(len(p),upper_bound(n))

    def test_envelope_and_bound_formulas(self):
        for n in range(1,101):
            envelope=sum(len(log_range(n,k,j)) for k in range(1,n+1)
                         for j in range(n+1))
            lower=sum(1+max(n-2*j,k-j,0) for k in range(1,n+1)
                      for j in range(n+1))
            self.assertEqual(envelope,upper_bound(n))
            self.assertEqual(lower,lower_bound(n))

    def test_leading_coefficient_formula(self):
        oracle=CoefficientOracle()
        for n in range(1,20):
            for j in range(1,n+1):
                d=n-j
                for k in range(1,n+1):
                    ell=log_range(n,k,j).stop-1
                    if k>=d+1:
                        expected=comb(n,d)*oracle.q_poly(j,0)[k-d]
                    else:
                        from math import factorial
                        expected=(-1)**(j-1)*factorial(j-1)*(
                            comb(n,d-1)*oracle.noncentral_stirling(d,k,0)
                            +comb(n,d)*oracle.noncentral_stirling(d+1,k,0))
                    self.assertEqual(oracle.coefficient(n,k,j,ell),expected)
                    self.assertNotEqual(expected,0)

    def test_odd_central_cancellations(self):
        oracle=CoefficientOracle()
        for n in range(3,80,2):
            d=(n-1)//2
            holes=[k for k in range(1,d+2) if (k-d)%2==0]
            self.assertEqual(len(holes),(n+1)//4)
            for k in holes:
                self.assertEqual(oracle.coefficient(n,k,d+1,0),0)

    def test_nonlogarithmic_infinite_family(self):
        oracle=CoefficientOracle()
        for t in range(2,13):
            n=t*t+t-1
            k,j,ell=n-1,t+2,2*t*t-7
            self.assertIn(ell,log_range(n,k,j))
            self.assertEqual(oracle.coefficient(n,k,j,ell),0)
            self.assertNotEqual(oracle.coefficient(n,k,j,ell+1),0)

    def test_validation(self):
        for n in (-1,True,1.5,'5'):
            with self.assertRaises(ValueError):a(n)
        with self.assertRaises(ValueError):a_modular(5,1)

if __name__=='__main__':unittest.main(verbosity=2)
