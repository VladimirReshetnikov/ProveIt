#!/usr/bin/env python3
"""Small exhaustive and exact regression tests for the delivered kernels."""
from itertools import product
from fractions import Fraction as Q
from math import comb, factorial
import unittest
from word_algebra import *
from certified_euler import euler,Interval,harmonic_values
import verify_s4_independent as other

class WordTests(unittest.TestCase):
    def test_shuffle_implementations(self):
        words=[w for n in range(1,4) for w in product((-1,0,1),repeat=n)]
        for u in words:
            for v in words:
                if len(u)+len(v)>5:continue
                self.assertEqual(shuffle(u,v),dict(other.sh(u,v)))
                self.assertEqual(sum(shuffle(u,v).values()),comb(len(u)+len(v),len(u)))
    def test_roundtrip(self):
        for n in range(1,5):
            for w in product(range(-1,4),repeat=n):
                if w[-1]!=-1:self.assertEqual(to_word(to_indices(w)),w)
    def test_stuffle_implementations(self):
        for n in range(1,4):
            for w in product(range(-1,4),repeat=n):
                if not admissible(w):continue
                for v in [(0,),(1,),(2,),(-1,0),(-1,1),(1,2)]:
                    p={to_word(s):c for s,c in stuffle(to_indices(w),to_indices(v)).items()}
                    self.assertEqual(p,dict(other.stuffleword(w,v)))
    def test_cayley_involution(self):
        for n in range(1,5):
            for w in product(range(-1,4),repeat=n):
                if not admissible(w):continue
                d=cayley(w);dd={}
                for v,c in d.items():dd=plus(dd,cayley(v),c)
                self.assertEqual(dd,{w:1})
                self.assertEqual(d,dict(other.D(w)))
    def test_target(self):
        self.assertEqual(target(),dict(other.build_target()))
        self.assertEqual(len(odd_projection(target())),24)
        self.assertEqual(plus(target(),{conjugate(w):c for w,c in target().items()}),{})
    def test_known_shuffle(self):
        # Li_1(z)*Li_4(z) = 2F41+F32+F23+F14.
        self.assertEqual(shuffle((1,),(-1,-1,-1,1)),
                         {(-1,-1,-1,1,1):2,(-1,-1,1,-1,1):1,
                          (-1,1,-1,-1,1):1,(1,-1,-1,-1,1):1})

class EulerTests(unittest.TestCase):
    def test_point_masses(self):
        for t in [Q(0),Q(1,3),Q(1,2),Q(1)]:
            for N in range(1,16):
                J=euler((t**k for k in range(N)),N,Q(1))
                self.assertLessEqual(J.lo,1/(1+t));self.assertGreaterEqual(J.hi,1/(1+t))
    def test_difference_table_equivalence(self):
        for N in range(1,20):
            vals=list(harmonic_values(N,3,2,2,2));diff=vals[:];E=Q(0)
            for j in range(N):
                E+=diff[0]/2**(j+1)
                diff=[diff[k]-diff[k+1] for k in range(len(diff)-1)]
            J=euler(vals,N,Q(10,3))
            self.assertEqual((J.lo+J.hi)/2,E)
    def test_interval_products(self):
        J=Interval(Q(-2),Q(3));K=Interval(Q(-4),Q(-1))
        self.assertEqual(J*K,Interval(Q(-12),Q(8)))
        self.assertTrue((J**2).lo<=0<=(J**2).hi)

if __name__=='__main__':unittest.main(verbosity=2)
