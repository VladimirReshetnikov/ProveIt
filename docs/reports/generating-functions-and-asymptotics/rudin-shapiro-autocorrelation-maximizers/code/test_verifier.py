#!/usr/bin/env python3
"""Independent small defining-sum tests and elementary certificate sanity tests."""
import random
import unittest
from fractions import Fraction as Q
import verify as v
from rs_maximum import autocorrelation,maximum

class Tests(unittest.TestCase):
    def test_all_small_defining_sums(self):
        for m in range(1,10):
            signs=[(-1)**bin(j & (j>>1)).count('1') for j in range(1<<m)]
            values=[]
            for k in range(1<<m):
                expected=sum(signs[j]*signs[j+k] for j in range(len(signs)-k))
                self.assertEqual(autocorrelation(m,k),expected)
                self.assertEqual(autocorrelation(m,-k),expected)
                values.append(expected)
            result=maximum(m)
            best=max(abs(x) for x in values[1:])
            self.assertEqual(result.value,best)
            self.assertEqual(result.shifts,tuple(k for k in range(1,len(values))
                                                 if abs(values[k])==best))
    def test_matrix_inverse_and_cayley_hamilton(self):
        self.assertEqual(v.mm(v.U,v.inverse(v.U)),v.ident())
        self.assertEqual(v.det(*v.U),-4)
        u2=v.mpow(v.U,2);u3=v.mpow(v.U,3)
        for i in range(3):
            for j in range(3):
                self.assertEqual(u3[i][j]-u2[i][j]-2*v.U[i][j]+4*int(i==j),0)
    def test_polynomial_determinants_against_scalar_determinants(self):
        rng=random.Random(1729)
        for _ in range(100):
            mats=[tuple(tuple(rng.randrange(-5,6) for _ in range(3))
                        for _ in range(3)) for _ in range(3)]
            x,z=Q(rng.randrange(-20,21),7),Q(rng.randrange(-20,21),11)
            poly=v.pdet(*mats)
            value=sum(c*x**i*z**j for (i,j),c in poly.items())
            direct=v.det(*(v.mv(a,(x,1,z)) for a in mats))
            self.assertEqual(value,direct)
            box=((x-Q(1,100),x+Q(1,100)),(z-Q(1,100),z+Q(1,100)))
            low,high=v.polynomial_bounds(poly,box)
            self.assertLessEqual(low,value);self.assertLessEqual(value,high)
    def test_tetrahedron_acceptance_and_rejection(self):
        a,b,c=(4,0,0),(0,4,0),(0,0,4)
        self.assertTrue(v.tetra_contains((1,1,1),a,b,c))
        self.assertTrue(v.tetra_contains((0,0,0),a,b,c))
        self.assertTrue(v.tetra_contains(a,a,b,c))
        self.assertFalse(v.tetra_contains((2,2,2),a,b,c))
        self.assertFalse(v.tetra_contains((-1,1,1),a,b,c))
    def test_sharp_threshold_and_large_index(self):
        self.assertEqual(maximum(39).shifts,(366503875923,))
        self.assertEqual(autocorrelation(39,366503875925),132094089)
        self.assertEqual(maximum(40).value,255886741)
        for m in (40,41,42,100,402,1000):
            result=maximum(m)
            ell=((1<<(m+1))+(-1)**m)//3
            self.assertEqual(result.shifts,(ell,))
            self.assertEqual(result.correlations,(autocorrelation(m,ell),))
    def test_invalid_input(self):
        for m in (0,-1,False,1.2):
            with self.assertRaises(ValueError):maximum(m)
        with self.assertRaises(ValueError):autocorrelation(10,1.5)

if __name__=='__main__':
    unittest.main(verbosity=2)
