#!/usr/bin/env python3
"""Regression checks independent of the all-height proof."""
import unittest
from tetration_tools import (Profile, valuation, crt_base, crt_base_euclid,
                              tower_mod, phi_2_5_smooth)


class TetrationTests(unittest.TestCase):
    def test_direct_first_differences(self):
        # Directly form a^a (not a taller tower), for every a=1 mod 10 below 1000.
        for a in range(11,1000,10):
            p = Profile.from_base(a)
            delta = pow(a,a)-a
            with self.subTest(a=a):
                self.assertEqual(valuation(delta,2),p.alpha+p.sigma)
                self.assertEqual(valuation(delta,5),2*p.c)

    def test_independent_modular_towers(self):
        # Euler reduction does not use the claimed valuation formula.
        for a in range(11,1000,10):
            p = Profile.from_base(a)
            for n in range(2,11):
                k = p.stable(n)
                modulus = 10**(k+1)
                delta = (tower_mod(a,n+1,modulus)-tower_mod(a,n,modulus)) % modulus
                with self.subTest(a=a,n=n):
                    self.assertNotEqual(delta,0)
                    self.assertEqual(min(valuation(delta,2),valuation(delta,5)),k)

    def test_constructed_crossover_profiles(self):
        for c in range(1,81):
            a = crt_base(c)
            self.assertEqual(a,crt_base_euclid(c))
            p = Profile.from_base(a)
            for n in (1,2,3,4,5,9):
                k = p.stable(n)
                modulus = 10**(k+1)
                delta = (tower_mod(a,n+1,modulus)-tower_mod(a,n,modulus)) % modulus
                self.assertNotEqual(delta,0)
                self.assertEqual(min(valuation(delta,2),valuation(delta,5)),k)

    def test_onset_formula(self):
        # All admissible abstract profiles in this finite rectangle.
        for c in range(1,81):
            for high in range(2,81):
                for alpha,beta in ((1,high),(high,1)):
                    p = Profile(alpha,beta,c)
                    B = p.onset
                    self.assertTrue(all(p.speed(n)==p.eventual_speed
                                        for n in range(B,B+5)))
                    if B>1:
                        self.assertNotEqual(p.speed(B-1),p.eventual_speed)

    def test_partial_crossing_step(self):
        p = Profile(1,7,5)  # h=4 divisible by d=2: no intermediate gain.
        self.assertEqual([p.speed(i) for i in range(1,6)],[7,7,5,5,5])
        p = Profile(1,8,6)  # h=5 = 2*2+1: one intermediate gain 7.
        self.assertEqual([p.speed(i) for i in range(1,6)],[8,8,7,6,6])

    def test_published_example(self):
        p = Profile.from_base(163574218751)
        self.assertEqual((p.alpha,p.beta,p.c),(1,15,13))
        self.assertEqual(p.onset,7)
        self.assertEqual([p.stable(i) for i in range(1,8)],
                         [16,31,46,61,76,91,104])

    def test_error_handling(self):
        for a in (0,1,2,5,10,-9):
            with self.assertRaises(ValueError):
                Profile.from_base(a)
        with self.assertRaises(ValueError): valuation(0,2)
        with self.assertRaises(ValueError): valuation(3,3)
        with self.assertRaises(ValueError): phi_2_5_smooth(3)
        with self.assertRaises(ValueError): crt_base(0)
        with self.assertRaises(ValueError): Profile(2,2,1)

if __name__ == '__main__':
    unittest.main(verbosity=2)
