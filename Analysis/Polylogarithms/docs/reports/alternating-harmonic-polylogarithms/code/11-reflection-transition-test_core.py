#!/usr/bin/env python3
"""Fast exact-arithmetic and correction-script regression tests."""
from fractions import Fraction as Q
import importlib.util
from pathlib import Path
import unittest
from polylog_research import (harmonic_elementary, composition_coefficient,
    envelope, log2_interval, inverse_sqrt2_interval, fast_certificate,
    decimal_outward)

path=Path(__file__).resolve().parents[1]/'corrections'/'apply_goncharov_fix.py'
spec=importlib.util.spec_from_file_location('order_fix',path)
fix=importlib.util.module_from_spec(spec)
spec.loader.exec_module(fix)


class CoreTests(unittest.TestCase):
    def test_harmonic_values(self):
        self.assertEqual(harmonic_elementary(0,0),1)
        self.assertEqual(harmonic_elementary(4,2),Q(35,24))
        self.assertEqual(harmonic_elementary(3,4),0)

    def test_composition(self):
        for r in range(5):
            for j in range(6):
                self.assertEqual(composition_coefficient(r,j),harmonic_elementary(r+j,r))

    def test_envelope(self):
        self.assertEqual(envelope(5,1,0),(Q(-1,243),Q(0)))
        self.assertEqual(envelope(1,0,0),(Q(0),Q(1)))

    def test_positive_intervals(self):
        lo,hi=log2_interval(10)
        self.assertTrue(Q(69,100)<lo<hi<Q(70,100))
        lo,hi=inverse_sqrt2_interval(100)
        self.assertTrue(lo**2<Q(1,2)<hi**2)

    def test_decimal_outward(self):
        self.assertEqual(decimal_outward(Q(-1,3),3),'-0.334')
        self.assertEqual(decimal_outward(Q(-1,3),3,True),'-0.333')
        self.assertEqual(decimal_outward(Q(1,3),3),'0.333')
        self.assertEqual(decimal_outward(Q(1,3),3,True),'0.334')

    def test_certificate_consistency(self):
        lo,hi=fast_certificate(1,1,32)
        el,eh=envelope(1,1,12)
        self.assertTrue(el<=lo<hi<=eh)

    def test_guarded_transformation(self):
        source=r'\label{eq:G-def} G=\int_{0<t_1<\dots<t_n<1}'
        changed=fix.transform(source)
        self.assertIn(fix.NEW,changed)
        self.assertNotIn(fix.OLD,changed)
        with self.assertRaises(ValueError):
            fix.transform(source+fix.OLD)
        with self.assertRaises(ValueError):
            fix.transform('wrong source')
        self.assertEqual(fix.git_blob_sha(b''),'e69de29bb2d1d6434b8b29ae775ad8c2e48c5391')

if __name__=='__main__':
    unittest.main(verbosity=2)
