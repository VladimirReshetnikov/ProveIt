"""Domain, exactness, and CLI regression tests; all checks survive -O."""
import argparse
from contextlib import redirect_stderr, redirect_stdout
from fractions import Fraction
import io
import json
import unittest
import prefactor as p


class PrefactorTests(unittest.TestCase):
    def test_empty(self):
        self.assertEqual(p.counts(0),[1])
        self.assertEqual(p.q_series(0),[1])
        self.assertEqual(p.enumerate_checks(0)['admissible_partitions'],1)

    def test_count_prefix(self):
        self.assertEqual(p.counts(15),[1,1,1,2,3,3,5,7,9,11,14,19,25,31,38,46])

    def test_series_independence(self):
        self.assertEqual(p.q_series(80),p.counts(80))

    def test_counts_nested(self):
        self.assertEqual(p.counts(90)[:51],p.counts(50))

    def test_direct_enumeration(self):
        check=p.enumerate_checks(20)
        self.assertTrue(check['count_match'])
        self.assertEqual(check['injection_images'],check['admissible_partitions'])

    def test_domains(self):
        for function,maximum in ((p.counts,p.MAX_N),(p.q_series,p.MAX_SERIES),(p.enumerate_checks,p.MAX_ENUMERATION)):
            for bad in (-1,maximum+1,True,False,1.0,'1',None,Fraction(1)):
                with self.subTest(function=function.__name__,bad=bad):
                    with self.assertRaises((ValueError,TypeError)):
                        function(bad)

    def test_threshold_domains(self):
        for bad in (0,-1,p.MAX_TARGET+1,True,1.0,'10'):
            with self.assertRaises((ValueError,TypeError)):
                p.threshold(bad,10)
        for bad in (-1,401,True,'10'):
            with self.assertRaises((ValueError,TypeError)):
                p.threshold(10,bad)

    def test_threshold_plateau(self):
        self.assertEqual(p.threshold(1,0)['threshold'],0)
        self.assertEqual(p.threshold(2,4)['threshold'],3)
        self.assertEqual(p.threshold(3,6)['threshold'],4)
        self.assertEqual(p.threshold(4,6)['threshold'],6)
        self.assertEqual(p.threshold(4,5)['status'],'unreached')
        self.assertIsNone(p.threshold(p.MAX_TARGET,0)['threshold'])

    def test_airy_algebra(self):
        self.assertTrue(p.airy_algebra()['Q1_integral_zero'])

    def test_tilt(self):
        result=p.tilt_checks()
        self.assertTrue(result['exact_tilt'])
        self.assertEqual(result['rational_tilt_comparisons'],2*sum(4**m for m in range(7)))

    def test_canonical_cli_integer(self):
        self.assertEqual(p.canonical_integer('0',400),0)
        self.assertEqual(p.canonical_integer('400',400),400)
        for bad in ('','00','01','+1','-1',' 1','1 ','1.0','1e2','１','١','401','9'*202):
            with self.assertRaises(argparse.ArgumentTypeError):
                p.canonical_integer(bad,400)

    def test_cli_stdout(self):
        stream=io.StringIO()
        with redirect_stdout(stream): p.main(['counts','--max-n','5'])
        self.assertEqual(json.loads(stream.getvalue())['counts'],['1','1','1','2','3','3'])

    def test_cli_invalid(self):
        for args in (['counts','--max-n','401'],['series','--max-n','101'],['counts','--max-n','+1'],['unknown'],[]):
            with redirect_stderr(io.StringIO()):
                with self.assertRaises(SystemExit): p.main(args)

    def test_illustration_labels(self):
        result=p.illustrations()
        self.assertIn('Noncertified',result['scope'])
        self.assertAlmostEqual(float(result['constants']['K']),1.27049761356,places=10)
        self.assertEqual([r['n'] for r in result['finite_residuals']],[25,50,100,200,400])


if __name__=='__main__':
    unittest.main()
