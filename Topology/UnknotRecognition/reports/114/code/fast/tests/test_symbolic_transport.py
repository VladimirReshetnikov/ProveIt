"""Huge signed runs must survive CLI serialization and exact replay."""
from contextlib import redirect_stdout
import copy
import io
import importlib
import json
import sys
import unittest
from unittest.mock import patch

from fastunknot.braid_profile import structural_runs_certificate, verify_structural_runs_certificate
from fastunknot.integer_codec import decode_degree_profile, encoded_integer, json_safe
from fastunknot.twist.continuation import load_runs, main
from fastunknot.twist.core import Run, homology
from fastunknot.twist.tail import expand_profile, profile_dimension, profile_rank, tail_homology


class SymbolicTransportTests(unittest.TestCase):
    def invoke(self, value, *flags):
        output = io.StringIO()
        with patch('sys.stdin', io.StringIO(json.dumps(value))), redirect_stdout(output):
            code = main(['-', *flags])
        return code, json.loads(output.getvalue())

    def test_huge_both_sign_profiles_roundtrip_without_global_limit_change(self):
        limit = sys.get_int_max_str_digits()
        magnitude = (1 << 20000) + 1
        for sign in (-1, 1):
            code, result = self.invoke({'strands': '0x2', 'runs': [['0x1', hex(sign*magnitude)]]},
                                       '--mode', 'homology', '--check-d2')
            self.assertEqual((code, result['status']), (0, 'COMPUTED'))
            h = result['homology']
            self.assertEqual(encoded_integer(h['reduced_rank']), magnitude)
            profile = decode_degree_profile(h['degree_profile'])
            self.assertEqual(profile_rank(profile), magnitude)
            self.assertEqual(profile_dimension(profile, sign * 10000), 1)
            self.assertEqual(h['reference']['stats']['basis'], 4)
            self.assertEqual(h['tail_certificate']['one_full_slice_reduced_rank'], 1)
        self.assertEqual(sys.get_int_max_str_digits(), limit)

    def test_huge_balanced_structural_certificate_replays_independently(self):
        magnitude = (1 << 20000) + 1
        pairs = [(1,magnitude),(2,-magnitude),(3,magnitude),(4,-magnitude)]
        code, result = self.invoke({'strands':5, 'runs':json_safe(pairs)}, '--mode', 'profile')
        self.assertEqual((code,result['status']), (0,'KNOTTED'))
        certificate = result['certificate']
        self.assertEqual(encoded_integer(certificate['writhe']), 0)
        with patch('fastunknot.braid_profile.structural_runs_certificate', side_effect=AssertionError):
            self.assertTrue(verify_structural_runs_certificate(5, pairs, certificate))
        for key, value in [('homogeneity_defect',False), ('crossings',1),
                           ('status','UNKNOT'), ('strands',True)]:
            bad = dict(certificate, **{key:value})
            self.assertFalse(verify_structural_runs_certificate(5, pairs, bad))
        self.assertFalse(verify_structural_runs_certificate(10**100, [], certificate))

    def test_small_serialized_profile_and_verifier_types(self):
        result = tail_homology(3, [Run(1,17),Run(2,-1),Run(1,1),Run(2,-1)])
        restored = decode_degree_profile(json.loads(json.dumps(json_safe(result['degree_profile']))))
        self.assertEqual(restored, result['degree_profile'])
        self.assertEqual(expand_profile(restored), homology(3,[Run(1,17),Run(2,-1),Run(1,1),Run(2,-1)])['by_degree'])
        cert = structural_runs_certificate(2,[(1,1)])
        for key, value in list(cert.items()):
            if type(value) is int:
                bad = dict(cert, **{key:float(value)})
                self.assertFalse(verify_structural_runs_certificate(2,[(1,1)],bad))
        bad = copy.deepcopy(cert)
        bad['rasmussen_interval'][0] = False
        self.assertFalse(verify_structural_runs_certificate(2,[(1,1)],bad))

    def test_strict_numeric_and_profile_schemas(self):
        for bad in (True,1.0,'12','1e20','0x','-0x',' 0x1','0b1'):
            with self.subTest(value=bad), self.assertRaises(ValueError):
                load_runs({'strands':2,'runs':[[1,bad]]})
        for bad in ({'points':{'1':1,'0x1':1},'intervals':[]},
                    {'points':{},'intervals':[{'start':0,'end':1,'dimension':True}]}):
            with self.assertRaises(ValueError):
                decode_degree_profile(bad)
        with self.assertRaises(ValueError):
            json_safe({1:1,'1':2})

    def test_expiry_during_final_structural_arithmetic_stays_unknown(self):
        module = importlib.import_module('fastunknot.twist.continuation')
        from fastunknot.twist.core import Budget
        finished = [False]
        real = module.structural_runs_certificate
        def certificate(*args, **kwargs):
            result = real(*args, **kwargs)
            finished[0] = True
            return result
        for mode in ('recognize','profile'):
            finished[0] = False
            with patch.object(module, 'monotonic', side_effect=lambda: 2.0 if finished[0] else 0.0), \
                    patch.object(module, 'structural_runs_certificate', side_effect=certificate):
                result = module.compute(2,[Run(1,3)],mode=mode,budget=Budget(seconds=1))
            self.assertEqual(result['status'], 'UNKNOWN')


if __name__ == '__main__':
    unittest.main()
