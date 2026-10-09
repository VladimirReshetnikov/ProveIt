"""Maintained API boundaries beyond the delivered sparse reconstruction tests."""
import copy
import json
import unittest
from unittest.mock import patch
from fastunknot.interval_orbits import IntervalPairing as P, SignedPairing as SP
from fastunknot.integer_codec import json_safe
from fastunknot.sparse_incidence import analyze_sparse_port_incidence as analyze, analyze_sparse_signed_incidence as signed
from fastunknot.sparse_incidence_verify import verify_sparse_port_incidence_certificate as verify, verify_sparse_signed_incidence_certificate as signed_verify


class IntegrationTests(unittest.TestCase):
    def test_invalid_options_precede_resource_exhaustion(self):
        with patch('fastunknot.sparse_incidence.count_orbits',side_effect=AssertionError('orbit search should not run')):
            for fn in (analyze,signed):
                for options in ({'strategy':'unknown'},{'max_signatures':True},{'max_signatures':-1}):
                    with self.assertRaises(ValueError):fn(0,[],[],max_cycles=0,max_queries=0,**options)

    def test_false_callable_cancellation_is_not_ignored(self):
        class Cancel:
            def __bool__(self):return False
            def __call__(self):raise RuntimeError('cancelled callback')
        for fn in (analyze,signed):
            with self.assertRaisesRegex(RuntimeError,'cancelled callback'):fn(0,[],[],check=Cancel())
        for fn in (verify,signed_verify):
            with self.assertRaisesRegex(RuntimeError,'cancelled callback'):fn(0,[],[],{},check=Cancel())

    def test_signed_allowances_cover_entire_discovery_and_proof(self):
        ps=[SP(P(0,4,5,9),0),SP(P(10,14,10,14,True),1)]
        ports=[[(0,3)],[(3,8)],[(11,14)]]
        complete=signed(20,ps,ports,strategy='split',record_certificate=True)
        limits=complete['stats'];self.assertTrue(signed_verify(20,ps,ports,complete['certificate']))
        for key,stat in (('max_queries','orbit_queries'),('max_cycles','orbit_cycles')):
            for limit in (0,1,limits[stat]-1):
                result=signed(20,ps,ports,strategy='split',record_certificate=True,**{key:limit})
                self.assertEqual(result['status'],'INCONCLUSIVE');self.assertNotIn('histogram',result)
                self.assertNotIn('signed_histogram',result);self.assertNotIn('certificate',result)
                self.assertLessEqual(result['stats'][stat],limit)
            result=signed(20,ps,ports,strategy='split',record_certificate=True,**{key:limits[stat]})
            self.assertEqual(result['signed_histogram'],complete['signed_histogram'])
        result=signed(20,ps,ports,max_signatures=1,record_certificate=True)
        self.assertEqual(result['status'],'INCONCLUSIVE');self.assertNotIn('histogram',result)

    def test_sparse_masks_and_proofs_round_trip_beyond_decimal_limit(self):
        size=1<<16000;ports=[[(0,7)],[],[(0,7)],[(9,12)]]
        result=analyze(size,[],ports,strategy='split',record_certificate=True)
        proof=json.loads(json.dumps(json_safe(result['certificate'])))
        self.assertTrue(verify(size,[],ports,proof))
        self.assertFalse(verify(size,[],list(reversed(ports)),proof))
        for mask in (-1,1<<len(ports),True,'not a number'):
            bad=copy.deepcopy(proof);bad['entries'][0]['mask']=mask
            self.assertFalse(verify(size,[],ports,bad))
