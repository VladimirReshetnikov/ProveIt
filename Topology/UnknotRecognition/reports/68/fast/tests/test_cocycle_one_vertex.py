from copy import deepcopy
import json
import unittest
from unittest.mock import patch

from fastunknot.cocycle_span import minimize_cocycle_span
from fastunknot.cocycle_span_verify import verify_cocycle_span
from fastunknot.integer_codec import json_safe
from fastunknot.normal_cocycle import CocycleLimit


class OneVertexSpanTests(unittest.TestCase):
    def test_direct_duality_and_linear_work_with_no_network(self):
        for n in (1,8,64,512):
            vs=[[71]*4 for _ in range(n)];hs=[[0,i,-3*i,i+1] for i in range(n)]
            with patch('fastunknot.cocycle_span._zero_block',side_effect=AssertionError), \
                 patch('fastunknot.cocycle_span.heappush',side_effect=AssertionError):
                result=minimize_cocycle_span(vs,hs)
            self.assertEqual(result['stats']['work'],5*n+3)
            for key in ('network_nodes','network_arcs','augmentations','heap_pops','relaxations'):
                self.assertEqual(result['stats'][key],0)
            self.assertEqual(result['stats']['disc_count'],sum(max(h)-min(h) for h in hs))
            self.assertTrue(verify_cocycle_span(vs,hs,result['certificate']))

    def test_binary_heights_offsets_signs_and_producer_free_replay(self):
        vs=[[17]*4 for _ in range(9)]
        hs=[[0,i,-i,3*i] for i in range(9)]
        small=minimize_cocycle_span(vs,hs)
        for sign in (1,-1):
            huge=[[sign*x*(1<<20000)+(i+1)*(1<<24000) for x in row] for i,row in enumerate(hs)]
            result=minimize_cocycle_span(vs,huge)
            self.assertEqual(result['stats']['work'],small['stats']['work'])
            self.assertEqual(result['stats']['disc_count'],small['stats']['disc_count']*(1<<20000))
            proof=json.loads(json.dumps(json_safe(result['certificate'])))
            with patch('fastunknot.cocycle_span.minimize_cocycle_span',side_effect=AssertionError), \
                 patch('fastunknot.normal_cocycle.local_coordinates',side_effect=AssertionError):
                self.assertTrue(verify_cocycle_span(vs,huge,proof))
            bad=deepcopy(proof);bad['matching'][1]=bad['matching'][0]
            self.assertFalse(verify_cocycle_span(vs,huge,bad))

    def test_budget_cancellation_validation_and_input_immutability(self):
        vs=[[4]*4]*8;hs=[[0,i,-i,i] for i in range(8)];saved=deepcopy((vs,hs))
        result=minimize_cocycle_span(vs,hs);work=result['stats']['work']
        self.assertEqual(minimize_cocycle_span(vs,hs,max_work=work),result)
        with self.assertRaises(CocycleLimit):minimize_cocycle_span(vs,hs,max_work=work-1)
        for stop in (1,work//2,work):
            calls=[0]
            def cancel():
                calls[0]+=1
                if calls[0]==stop:raise RuntimeError('cancelled')
            with self.assertRaisesRegex(RuntimeError,'cancelled'):minimize_cocycle_span(vs,hs,check=cancel)
        self.assertEqual((vs,hs),saved)
        for hs in (None,[],[[0,1,2,True]],[[0,1,2,'7']]):
            with self.assertRaises(ValueError):minimize_cocycle_span([[0]*4],hs)
