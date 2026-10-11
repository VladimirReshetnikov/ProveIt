"""Connected normal midsections and binary bundle multiplicities."""
from contextlib import ExitStack
from copy import deepcopy
import json
import unittest
from unittest.mock import patch
from fastunknot.integer_codec import json_safe
from fastunknot.normal_cut_complement import normal_complement_components
from fastunknot.normal_prismatic_inventory import normal_prismatic_inventory
from fastunknot.normal_prismatic_inventory_verify import verify_normal_prismatic_inventory
from normal_orbit_research.fixtures import layered_torus

class PrismaticInventoryTests(unittest.TestCase):
    def test_parallel_meridian_and_vertex_link_inventory(self):
        raw,vector=layered_torus(1)
        for v,core in ((vector,1),([[1,1,1,1,0,0,0]],2)):
            for n in (1,2,3,16):
                rows=[[n*x for x in row]for row in v]
                r=normal_prismatic_inventory(raw,rows,record_certificate=True)
                self.assertEqual(r['inventory']['core_components'],core)
                self.assertEqual(r['inventory']['prismatic_components'],n-1)
                bases=r['inventory']['bases']
                self.assertEqual(bases,[]if n==1 else[dict(coordinates=v,multiplicity=n-1,euler_characteristic=1)])
                self.assertTrue(verify_normal_prismatic_inventory(raw,rows,r['certificate']))

    def test_one_sided_midsection_and_connected_double_remain_distinct(self):
        raw,_=layered_torus(1);mobius=[[0,0,0,0,0,1,0]];annulus=[[0,0,0,0,0,2,0]]
        for n in range(2,8):
            rows=[[n*x for x in row]for row in mobius]
            r=normal_prismatic_inventory(raw,rows,record_certificate=True)
            expected=[]
            if n//2-(not n%2)>0:
                expected.append(dict(coordinates=annulus,multiplicity=n//2-(not n%2),euler_characteristic=0))
            if n%2==0:expected.append(dict(coordinates=mobius,multiplicity=1,euler_characteristic=0))
            expected.sort(key=lambda b:tuple(x for row in b['coordinates']for x in row))
            self.assertEqual(r['inventory']['bases'],expected)
            self.assertTrue(verify_normal_prismatic_inventory(raw,rows,r['certificate']))

    def test_layered_actual_midsections(self):
        for t in (2,4,8):
            raw,v=layered_torus(t);rows=[[3*x for x in row]for row in v]
            r=normal_prismatic_inventory(raw,rows,record_certificate=True)
            self.assertEqual(r['inventory']['bases'],[dict(coordinates=v,multiplicity=2,euler_characteristic=1)])
            self.assertTrue(verify_normal_prismatic_inventory(raw,rows,r['certificate']))

    def test_binary_multiplicity_json_replay_without_expansion(self):
        raw,v=layered_torus(1);n=1<<16384;rows=[[n*x for x in row]for row in v]
        r=normal_prismatic_inventory(raw,rows,record_certificate=True)
        self.assertEqual(r['inventory']['bases'][0]['multiplicity'],n-1)
        self.assertEqual(r['stats']['maximum_weight_runs'],6)
        wire=json.loads(json.dumps(json_safe(r['certificate'])))
        self.assertTrue(verify_normal_prismatic_inventory(raw,json.loads(json.dumps(json_safe(rows))),wire))

    def test_orbit_trace_reuse_is_checked_and_search_free(self):
        raw,v=layered_torus(3);rows=[[4*x for x in row]for row in v]
        cut=normal_complement_components(raw,rows,record_certificate=True)
        fresh=normal_prismatic_inventory(raw,rows,record_certificate=True)
        with patch('fastunknot.weighted_orbits.count_orbits',side_effect=AssertionError('orbit search')):
            reused=normal_prismatic_inventory(raw,rows,orbit_certificate=cut['certificate']['orbit_certificate'],record_certificate=True)
        self.assertEqual(reused['inventory'],fresh['inventory'])
        self.assertTrue(verify_normal_prismatic_inventory(raw,rows,reused['certificate']))
        wrong=deepcopy(cut['certificate']['orbit_certificate']);wrong['orbit_count']+=1
        with self.assertRaises(ValueError):normal_prismatic_inventory(raw,rows,orbit_certificate=wrong)
        with self.assertRaises(ValueError):normal_prismatic_inventory(raw,rows,orbit_certificate=cut['certificate']['orbit_certificate'],max_cycles=1)

    def test_independent_weights_and_summary_replay_without_producers(self):
        raw,v=layered_torus(4);rows=[[3*x for x in row]for row in v]
        proof=normal_prismatic_inventory(raw,rows,record_certificate=True)['certificate']
        disabled=('fastunknot.normal_prismatic_inventory._prism_weights',
            'fastunknot.normal_prismatic_inventory._inventory','fastunknot.normal_prismatic_inventory.normal_prismatic_inventory',
            'fastunknot.normal_cut_complement._chamber_system','fastunknot.weighted_orbits.weighted_orbit_histogram',
            'fastunknot.weighted_orbits.weighted_histogram_from_orbit_certificate','fastunknot.interval_orbits.count_orbits')
        with ExitStack()as stack:
            for name in disabled:stack.enter_context(patch(name,side_effect=AssertionError('producer invoked')))
            self.assertTrue(verify_normal_prismatic_inventory(raw,rows,proof))

    def test_mutated_source_weights_bases_and_multiplicities_rejected(self):
        raw,v=layered_torus(2);rows=[[4*x for x in row]for row in v]
        proof=normal_prismatic_inventory(raw,rows,record_certificate=True)['certificate']
        mutations=[]
        for field,value in (('schema','normal-cut-components-v2'),('input_sha256','0'*64),('weighted_certificate',None)):
            p=deepcopy(proof);p[field]=value;mutations.append(p)
        for field,value in (('core_components',True),('prismatic_components',0)):
            p=deepcopy(proof);p['inventory'][field]=value;mutations.append(p)
        p=deepcopy(proof);p['inventory']['bases'][0]['multiplicity']+=1;mutations.append(p)
        p=deepcopy(proof);p['inventory']['bases'][0]['coordinates'][0][0]+=1;mutations.append(p)
        p=deepcopy(proof);p['inventory']['bases'][0]['euler_characteristic']+=1;mutations.append(p)
        p=deepcopy(proof);p['weighted_certificate']['weights'][0][2][0]+=1;mutations.append(p)
        p=deepcopy(proof);p['weighted_certificate']['histogram'][0]['orbits']+=1;mutations.append(p)
        p=deepcopy(proof);p['inventory']['bases'].append(deepcopy(p['inventory']['bases'][0]));mutations.append(p)
        for p in mutations:self.assertFalse(verify_normal_prismatic_inventory(raw,rows,p))
        self.assertFalse(verify_normal_prismatic_inventory(raw,[[2*x for x in r]for r in rows],proof))

    def test_caps_limits_and_external_cancellation(self):
        raw,v=layered_torus(2);rows=[[3*x for x in row]for row in v]
        r=normal_prismatic_inventory(raw,rows,max_cycles=0,record_certificate=True)
        self.assertEqual(r['status'],'INCONCLUSIVE');self.assertNotIn('inventory',r);self.assertNotIn('certificate',r)
        proof=normal_prismatic_inventory(raw,rows,record_certificate=True)['certificate']
        self.assertFalse(verify_normal_prismatic_inventory(raw,rows,proof,max_operations=0))
        with self.assertRaises(ValueError):normal_prismatic_inventory(raw,rows,max_cycles=True)
        class Stop:
            def __bool__(self):return False
            def __call__(self):raise ValueError('external cancellation')
        with self.assertRaisesRegex(ValueError,'external cancellation'):normal_prismatic_inventory(raw,rows,check=Stop())
        with self.assertRaisesRegex(ValueError,'external cancellation'):verify_normal_prismatic_inventory(raw,rows,proof,check=Stop())

    def test_empty_cut_inventory_has_only_the_conservative_core(self):
        raw,_=layered_torus(1);r=normal_prismatic_inventory(raw,[[0]*7],record_certificate=True)
        self.assertEqual(r['inventory'],dict(core_components=1,prismatic_components=0,bases=[]))
        self.assertTrue(verify_normal_prismatic_inventory(raw,[[0]*7],r['certificate']))

if __name__=='__main__':unittest.main()
