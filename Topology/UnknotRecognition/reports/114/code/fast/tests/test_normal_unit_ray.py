"""Primitive matching rays, scalar multiples, strict replay and honest caps."""
from copy import deepcopy
import json
import random
import unittest
from unittest.mock import patch

from fastunknot.integer_codec import json_safe
from fastunknot.normal_disk_kernel import normal_compressing_disk_count,verify_normal_disk_count_certificate
from fastunknot.normal_support_peeling import peel_normal_support_ray,peel_support_ray
from fastunknot.normal_support_peeling_verify import verify_normal_support_ray,verify_support_ray
from normal_orbit_research.fixtures import layered_torus,interior_vertex_torus
from tests.test_normal_surface_orbits import relabel


class NormalUnitRayTests(unittest.TestCase):
    def test_layered_linear_witness_and_zero_orbit_allowance(self):
        for n in (1,2,8,32,128,256):
            raw,coords=layered_torus(n)
            proof=peel_normal_support_ray(raw,coords)
            self.assertEqual(len(proof['steps']),3*n-1)
            self.assertTrue(verify_normal_support_ray(raw,coords,proof))
            old=normal_compressing_disk_count(raw,coords,unit_ray=False,record_certificate=True)
            new=normal_compressing_disk_count(raw,coords,max_cycles=0,record_certificate=True)
            self.assertEqual(new['compressing_disk_components'],old['compressing_disk_components'])
            self.assertEqual(new['stats']['orbit_cycles'],0)
            self.assertEqual(new['certificate']['schema'],'normal-disc-count-v2')
            self.assertTrue(verify_normal_disk_count_certificate(raw,coords,new['certificate']))
            self.assertTrue(verify_normal_disk_count_certificate(raw,coords,old['certificate']))

    def test_source_scaling_links_relabellings_and_one_sided_counts(self):
        rng=random.Random(261009602)
        raw,base=layered_torus(4)
        for _ in range(6):
            raw,base=relabel(raw,base,rng)
            for factor in (1,2,7):
                coords=[[factor*x+(factor+1 if j<4 else 0) for j,x in enumerate(row)] for row in base]
                new=normal_compressing_disk_count(raw,coords,record_certificate=True)
                self.assertEqual(new['compressing_disk_components'],factor)
                self.assertTrue(verify_normal_disk_count_certificate(raw,coords,new['certificate']))
        coords=[[(2**20000+1)*x+(2**10000+7 if j<4 else 0) for j,x in enumerate(row)] for row in base]
        answer=normal_compressing_disk_count(raw,coords,record_certificate=True)
        proof=json.loads(json.dumps(json_safe(answer['certificate'])))
        self.assertTrue(verify_normal_disk_count_certificate(raw,coords,proof))
        raw,_=layered_torus(1)
        for factor in (1,2,3,8):
            coords=[[0,0,0,0,0,factor,0]]
            result=normal_compressing_disk_count(raw,coords,record_certificate=True)
            self.assertEqual(result['compressing_disk_components'],0)
            self.assertTrue(verify_normal_disk_count_certificate(raw,coords,result['certificate']))

    def test_no_search_or_reduction_in_replay_and_mutations(self):
        raw,coords=layered_torus(4)
        proof=normal_compressing_disk_count(raw,coords,record_certificate=True)['certificate']
        with patch('fastunknot.normal_support_peeling.peel_support_ray',side_effect=AssertionError), \
             patch('fastunknot.normal_disk_kernel.canonical_disk_core',side_effect=AssertionError), \
             patch('fastunknot.normal_disk_kernel.normal_component_census',side_effect=AssertionError):
            self.assertTrue(verify_normal_disk_count_certificate(raw,coords,proof))
        for field in proof:
            bad=deepcopy(proof);del bad[field]
            self.assertFalse(verify_normal_disk_count_certificate(raw,coords,bad))
        for field in proof['core_certificate']:
            bad=deepcopy(proof);del bad['core_certificate'][field]
            self.assertFalse(verify_normal_disk_count_certificate(raw,coords,bad))
        for action in ('seed','pivot','missing','repeat','coefficient','parity','count','euler','extra','schema'):
            bad=deepcopy(proof);core=bad['core_certificate'];support=core['support_certificate']
            if action=='seed':support['seed']=True
            elif action=='pivot':support['steps'][0][1]=support['seed']
            elif action=='missing':support['steps'].pop()
            elif action=='repeat':support['steps'][-1]=support['steps'][0]
            elif action=='coefficient':support['steps'][0][0]=0
            elif action=='parity':core['boundary_homology_mod2']=[0,0]
            elif action=='count':core['compressing_disk_components']=0
            elif action=='euler':core['euler_characteristic']=0
            elif action=='extra':core['extra']=1
            else:bad['schema']='normal-disc-count-v1'
            if bad==proof:continue
            self.assertFalse(verify_normal_disk_count_certificate(raw,coords,bad),action)

    def test_failed_exposure_is_inconclusive_not_rank_evidence(self):
        prepared={'matching':[{0:2,1:-3}]};analysed={'rows':[[3,2,0,0,0,0,0]]}
        self.assertIsNone(peel_support_ray(prepared,analysed))
        forged=dict(schema='normal-support-ray-peeling-v1',support=[0,1],seed=0,steps=[[0,1]],nullity=1)
        self.assertFalse(verify_support_ray(prepared,analysed,forged))
        self.assertIsNone(peel_support_ray({'matching':[]},{'rows':[[1,1,0,0,0,0,0]]}))
        raw,basis=interior_vertex_torus()
        coords=[[basis['sphere'][t][j]+basis['boundary_disk'][t][j] for j in range(7)] for t in range(len(basis['sphere']))]
        self.assertEqual(normal_compressing_disk_count(raw,coords,max_cycles=0)['compressing_disk_components'],0)

    def test_options_and_cancellation(self):
        raw,coords=layered_torus(8)
        for value in (None,0,1,'yes'):
            with self.assertRaises(ValueError):normal_compressing_disk_count(raw,coords,unit_ray=value)
        proof=normal_compressing_disk_count(raw,coords,record_certificate=True)['certificate']
        for call in (lambda check:normal_compressing_disk_count(raw,coords,check=check),
                     lambda check:verify_normal_disk_count_certificate(raw,coords,proof,check=check)):
            ticks=[0]
            def count():ticks[0]+=1
            call(count);total=ticks[0]
            for stop in (1,total//2,total):
                ticks[0]=0
                def cancel():
                    ticks[0]+=1
                    if ticks[0]==stop:raise ValueError('caller cancellation')
                with self.assertRaisesRegex(ValueError,'caller cancellation'):call(cancel)
