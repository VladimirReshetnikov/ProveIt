"""Wholly prismatic cut components and conservative bounded core counts."""
from contextlib import ExitStack
from copy import deepcopy
import json
from pathlib import Path
import subprocess
from types import ModuleType
import unittest
from unittest.mock import patch
from fastunknot.integer_codec import json_safe
from fastunknot.normal_cut_complement import normal_complement_components
from fastunknot.normal_cut_complement_verify import verify_normal_complement_certificate
from normal_orbit_research.fixtures import layered_torus
ROOT=Path(__file__).resolve().parents[2]

class CutProductTests(unittest.TestCase):
    def test_meridian_vertex_link_and_one_sided_product_families(self):
        raw,meridian=layered_torus(1)
        for vector,core,product in ((meridian,1,lambda n:n-1),([[1,1,1,1,0,0,0]],2,lambda n:n-1),
                                   ([[0,0,0,0,0,1,0]],1,lambda n:n//2)):
            for n in range(1,7):
                rows=[[n*x for x in row]for row in vector]
                r=normal_complement_components(raw,rows,classify_prisms=True,record_certificate=True)
                self.assertEqual((r['core_components'],r['prismatic_components']),(core,product(n)))
                self.assertTrue(verify_normal_complement_certificate(raw,rows,r['certificate']))
                self.assertEqual(r['cut_components'],r['core_components']+r['prismatic_components'])

    def test_actual_scaled_sources_match_expanded_chamber_midsections(self):
        bank={r['id']:r['triangulation']for r in json.loads((ROOT/'reports/57/results/discovery_corpus.json').read_text())['records']}
        initial=json.loads((ROOT/'synthesis/data/complement-chamber-pilot.json').read_text())
        vectors={(r['id'],r['index']):r['coordinates']for r in initial['records']}
        pilot=json.loads((ROOT/'synthesis/data/cut-product-pilot.json').read_text())
        selected={}
        for case in pilot['records']:
            if case['product_components']>0:selected.setdefault(case['id'],case)
        self.assertEqual(len(selected),48)
        for name,case in selected.items():
            raw=bank[name];rows=[[case['scale']*x for x in row]for row in vectors[name,case['index']]]
            r=normal_complement_components(raw,rows,classify_prisms=True,record_certificate=True)
            for key in ('cut_components','core_components','prismatic_components'):
                self.assertEqual(r[key],case['product_components']if key=='prismatic_components'else case[key])
            self.assertLessEqual(r['core_components'],r['exceptional_chambers'])
            self.assertLessEqual(r['exceptional_chambers'],6*len(rows))
            self.assertTrue(verify_normal_complement_certificate(raw,rows,r['certificate']))

    def test_disabled_mode_preserves_frozen_results_and_legacy_replay(self):
        path='Topology/UnknotRecognition/fast/fastunknot/normal_cut_complement.py'
        old=ModuleType('fastunknot._old_product_cut');old.__package__='fastunknot'
        code=subprocess.check_output(['git','show','1aeabfa735c78a30b732405b101009d376d56f18:'+path],cwd=ROOT.parents[1])
        exec(compile(code,path,'exec'),old.__dict__)
        for t in (1,3):
            raw,rows=layered_torus(t)
            expected=old.normal_complement_components(raw,rows,record_certificate=True)
            self.assertEqual(normal_complement_components(raw,rows,record_certificate=True),expected)
            self.assertEqual(normal_complement_components(raw,rows,classify_prisms=False,record_certificate=True),expected)
            self.assertTrue(verify_normal_complement_certificate(raw,rows,expected['certificate']))

    def test_shared_cycle_and_replay_operation_caps(self):
        raw,rows=layered_torus(1)
        for limit in (0,4,7):
            r=normal_complement_components(raw,rows,classify_prisms=True,record_certificate=True,max_cycles=limit)
            self.assertEqual(r['status'],'INCONCLUSIVE');self.assertLessEqual(r['cycles'],limit)
            for key in ('cut_components','core_components','prismatic_components','certificate'):self.assertNotIn(key,r)
        r=normal_complement_components(raw,rows,classify_prisms=True,record_certificate=True,max_cycles=8)
        self.assertEqual(r['status'],'COMPLETE')
        proof=r['certificate'];first=len(proof['orbit_certificate']['operations'])
        full=first+len(proof['core_cone_certificate']['operations'])
        self.assertFalse(verify_normal_complement_certificate(raw,rows,proof,max_operations=first))
        self.assertTrue(verify_normal_complement_certificate(raw,rows,proof,max_operations=full))

    def test_large_binary_product_count_and_producer_disabled_replay(self):
        raw,vector=layered_torus(1);n=1<<16384
        rows=[[n*x for x in row]for row in vector]
        r=normal_complement_components(raw,rows,classify_prisms=True,record_certificate=True)
        self.assertEqual((r['core_components'],r['prismatic_components']),(1,n-1))
        wire=json.loads(json.dumps(json_safe(r['certificate'])))
        disabled=('fastunknot.normal_cut_complement._exceptional_chambers',
            'fastunknot.normal_cut_complement._chamber_system','fastunknot.interval_orbits.count_orbits')
        with ExitStack()as stack:
            for name in disabled:stack.enter_context(patch(name,side_effect=AssertionError('producer used')))
            self.assertTrue(verify_normal_complement_certificate(raw,rows,wire))

    def test_schema_arithmetic_and_cone_trace_mutations_rejected(self):
        raw,vector=layered_torus(1);rows=[[4*x for x in row]for row in vector]
        proof=normal_complement_components(raw,rows,classify_prisms=True,record_certificate=True)['certificate']
        for key,value in (('core_components',True),('core_components',0),('prismatic_components',-1),
                          ('prismatic_components','3'),('core_cone_certificate',None),('schema','normal-cut-components-v1')):
            p=deepcopy(proof);p[key]=value
            self.assertFalse(verify_normal_complement_certificate(raw,rows,p))
        p=deepcopy(proof);p['core_components']=2;p['prismatic_components']=2
        self.assertFalse(verify_normal_complement_certificate(raw,rows,p))
        p=deepcopy(proof);p['core_cone_certificate']['pairings'][-1][2]+=1
        self.assertFalse(verify_normal_complement_certificate(raw,rows,p))
        p=deepcopy(proof);p.pop('core_cone_certificate')
        self.assertFalse(verify_normal_complement_certificate(raw,rows,p))
        with self.assertRaises(ValueError):normal_complement_components(raw,rows,classify_prisms=1)

    def test_empty_surface_conservative_core_and_cancellation(self):
        raw,_=layered_torus(1);rows=[[0]*7]
        r=normal_complement_components(raw,rows,classify_prisms=True,record_certificate=True)
        self.assertEqual((r['core_components'],r['prismatic_components']),(1,0))
        def cancel():raise ValueError('external interruption')
        with self.assertRaisesRegex(ValueError,'external interruption'):
            normal_complement_components(raw,rows,classify_prisms=True,check=cancel)
        with self.assertRaisesRegex(ValueError,'external interruption'):
            verify_normal_complement_certificate(raw,rows,r['certificate'],check=cancel)

if __name__=='__main__':unittest.main()
