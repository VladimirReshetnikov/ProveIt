from copy import deepcopy
import json
from pathlib import Path
import random
import unittest
from unittest.mock import patch

from fastunknot.pachner23 import pachner_23
from fastunknot.pachner32 import pachner_32
from fastunknot.pachner32_verify import verify_pachner_32
from fastunknot.normal_cocycle import _rank_one_cocycle_seed_details, CocycleLimit
from fastunknot.normal_surface_geometry import _prepare, NormalOrbitError
from fastunknot.normal_disk_kernel import normal_compressing_disk_count, verify_normal_disk_count_certificate
from normal_orbit_research.fixtures import layered_torus
from tests.test_normal_surface_orbits import relabel


class Pachner32Tests(unittest.TestCase):
    def test_certified_escape_from_coherent_family_obstruction(self):
        path=Path(__file__).resolve().parents[2]/'synthesis/data/coherent-obstruction-certificate.json'
        raw=json.loads(path.read_text())['moves'][-1]['triangulation']
        result=pachner_32(raw,5,[0,1]);after=result['triangulation']
        with patch('fastunknot.pachner32.pachner_32',side_effect=AssertionError):
            self.assertTrue(verify_pachner_32(raw,after,result['certificate']))
        self.assertEqual(len(after['tetrahedra']),7)
        seed,p=_rank_one_cocycle_seed_details(after)
        self.assertEqual(sum(map(sum,seed['coordinates'])),36)
        answer=normal_compressing_disk_count(after,seed['coordinates'],record_certificate=True)
        self.assertEqual(answer['compressing_disk_components'],1)
        self.assertTrue(verify_normal_disk_count_certificate(after,seed['coordinates'],answer['certificate']))
        self.assertEqual(p['vertices'],1)

    def test_round_trips_identified_vertices_and_relabelled_sites(self):
        rng=random.Random(261009514)
        for n in (2,3,8,20):
            initial,_=layered_torus(n)
            for _ in range(6):
                raw,_=relabel(initial,[[0]*7 for _ in initial['tetrahedra']],rng)
                t,f=next((t,f) for t,row in enumerate(raw['tetrahedra']) for f,r in enumerate(row)
                         if r is not None and r['tetrahedron'] != t)
                before=pachner_23(raw,t,f)['triangulation']
                for vs in ([0,1],[1,0]):
                    reduced=pachner_32(before,len(before['tetrahedra'])-3,vs)
                    self.assertTrue(verify_pachner_32(before,reduced['triangulation'],reduced['certificate']))
                    self.assertEqual(_prepare(reduced['triangulation'],lambda:None)['vertices'],1)

    def test_strict_proofs_boundary_maps_and_invalid_edges(self):
        initial,_=layered_torus(8)
        raw=pachner_23(initial,0,0)['triangulation']
        result=pachner_32(raw,6,[0,1]);proof=result['certificate'];after=result['triangulation']
        for bad in (None,{},dict(proof,extra=0),dict(proof,schema='wrong'),dict(proof,region=[])):
            self.assertFalse(verify_pachner_32(raw,after,bad))
        for field,value in [('tetrahedron',True),('tetrahedron',-1),('tetrahedron',99),
                            ('vertices',[0,1,2,3]),('vertices',[0,1,3,3]),
                            ('vertices',[True,1,3,4]),('vertices',None),('extra',0)]:
            bad=deepcopy(proof);bad['region'][0][field]=value
            self.assertFalse(verify_pachner_32(raw,after,bad))
        bad=deepcopy(proof);bad['region'][1]=bad['region'][0]
        self.assertFalse(verify_pachner_32(raw,after,bad))
        changed,_=relabel(after,[[0]*7 for _ in after['tetrahedra']],random.Random(71))
        self.assertFalse(verify_pachner_32(raw,changed,proof))
        for t,row in enumerate(after['tetrahedra']):
            for f,r in enumerate(row):
                if r is not None:
                    bad=deepcopy(after);bad['tetrahedra'][t][f]=None
                    self.assertFalse(verify_pachner_32(raw,bad,proof))
        for t,vs in ((True,[0,1]),(-1,[0,1]),(999,[0,1]),(0,[0,0]),(0,[True,1]),(0,(0,1))):
            with self.assertRaises(ValueError):pachner_32(raw,t,vs)
        # A one-tetrahedron torus has no three-distinct-tetrahedra edge star.
        one,_=layered_torus(1)
        for a in range(4):
            for b in range(a+1,4):
                with self.assertRaises(NormalOrbitError):pachner_32(one,0,[a,b])

    def test_limits_cancellation_and_aliases(self):
        raw=pachner_23(layered_torus(3)[0],0,0)['triangulation'];saved=deepcopy(raw)
        result=pachner_32(raw,1,[0,1])
        self.assertEqual(pachner_32(raw,1,[0,1],max_work=result['stats']['work']),result)
        with self.assertRaises(CocycleLimit):pachner_32(raw,1,[0,1],max_work=result['stats']['work']-1)
        for operation in (lambda c:pachner_32(raw,1,[0,1],check=c),
                          lambda c:verify_pachner_32(raw,result['triangulation'],result['certificate'],check=c)):
            calls=[0]
            def tick():calls[0]+=1
            operation(tick);total=calls[0]
            for stop in (1,total//2,total):
                calls[0]=0
                def cancel():
                    tick()
                    if calls[0]==stop:raise RuntimeError('cancelled')
                with self.assertRaisesRegex(RuntimeError,'cancelled'):operation(cancel)
        self.assertEqual(raw,saved)
        pair=next(r for row in result['triangulation']['tetrahedra'] for r in row if r is not None)
        pair['permutation'][0]=99
        self.assertEqual(raw,saved)
