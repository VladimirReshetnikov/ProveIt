"""Check the retriangulation proof and the entire one-vertex cocycle family."""
from copy import deepcopy
import json
from pathlib import Path
import random
import unittest
from unittest.mock import patch

from fastunknot.coherent_family_verify import inspect_one_vertex_family
from fastunknot.integer_codec import json_safe
from fastunknot.normal_cocycle import CocycleLimit
from fastunknot.normal_surface_geometry import NormalOrbitError, _prepare
from fastunknot.pachner23 import pachner_23
from fastunknot.pachner23_verify import verify_pachner_23
from normal_orbit_research.coherent_obstruction import family_proof, replay, reproduce
from normal_orbit_research.fixtures import layered_torus, boundary_cap
from tests.test_normal_surface_orbits import relabel

RECORD = Path(__file__).resolve().parents[2]/'synthesis/data/coherent-obstruction-certificate.json'


class CoherentObstructionTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.record = json.loads(RECORD.read_text())
        cls.raw = cls.record['moves'][-1]['triangulation']
        cls.proof = cls.record['family_certificate']

    def test_exact_reproduction_and_producer_free_replay(self):
        self.assertEqual(reproduce(),self.record)
        with patch('fastunknot.pachner23.pachner_23',side_effect=AssertionError), \
             patch('fastunknot.normal_cocycle._rank_one_cocycle_seed_details',side_effect=AssertionError), \
             patch('normal_orbit_research.coherent_obstruction.pachner_23',side_effect=AssertionError), \
             patch('normal_orbit_research.coherent_obstruction._rank_one_cocycle_seed_details',side_effect=AssertionError), \
             patch('normal_orbit_research.coherent_obstruction.normal_surface_topology',side_effect=AssertionError), \
             patch('normal_orbit_research.coherent_obstruction.normal_compressing_disk_count',side_effect=AssertionError), \
             patch('normal_orbit_research.coherent_obstruction.reproduce',side_effect=AssertionError), \
             patch('normal_orbit_research.coherent_obstruction.family_proof',side_effect=AssertionError):
            self.assertEqual(replay(self.record),self.raw)
        self.assertEqual(_prepare(self.raw,lambda:None)['vertices'],1)

    def test_rank_minor_and_strict_certificate_fields(self):
        for key in self.proof:
            bad=deepcopy(self.proof);del bad[key]
            self.assertIsNone(inspect_one_vertex_family(self.raw,bad))
        for key,value in [('extra',0),('schema','wrong'),('determinant',0),('determinant',-1),
                          ('determinant',True),('minor_rows',[0]*9),('minor_columns',[0]*9),
                          ('minor_rows',[True]+list(range(8))),('minor_columns',list(range(1,11))),
                          ('heights',[]),('coordinates',None)]:
            self.assertIsNone(inspect_one_vertex_family(self.raw,dict(self.proof,**{key:value})))
        for key in ('heights','coordinates'):
            bad=deepcopy(self.proof);bad[key][0][0]+=1
            self.assertIsNone(inspect_one_vertex_family(self.raw,bad))
        doubled=deepcopy(self.proof)
        for key in ('heights','coordinates'):
            doubled[key]=[[2*x for x in row] for row in doubled[key]]
        self.assertIsNone(inspect_one_vertex_family(self.raw,doubled))
        multi,_=boundary_cap(*layered_torus(2))
        self.assertIsNone(inspect_one_vertex_family(multi,family_proof(multi)))

    def test_sign_offsets_and_huge_binary_transport(self):
        saved=deepcopy(self.proof)
        for sign in (1,-1):
            proof=deepcopy(self.proof)
            proof['heights']=[[sign*x+(t+1)*(1<<20000) for x in row]
                              for t,row in enumerate(proof['heights'])]
            proof=json.loads(json.dumps(json_safe(proof)))
            self.assertEqual(inspect_one_vertex_family(self.raw,proof),self.record['family_summary'])
        self.assertEqual(self.proof,saved)

    def test_relabelled_entire_families(self):
        rng=random.Random(261009513)
        for _ in range(20):
            raw,_=relabel(self.raw,self.proof['coordinates'],rng)
            proof=family_proof(raw)
            self.assertEqual(inspect_one_vertex_family(raw,proof),self.record['family_summary'])

    def test_move_mutations_and_invalid_sites(self):
        before=self.record['initial']
        for move in self.record['moves']:
            after,proof=move['triangulation'],move['certificate']
            self.assertTrue(verify_pachner_23(before,after,proof))
            for bad in (None,{},dict(proof,extra=0),dict(proof,tetrahedron=True),
                        dict(proof,tetrahedron=-1),dict(proof,tetrahedron=len(before['tetrahedra'])),
                        dict(proof,face=True),dict(proof,face=4),dict(proof,schema='wrong')):
                self.assertFalse(verify_pachner_23(before,after,bad))
            for bad in ({},dict(after,extra=0),before):
                self.assertFalse(verify_pachner_23(before,bad,proof))
            # A valid manifold of the correct size still needs the exact boundary map.
            changed,_=relabel(after,[[0]*7 for _ in after['tetrahedra']],random.Random(42))
            self.assertFalse(verify_pachner_23(before,changed,proof))
            for t,row in enumerate(after['tetrahedra']):
                for f,r in enumerate(row):
                    if r is None:continue
                    bad=deepcopy(after);bad['tetrahedra'][t][f]=None
                    self.assertFalse(verify_pachner_23(before,bad,proof))
            before=after
        raw,_=layered_torus(1)
        for f in range(4):
            with self.assertRaises(NormalOrbitError):pachner_23(raw,0,f)
        for t,f in ((True,0),(-1,0),(1,0),(0,True),(0,-1),(0,4)):
            with self.assertRaises(ValueError):pachner_23(raw,t,f)

    def test_budget_cancellation_and_no_input_mutation(self):
        raw=self.record['initial'];saved=deepcopy(raw)
        result=pachner_23(raw,1,2)
        self.assertEqual(pachner_23(raw,1,2,max_work=result['stats']['work']),result)
        with self.assertRaises(CocycleLimit):pachner_23(raw,1,2,max_work=result['stats']['work']-1)
        operations=(lambda c:pachner_23(raw,1,2,check=c),
                    lambda c:verify_pachner_23(raw,result['triangulation'],result['certificate'],check=c),
                    lambda c:inspect_one_vertex_family(self.raw,self.proof,check=c))
        for operation in operations:
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
        record=next(r for row in result['triangulation']['tetrahedra'] for r in row if r is not None)
        record['permutation'][0]=99
        self.assertEqual(raw,saved)


if __name__ == '__main__':
    unittest.main()
