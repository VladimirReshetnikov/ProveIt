"""All-dimensional source parallelity, bounded core charts and hostile proofs."""
from collections import Counter
from contextlib import ExitStack
from copy import deepcopy
import json
from pathlib import Path
import random
import unittest
from unittest.mock import patch

from fastunknot.integer_codec import json_safe
from fastunknot.normal_parallelity import normal_cut_parallelity
from fastunknot.normal_parallelity_verify import verify_normal_cut_parallelity
from normal_orbit_research.fixtures import layered_torus
from normal_orbit_research.parallelity import literal_base
from tests.test_normal_surface_orbits import relabel

ROOT=Path(__file__).resolve().parents[2]

def profiles(summary):
    result=Counter()
    for p in summary['base_profiles']:
        result[(p['euler_characteristic'],p['boundary_components'],p['orientable'],*p['handles'],p['original_boundary_edges'],tuple(p['core_ports']))]+=p['multiplicity']
    return result


class ParallelityTests(unittest.TestCase):
    def checked(self,raw,rows):
        a=normal_cut_parallelity(raw,rows,record_certificate=True)
        self.assertEqual(a['status'],'COMPLETE')
        self.assertTrue(verify_normal_cut_parallelity(raw,rows,a['certificate']))
        b=literal_base(a['geometry'],max_points=50000)
        self.assertEqual(profiles(a['summary']),b['profiles'])
        self.assertEqual(a['summary']['attachment_euler_characteristic'],b['attachment_euler_characteristic'])
        self.assertLessEqual(sum(a['summary']['core_handle_counts']),30*len(rows))
        return a

    def test_layered_meridians_include_face_and_edge_handles(self):
        for t in (1,2,4,8):
            raw,base=layered_torus(t)
            for n in (0,1,2,5):
                a=self.checked(raw,[[n*x for x in row]for row in base])
                if n:
                    self.assertEqual(a['summary']['core_euler_characteristic'],1)
                    self.assertTrue(all(p['orientable'] and p['genus']==0 for p in a['summary']['base_profiles']))
                    self.assertEqual(a['summary']['core_handle_counts'],[4*t,6*t-3,2*t-2,0])
                if t>1 and n>1:
                    self.assertEqual({p['kind']for p in a['geometry']['polygons']},{'prism','face_strip','edge_cap'})

    def test_one_sided_fibre_cover_distinguishes_annuli_and_mobius_bands(self):
        raw,_=layered_torus(1)
        for n in range(1,10):
            a=self.checked(raw,[[0,0,0,0,0,n,0]])
            got=Counter()
            for p in a['summary']['base_profiles']:got[(p['orientable'],p['boundary_components'])]+=p['multiplicity']
            expected=Counter({(True,2):(n-1)//2})
            if n%2==0:expected[(False,1)]=1
            self.assertEqual(+got,+expected)

    def test_rich_sources_and_interior_core_three_handles(self):
        bank=json.loads((ROOT/'synthesis/data/cut-complement-audit.json').read_text())['source_proofs']
        prefixes=('interior_1_2/','finite_trefoil/','finite_figureEight/','solid_torus_sum_rp3/','solid_torus_sum_s2xs1/')
        for c in bank:
            if c['id'].startswith(prefixes):self.checked(c['triangulation'],c['coordinates'])
        c=next(c for c in bank if c['id']=='interior_1_2/0')
        self.assertTrue(normal_cut_parallelity(c['triangulation'],c['coordinates'])['geometry']['core']['handles3'])

    def test_relabelled_source_rank_and_self_face_flags(self):
        rng=random.Random(2610127)
        for t in (1,2,4):
            raw,base=layered_torus(t);rows=[[3*x for x in row]for row in base]
            for _ in range(6):
                changed,vector=relabel(raw,rows,rng);self.checked(changed,vector)

    def test_large_binary_multiplicity_and_independent_source_replay(self):
        raw,base=layered_torus(1);n=1<<16384;rows=[[n*x for x in row]for row in base]
        a=normal_cut_parallelity(raw,rows,record_certificate=True)
        self.assertEqual(a['summary']['bundle_components'],n-1)
        self.assertEqual(a['summary']['core_handle_counts'],[4,3,0,0])
        self.assertLess(len(a['geometry']['polygons']),10)
        proof=json.loads(json.dumps(json_safe(a['certificate'])))
        disabled=('fastunknot.normal_parallelity.normal_cut_parallelity','fastunknot.normal_parallelity._parallelity_geometry',
                  'fastunknot.normal_parallelity._systems','fastunknot.normal_parallelity._summary',
                  'fastunknot.normal_cut_boundary._cycle_recipes','fastunknot.weighted_transversal._tagged_replay')
        with ExitStack() as stack:
            for name in disabled:stack.enter_context(patch(name,side_effect=AssertionError('producer used')))
            self.assertTrue(verify_normal_cut_parallelity(raw,json_safe(rows),proof))
        with self.assertRaises(ValueError):literal_base(a['geometry'])

    def test_forged_source_gluings_core_ports_and_summary(self):
        raw,base=layered_torus(2);rows=[[3*x for x in row]for row in base]
        proof=normal_cut_parallelity(raw,rows,record_certificate=True)['certificate'];bad=[]
        for key,value in (('schema','wrong'),('input_sha256','0'*64),('summary',None)):
            p=deepcopy(proof);p[key]=value;bad.append(p)
        p=deepcopy(proof);p['geometry']['gluings'][0]['fibre_flip']^=True;bad.append(p)
        p=deepcopy(proof);p['geometry']['gluings'][0]['ends_reverse']^=True;bad.append(p)
        p=deepcopy(proof);p['geometry']['core']['handles1'][0]['ends'].reverse();p['geometry']['core']['handles1'][0]['ends'][0]+=1;bad.append(p)
        p=deepcopy(proof);p['geometry']['ports'][0]['core_handle']+=1;bad.append(p)
        p=deepcopy(proof);p['summary']['base_profiles'][0]['orientable']=False;bad.append(p)
        p=deepcopy(proof);p['summary']['core_euler_characteristic']=True;bad.append(p)
        for p in bad:self.assertFalse(verify_normal_cut_parallelity(raw,rows,p))
        self.assertFalse(verify_normal_cut_parallelity(raw,base,proof))

    def test_shared_discovery_and_verification_caps(self):
        raw,rows=layered_torus(2);a=normal_cut_parallelity(raw,rows,record_certificate=True)
        cycles=sum(s['orbit_cycles']for s in a['stats'].values())
        for cap in (0,cycles-1):
            b=normal_cut_parallelity(raw,rows,max_cycles=cap,record_certificate=True)
            self.assertEqual(b['status'],'INCONCLUSIVE')
            for key in ('geometry','summary','certificate'):self.assertNotIn(key,b)
        self.assertEqual(normal_cut_parallelity(raw,rows,max_cycles=cycles)['summary'],a['summary'])
        proof=a['certificate'];operations=0
        for field in ('vertex_selector','boundary_selector','polygon_weights','fibre_cover'):
            p=proof[field]
            if field.endswith('selector'):p=p['weighted_certificate']
            operations+=len(p['orbit_proof']['operations'])
        self.assertFalse(verify_normal_cut_parallelity(raw,rows,proof,max_operations=operations-1))
        self.assertTrue(verify_normal_cut_parallelity(raw,rows,proof,max_operations=operations))

    def test_cancellation_and_source_aliasing(self):
        raw,rows=layered_torus(2);source,vector=deepcopy(raw),deepcopy(rows)
        a=normal_cut_parallelity(raw,rows,record_certificate=True)
        raw['tetrahedra'][0][0]['permutation'].reverse();rows[0][0]+=1
        self.assertEqual(a['geometry']['source'],source);self.assertEqual(a['geometry']['coordinates'],vector)
        class Cancel:
            def __bool__(self):return False
            def __call__(self):raise ValueError('cancelled')
        with self.assertRaisesRegex(ValueError,'cancelled'):normal_cut_parallelity(source,vector,check=Cancel())
        with self.assertRaisesRegex(ValueError,'cancelled'):verify_normal_cut_parallelity(source,vector,a['certificate'],check=Cancel())

if __name__=='__main__':unittest.main()
