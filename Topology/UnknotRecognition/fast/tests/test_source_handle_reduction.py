"""Geometric cancellation multiplicities, cocore discs and original-source binding."""
from contextlib import ExitStack
from copy import deepcopy
import importlib.util
import json
from pathlib import Path
import random
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

from fastunknot import Diagram, recognize
from fastunknot.normal_seed import normal_seed_decide
from fastunknot.normal_seed_verify import verify_normal_seed_certificate
from fastunknot.source_handle_reduction import reduce_source_handles
from fastunknot.source_handle_reduction_verify import verify_source_handle_reduction
from normal_orbit_research.fixtures import layered_torus,regina_triangulation
from tests.test_normal_components import relabel
from tests.test_normal_seed import OPTIONS

ROOT=Path(__file__).resolve().parents[2]
BANK=json.loads((ROOT/'reports/57/results/discovery_corpus.json').read_text())['records']


class SourceHandleTests(unittest.TestCase):
    def checked(self,raw):
        result=reduce_source_handles(raw,record_certificate=True)
        self.assertTrue(verify_source_handle_reduction(raw,result['certificate']))
        a,b=result['summary']['initial_handle_counts'],result['summary']['remaining_handle_counts']
        self.assertEqual(sum((-1)**i*x for i,x in enumerate(a)),sum((-1)**i*x for i,x in enumerate(b)))
        self.assertEqual(b[3],0)
        self.assertEqual(sum(a)-sum(b),2*len(result['moves']))
        return result

    def test_layered_tori_reduce_to_a_graph_with_one_cycle(self):
        for t in (1,2,4,8,16,32,128):
            raw,_=layered_torus(t);r=self.checked(raw)
            self.assertEqual(r['summary']['remaining_handle_counts'],[t,t,0,0])
            self.assertIsNotNone(r['compressing_disc'])

    def test_all_saved_sources_and_interior_three_handle_elimination(self):
        for c in BANK:
            r=self.checked(c['triangulation'])
            if c['id'].startswith('finite_'):self.assertIsNone(r['compressing_disc'],c['id'])
            else:self.assertIsNotNone(r['compressing_disc'],c['id'])
            if c['id'].startswith('interior_'):self.assertGreater(r['stats']['cancelled_23'],0)

    def test_relabellings_preserve_positive_and_negative_source_results(self):
        rng=random.Random(26101211)
        for name in ('fibonacci_lst_04','interior_1_2','finite_trefoil','finite_figureEight_interior'):
            raw=next(c['triangulation']for c in BANK if c['id']==name)
            for _ in range(12):
                changed,_=relabel(raw,[[0]*7 for _ in raw['tetrahedra']],rng);r=self.checked(changed)
                if name.startswith('finite_'):self.assertIsNone(r['compressing_disc'])
                else:self.assertIsNotNone(r['compressing_disc'])

    def test_source_replay_without_producers_and_discovery(self):
        raw=next(c['triangulation']for c in BANK if c['id']=='interior_1_2');r=self.checked(raw)
        names=('fastunknot.source_handle_reduction.reduce_source_handles','fastunknot.source_handle_reduction._source_handles',
               'fastunknot.normal_parallelity_geometry._parallelity_geometry','fastunknot.normal_parallelity_geometry._edge_links')
        with ExitStack()as stack:
            for name in names:stack.enter_context(patch(name,side_effect=AssertionError('producer used')))
            self.assertTrue(verify_source_handle_reduction(raw,r['certificate']))

    def test_forged_moves_remaining_handles_and_cocore_path(self):
        raw=next(c['triangulation']for c in BANK if c['id']=='interior_1_2');proof=self.checked(raw)['certificate'];bad=[]
        for key,value in (('input_sha256','0'*64),('boundary_pattern','nonempty'),('summary',{})):
            p=deepcopy(proof);p[key]=value;bad.append(p)
        p=deepcopy(proof);p['moves'][0]['three_handle']=True;bad.append(p)
        p=deepcopy(proof);p['moves'][0]['two_handle']=-1;bad.append(p)
        p=deepcopy(proof);p['moves'].reverse();bad.append(p)
        p=deepcopy(proof);p['moves'].append(deepcopy(p['moves'][-1]));bad.append(p)
        p=deepcopy(proof);p['remaining']['one_handles'].pop();bad.append(p)
        p=deepcopy(proof);p['compressing_disc']['connecting_path']=[dict(one_handle=p['compressing_disc']['one_handle'],forward=True)];bad.append(p)
        p=deepcopy(proof);p['compressing_disc']['boundary_witness']['period']=0;bad.append(p)
        p=deepcopy(proof);p['compressing_disc']['boundary_witness']['dual_values'][0]+=1;bad.append(p)
        p=deepcopy(proof);p['compressing_disc']['boundary_witness']['corner_potentials'][0][0]+=1;bad.append(p)
        p=deepcopy(proof);p['compressing_disc']['boundary_witness']['boundary_cycle'][0]['forward']^=True;bad.append(p)
        for p in bad:self.assertFalse(verify_source_handle_reduction(raw,p))
        other,_=layered_torus(1);self.assertFalse(verify_source_handle_reduction(other,proof))

    def test_geometric_occurrences_are_not_algebraic_coefficients(self):
        raw=next(c['triangulation']for c in BANK if c['id']=='solid_torus_sum_rp3');r=self.checked(raw)
        edge=next(e for e in r['source_handles']['two_handles']if e['id']==9)
        signs=[1 if x['forward']else -1 for x in edge['attaching_cycle']if x['one_handle']==3]
        self.assertEqual(signs,[1,-1])
        p=deepcopy(r['certificate']);p['moves']=[dict(kind='cancel_12',one_handle=3,two_handle=9)]
        self.assertFalse(verify_source_handle_reduction(raw,p))
        # A unit coefficient in one relator does not permit dropping another
        # relator's use of that handle without supplying a handle slide.
        raw=next(c['triangulation']for c in BANK if c['id']=='finite_trefoil');r=self.checked(raw)
        degree={}
        for e in r['source_handles']['two_handles']:
            for x in e['attaching_cycle']:degree[x['one_handle']]=degree.get(x['one_handle'],0)+1
        selected=None
        for e in r['source_handles']['two_handles']:
            for f in degree:
                if sum(x['one_handle']==f for x in e['attaching_cycle'])==1 and degree[f]>1:selected=f,e['id'];break
            if selected:break
        self.assertIsNotNone(selected)
        p=deepcopy(r['certificate']);p['moves']=[dict(kind='cancel_12',one_handle=selected[0],two_handle=selected[1])]
        self.assertFalse(verify_source_handle_reduction(raw,p))

    def test_caps_and_cancellation_never_emit_partial_disc_claims(self):
        raw,_=layered_torus(8);full=self.checked(raw);count=len(full['moves'])
        for cap in (0,count-1):
            r=reduce_source_handles(raw,max_moves=cap,record_certificate=True)
            self.assertEqual(r['status'],'INCONCLUSIVE');self.assertNotIn('certificate',r);self.assertNotIn('compressing_disc',r)
        self.assertEqual(reduce_source_handles(raw,max_moves=count)['remaining'],full['remaining'])
        self.assertFalse(verify_source_handle_reduction(raw,full['certificate'],max_moves=count-1))
        class Stop:
            def __bool__(self):return False
            def __call__(self):raise RuntimeError('cancelled')
        with self.assertRaisesRegex(RuntimeError,'cancelled'):reduce_source_handles(raw,check=Stop())
        with self.assertRaisesRegex(RuntimeError,'cancelled'):verify_source_handle_reduction(raw,full['certificate'],check=Stop())
        for cap in (-1,True):
            with self.assertRaises(ValueError):reduce_source_handles(raw,max_moves=cap)

    def test_native_seed_and_recognizer_integration(self):
        d=Diagram.from_braid(3,[1,-2])
        with patch('fastunknot.normal_seed._rank_one_cocycle_seed_details',side_effect=AssertionError('cocycle used')):
            result=normal_seed_decide(d,handles=True);self.assertEqual(result['method'],'native-handle-cocore')
        self.assertTrue(verify_normal_seed_certificate(d,result['certificate']))
        with patch('fastunknot.source_handle_reduction.reduce_source_handles',side_effect=AssertionError('discovery used')):
            self.assertTrue(verify_normal_seed_certificate(d,result['certificate']))
        verdict=recognize(d,normal_seed_handles=True,**OPTIONS)
        self.assertEqual(verdict.status,'UNKNOT');self.assertEqual(verdict.method,'native-handle-cocore')
        bad=deepcopy(result['certificate']);bad['handle_certificate']['compressing_disc']=None
        self.assertFalse(verify_normal_seed_certificate(d,bad))
        self.assertFalse(verify_normal_seed_certificate(Diagram.from_braid(2,[1,1,1]),result['certificate']))
        with self.assertRaises(ValueError):normal_seed_decide(d,handles=1)

    def test_cli_handle_stage_and_strict_option(self):
        d=Diagram.from_braid(2,[1])
        with tempfile.TemporaryDirectory()as directory:
            path=Path(directory)/'curl.json';path.write_text(json.dumps(dict(pd=d.pd)))
            output=subprocess.check_output([sys.executable,'-B','-m','fastunknot','recognize',str(path),
                '--normal-seed','--normal-seed-handles','--no-seifert','--no-reduction','--no-descending'],text=True)
        r=json.loads(output);self.assertEqual(r['method'],'native-handle-cocore')
        self.assertTrue(verify_normal_seed_certificate(d,r['evidence']['normal_seed']['certificate']))
        with self.assertRaises(ValueError):recognize(d,normal_seed_handles=1)

    def test_boundary_period_encoding_and_incompressible_reducible_control(self):
        raw,_=layered_torus(128);r=self.checked(raw);p=deepcopy(r['certificate']);w=p['compressing_disc']['boundary_witness']
        self.assertGreater(max(abs(x).bit_length()for x in w['dual_values']),80)
        w['dual_values']=[hex(x)for x in w['dual_values']]
        w['corner_potentials']=[[hex(x)for x in row]for row in w['corner_potentials']];w['period']=hex(w['period'])
        self.assertTrue(verify_source_handle_reduction(raw,p))
        w['period']=True;self.assertFalse(verify_source_handle_reduction(raw,p))
        control=json.loads((ROOT/'synthesis/data/handle-reducible-trefoil.json').read_text())
        self.assertIsNone(self.checked(control)['compressing_disc'])

    def test_shared_seed_budget_and_miss_fallback(self):
        d=Diagram.from_braid(3,[1,-2]);r=normal_seed_decide(d,handles=True)
        for cap in (0,r['work']-1):self.assertEqual(normal_seed_decide(d,handles=True,max_work=cap)['status'],'INCONCLUSIVE')
        self.assertEqual(normal_seed_decide(d,handles=True,max_work=r['work'])['status'],'UNKNOT')
        knot=normal_seed_decide(Diagram.from_braid(2,[1,1,1]),handles=True,optimize=False,tree_trials=0)
        self.assertEqual(knot['status'],'INCONCLUSIVE');self.assertIn('cocycle',knot['stats'])

    @unittest.skipUnless(importlib.util.find_spec('regina'),'Regina supplies an independent disc oracle')
    def test_regina_disc_oracle_and_reducible_non_solid_torus_controls(self):
        for c in BANK:
            r=self.checked(c['triangulation']);tri=regina_triangulation(c['triangulation'])
            self.assertEqual(r['compressing_disc']is not None,tri.hasCompressingDisc(),c['id'])
            if c['id'].startswith('solid_torus_sum_'):
                self.assertFalse(tri.isSolidTorus());self.assertNotIn('unknot',r);self.assertNotIn('solid_torus',r)

if __name__=='__main__':unittest.main()
