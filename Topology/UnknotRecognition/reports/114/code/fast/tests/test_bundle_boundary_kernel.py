"""Source-bound whole-cut kernel and expanded omitted-column checks."""
from collections import Counter
from contextlib import ExitStack
from copy import deepcopy
import json
from pathlib import Path
import random
import unittest
from unittest.mock import patch

from fastunknot.bundle_boundary_kernel_verify import replay_bundle_boundary_kernel
from fastunknot.integer_codec import json_safe
from fastunknot.normal_cut_handlebodies import normal_cut_handlebodies
from fastunknot.normal_cut_handlebodies_verify import verify_normal_cut_handlebodies
from tests.test_normal_surface_orbits import relabel


class BundleBoundaryKernelTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        bank=json.loads((Path(__file__).parents[1]/'marked_parallelity_research/corpus.json').read_text())['cases']
        cls.examples=[c for c in bank if c['id'] in ('fibonacci_lst_09/mixed','fibonacci_lst_10/mixed')]
        cls.results=[normal_cut_handlebodies(c['triangulation'],c['coordinates'],record_certificate=True) for c in cls.examples]

    def test_two_source_censuses_match_literal_cuts(self):
        from marked_parallelity_research.benchmark_census import explicit
        for c,a in zip(self.examples,self.results):
            self.assertEqual(a['status'],'COMPLETE')
            self.assertEqual(a['certificate']['schema'],'normal-cut-handlebodies-v5')
            self.assertTrue(verify_normal_cut_handlebodies(c['triangulation'],c['coordinates'],a['certificate']))
            oracle,_=explicit(c['triangulation'],c['coordinates'])
            self.assertEqual(a['census']['histogram'],oracle['histogram'])
            self.assertEqual(a['census']['histogram'][0],dict(genus=0,multiplicity=1))

    def test_all_boundary_and_spare_boundary_templates(self):
        for a in self.results:
            p=a['certificate']; profiles=p['parallelity']['summary']['base_profiles']; kinds=set()
            for f in p['kernel']['families']:
                b=profiles[f['base_profile']]['boundary_components']; n=len(f['annular_attachments'])
                kinds.add(n==b)
                self.assertEqual(len(f['boundary_columns']),min(n,b-1))
            self.assertEqual(kinds,{False,True})
        profiles=self.results[0]['certificate']['parallelity']['summary']['base_profiles']
        self.assertTrue(any(not p['orientable'] for p in profiles if p['core_ports']))

    def test_expanded_implicit_columns_support_every_pivot(self):
        saw_implicit_crossing=False
        for a in self.results:
            p=a['certificate']; k=p['kernel']; core=p['parallelity']['geometry']['core']
            bases=p['parallelity']['summary']['base_profiles']; offset=len(core['handles2']);tree=set(k['forest'])
            rows={h['id']:Counter(f['handle'] for f in h['cycle'] if f['dimension']==1 and f['handle'] not in tree) for h in core['handles2']}
            for c in k['curves']:
                rows[offset+c['attachment']]=Counter(x['handle'] for x in c['crossings'] if x['handle'] not in tree)
            finite=set(range(len(core['handles1'])))-tree
            for f in k['families']:
                annuli=f['annular_attachments']; columns=f['boundary_columns']; finite.update(columns)
                for i,h in zip(annuli,columns):rows[offset+i][h]=1
                if len(annuli)==bases[f['base_profile']]['boundary_components']:
                    for h in columns:rows[offset+annuli[-1]][h]=1
            next_column=max(finite,default=-1)+1; implicit=set()
            for f in k['families']:
                annuli=f['annular_attachments']
                for _ in range(f['omitted_genus_columns']):
                    implicit.add(next_column)
                    if len(annuli)==bases[f['base_profile']]['boundary_components']:
                        rows[offset+annuli[-1]][next_column]=2;saw_implicit_crossing=True
                    next_column+=1
            for i,att in enumerate(p['boundary']['skeleton']['attachment_components']):
                if i not in k['bridge_forest']:
                    implicit.add(next_column)
                    if att['kind']=='circle':rows[offset+i][next_column]=2;saw_implicit_crossing=True
                    next_column+=1
            columns=finite|implicit
            for r,c in k['cancellations']:
                self.assertIn(c,finite);self.assertEqual(rows[r][c],1)
                donor=rows.pop(r);columns.remove(c)
                for row in rows.values():
                    coefficient=row.pop(c,0)
                    for h in columns:row[h]+=coefficient*donor[h]
                    self.assertTrue(all(row[h]!=1 for h in implicit))
            self.assertFalse(rows)
            self.assertEqual(len(columns),sum(j['genus'] for j in a['census']['joined_components']))
        self.assertTrue(saw_implicit_crossing)

    def test_hostile_kernel_records(self):
        c=self.examples[0]; original=self.results[0]['certificate']
        mutations=[lambda p:p['kernel']['forest'].pop(),
                   lambda p:p['kernel']['bridge_forest'].pop(),
                   lambda p:p['kernel']['curves'].pop(),
                   lambda p:p['kernel']['curves'][0]['crossings'][0].update(sign=0),
                   lambda p:p['kernel']['families'][0].update(omitted_genus_columns=999),
                   lambda p:p['kernel']['families'][-1]['boundary_columns'].append(999),
                   lambda p:p['kernel']['cancellations'].pop(),
                   lambda p:p['kernel']['cancellations'][0].__setitem__(1,999999),
                   lambda p:p['kernel']['cancellations'][0].__setitem__(0,False),
                   lambda p:p['kernel']['cancellations'].__setitem__(0,p['kernel']['cancellations'][-1]),
                   lambda p:p['census']['histogram'][0].update(genus=1),
                   lambda p:p.update(schema='normal-cut-handlebodies-v4')]
        for mutate in mutations:
            p=deepcopy(original);mutate(p)
            self.assertFalse(verify_normal_cut_handlebodies(c['triangulation'],c['coordinates'],p))

    def test_independent_replay_hex_and_caps(self):
        c=self.examples[0];p=deepcopy(self.results[0]['certificate'])
        p['kernel']['cancellations']=[[hex(r),hex(h)] for r,h in p['kernel']['cancellations']]
        names=('fastunknot.bundle_boundary_kernel.bundle_boundary_kernel',
               'fastunknot.normal_cut_handlebodies.bundle_boundary_kernel',
               'fastunknot.bundle_boundary_kernel.source_core_circle',
               'fastunknot.core_handlebody.capped_cancellation_plan',
               'fastunknot.normal_cut_handlebodies._census')
        with ExitStack() as stack:
            for name in names:stack.enter_context(patch(name,side_effect=AssertionError('producer called')))
            self.assertTrue(verify_normal_cut_handlebodies(c['triangulation'],c['coordinates'],p))
        self.assertFalse(verify_normal_cut_handlebodies(c['triangulation'],c['coordinates'],p,max_operations=0))
        self.assertEqual(normal_cut_handlebodies(c['triangulation'],c['coordinates'],max_cycles=0)['status'],'INCONCLUSIVE')

    def test_endpoint_authentication_and_closed_base_refusal(self):
        p=deepcopy(self.results[0]['certificate']);g=p['parallelity']['geometry'];s=p['parallelity']['summary'];b=p['boundary']['skeleton']
        crossing=p['kernel']['curves'][0]['crossings'][0];port=g['ports'][crossing['port']]
        g['polygons'][port['polygon']]['vertices'][port['edge']]['face']=99
        self.assertIsNone(replay_bundle_boundary_kernel(g,s,b,p['kernel']))
        p=deepcopy(self.results[0]['certificate']);p['parallelity']['summary']['base_profiles'][0]['boundary_components']=0
        self.assertIsNone(replay_bundle_boundary_kernel(p['parallelity']['geometry'],p['parallelity']['summary'],p['boundary']['skeleton'],p['kernel']))

    def test_binary_multiplicity_and_relabelled_sources(self):
        c=self.examples[1];rows=[[(1<<1024)*x for x in row] for row in c['coordinates']]
        a=normal_cut_handlebodies(c['triangulation'],rows,record_certificate=True)
        self.assertEqual(a['status'],'COMPLETE')
        self.assertTrue(verify_normal_cut_handlebodies(c['triangulation'],json_safe(rows),json_safe(a['certificate'])))
        rng=random.Random(852031);successes=0
        for _ in range(3):
            raw,rows=relabel(c['triangulation'],c['coordinates'],rng)
            a=normal_cut_handlebodies(raw,rows,record_certificate=True)
            if a['status']=='COMPLETE':
                successes+=1
                self.assertEqual(a['census']['histogram'],self.results[1]['census']['histogram'])
                self.assertTrue(verify_normal_cut_handlebodies(raw,rows,a['certificate']))
            else:self.assertNotIn('certificate',a)
        self.assertGreater(successes,0)


if __name__=='__main__':unittest.main()
