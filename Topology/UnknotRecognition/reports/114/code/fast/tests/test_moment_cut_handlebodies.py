"""Moment-boundary integration, shared budgets and source-only independent replay."""
from contextlib import ExitStack
from copy import deepcopy
import json
from pathlib import Path
import unittest
from unittest.mock import patch
from fastunknot.normal_cut_handlebodies import normal_cut_handlebodies
from fastunknot.normal_cut_handlebodies_verify import verify_normal_cut_handlebodies
from normal_orbit_research.fixtures import layered_torus
BANK=json.loads((Path(__file__).parents[1]/'marked_parallelity_research/corpus.json').read_text())['cases']


def operations(proof):
    total=0
    for name in ('vertex_selector','boundary_selector','polygon_weights','fibre_cover'):
        part=proof['parallelity'][name]
        if name.endswith('selector'):part=part['weighted_certificate']
        total+=len(part['orbit_proof']['operations'])
    if proof['boundary']['census'] is not None:
        total+=len(proof['boundary']['census']['orbit_proof']['operations'])
    return total


class MomentCutHandlebodyTests(unittest.TestCase):
    def test_whole_cut_reuses_geometry_and_retains_all_census_fields(self):
        for name in ('pilot/lst_4_7/0','interior_1_2/mixed','fibonacci_lst_09/mixed'):
            c=next(c for c in BANK if c['id']==name);args=c['triangulation'],c['coordinates']
            old=normal_cut_handlebodies(*args,record_certificate=True)
            with patch('fastunknot.parallelity_boundary_moments._parallelity_geometry',side_effect=AssertionError('geometry rebuilt')):
                new=normal_cut_handlebodies(*args,record_certificate=True,boundary_method='moments')
            self.assertEqual(old['census'],new['census'])
            self.assertTrue(verify_normal_cut_handlebodies(*args,new['certificate']))
            self.assertTrue(verify_normal_cut_handlebodies(*args,old['certificate']))
            self.assertEqual(new['certificate']['boundary']['schema'],'native-moment-boundary-v2')
            self.assertEqual(new['stats']['boundary']['compilation']['weighted_calls'],1)

    def test_shared_five_trace_operation_and_cycle_budgets(self):
        c=next(c for c in BANK if c['id']=='interior_1_2/mixed');args=c['triangulation'],c['coordinates']
        full=normal_cut_handlebodies(*args,boundary_method='moments',record_certificate=True)
        proof=full['certificate'];size=operations(proof)
        self.assertGreater(size,0)
        self.assertTrue(verify_normal_cut_handlebodies(*args,proof,max_operations=size))
        self.assertFalse(verify_normal_cut_handlebodies(*args,proof,max_operations=size-1))
        cycles=sum(s['orbit_cycles'] for s in full['stats']['parallelity'].values())+full['stats']['boundary']['census']['orbit_cycles']
        exact=normal_cut_handlebodies(*args,boundary_method='moments',max_cycles=cycles,record_certificate=True)
        self.assertEqual(exact['certificate'],proof)
        for cap in (0,cycles-1):
            limited=normal_cut_handlebodies(*args,boundary_method='moments',max_cycles=cap,record_certificate=True)
            self.assertEqual(limited['status'],'INCONCLUSIVE');self.assertNotIn('certificate',limited)

    def test_independent_whole_replay_and_hostile_moment_proof(self):
        c=next(c for c in BANK if c['id']=='interior_1_2/mixed');args=c['triangulation'],c['coordinates']
        p=normal_cut_handlebodies(*args,boundary_method='moments',record_certificate=True)['certificate']
        names=('fastunknot.normal_cut_handlebodies._compile_moment_boundary',
               'fastunknot.parallelity_boundary_moments._moment_query',
               'fastunknot.parallelity_boundary_moments._assemble',
               'fastunknot.parallelity_boundary_moments.weighted_orbit_histogram')
        with ExitStack() as stack:
            for name in names:stack.enter_context(patch(name,side_effect=AssertionError('producer used')))
            self.assertTrue(verify_normal_cut_handlebodies(*args,p))
        for mutate in (lambda b:b.update(codec='unknown'),lambda b:b.update(schema='parallelity-boundary-words-v1'),
                       lambda b:b['skeleton']['gaps'][0].update(unmarked_edges=True),
                       lambda b:b['skeleton']['gaps'][0].update(unmarked_edges=999999),
                       lambda b:b['census']['histogram'][0].update(orbits=False)):
            bad=deepcopy(p);mutate(bad['boundary']);self.assertFalse(verify_normal_cut_handlebodies(*args,bad))

    def test_port_free_source_and_recordless_call(self):
        raw,_=layered_torus(1);rows=[[0]*7]
        r=normal_cut_handlebodies(raw,rows,boundary_method='moments',record_certificate=True)
        self.assertIsNone(r['certificate']['boundary']['census'])
        self.assertTrue(verify_normal_cut_handlebodies(raw,rows,r['certificate'],max_operations=operations(r['certificate'])))
        other=normal_cut_handlebodies(raw,rows,boundary_method='moments')
        self.assertEqual(other['census'],r['census']);self.assertNotIn('certificate',other)

    def test_invalid_method_and_cancellation_are_not_silent_fallbacks(self):
        raw,rows=layered_torus(2)
        for method in (True,None,[],{},'four','auto'):
            with self.assertRaises(ValueError):normal_cut_handlebodies(raw,rows,boundary_method=method)
        class Cancel:
            def __bool__(self):return False
            def __call__(self):raise RuntimeError('cancelled')
        with self.assertRaisesRegex(RuntimeError,'cancelled'):
            normal_cut_handlebodies(raw,rows,boundary_method='moments',check=Cancel())


if __name__=='__main__':unittest.main()
