"""Progress-driven discovery keeps complete coverage and one shared ray cap."""
from copy import deepcopy
from itertools import product
import json
from pathlib import Path
import unittest
from unittest.mock import patch

from fastunknot import normal_sector as sector
from fastunknot.sector_planar import sector_planar_discovery_rays,sector_planar_rays
from fastunknot.normal_sector_verify import verify_sector_exhaustion,verify_sector_witness
from planar_sector_research.fixtures import double_capped_fibonacci,vector_key

CORPUS=Path(__file__).resolve().parents[2]/'reports/57/results/discovery_corpus.json'


def frozen_source(name):
    return next(r['triangulation']for r in json.loads(CORPUS.read_text())['records']if r['id']==name)


class AdaptivePlanarTests(unittest.TestCase):
    def test_early_disc_never_constructs_a_minimum_overlay(self):
        for n in (1,4,8):
            f=double_capped_fibonacci(n)
            with patch('fastunknot.sector_planar._minimum_overlay',side_effect=AssertionError('eager overlay')):
                r=sector.discover_in_sector(f['triangulation'],f['allowed_types'],phase='standard',max_bases=1)
            self.assertEqual(r['status'],'DISC_FOUND')
            self.assertTrue(verify_sector_witness(f['triangulation'],r['certificate']))
            self.assertEqual(r['stats']['overlay_refinements'],0)
            self.assertEqual(r['stats']['corner_rays'],1)
            self.assertEqual(r['stats']['bases_attempted'],1)

    def test_resumed_stream_is_complete_unique_and_keeps_enumeration_order(self):
        f=double_capped_fibonacci(1)
        for kinds in product(range(4),repeat=3):
            allowed=[(i,q)for i,q in enumerate(kinds)if q<3]
            k=sector.build_sector_kernel(f['triangulation'],allowed)
            old=list(sector_planar_rays(k));stats={}
            new=list(sector_planar_discovery_rays(k,stats=stats))
            self.assertEqual({vector_key(r)for r in old},{vector_key(r)for r in new})
            self.assertEqual(len(new),len(old))
            self.assertEqual(list(sector_planar_rays(k)),old)
            self.assertEqual(stats['bases_attempted'],len(new))

    def test_negative_fallback_replays_and_cap_spans_both_stages(self):
        raw=frozen_source('fibonacci_lst_06')
        allowed=[(0,0),(1,2),(2,1),(3,0),(4,2),(5,1)]
        answer=sector.discover_in_sector(raw,allowed,phase='standard',max_bases=7)
        self.assertEqual(answer['status'],'NO_POSITIVE_EULER')
        self.assertEqual(answer['stats']['corner_rays'],3)
        self.assertEqual(answer['stats']['overlay_refinements'],1)
        self.assertEqual(len(answer['certificate']['rays']),7)
        self.assertTrue(verify_sector_exhaustion(raw,answer['certificate']))
        for cap in (0,1,3,6):
            partial=sector.discover_in_sector(raw,allowed,phase='standard',max_bases=cap)
            self.assertEqual(partial['status'],'INCONCLUSIVE')
            self.assertNotIn('certificate',partial)
            self.assertEqual(partial['stats']['bases_attempted'],cap)
        for i in range(7):
            missing=deepcopy(answer['certificate']);missing['rays'].pop(i)
            self.assertFalse(verify_sector_exhaustion(raw,missing))

    def test_cancellation_can_stop_between_corner_and_overlay_stages(self):
        f=double_capped_fibonacci(1);k=sector.build_sector_kernel(f['triangulation'],f['allowed_types'])
        state={'cancel':False}
        class Stop:
            def __bool__(self):return False
            def __call__(self):
                if state['cancel']:raise ValueError('tail cancelled')
        g=sector_planar_discovery_rays(k,check=Stop())
        for _ in range(3):next(g)
        state['cancel']=True
        with self.assertRaisesRegex(ValueError,'tail cancelled'):next(g)

    def test_sparse_search_reuses_the_kernel_across_a_failed_Q_phase(self):
        raw=deepcopy(frozen_source('finite_trefoil_interior'))
        t,f=next((t,f)for t,row in enumerate(raw['tetrahedra'])for f,value in enumerate(row)if value is None)
        new=len(raw['tetrahedra']);raw['tetrahedra'][t][f]={'tetrahedron':new,'permutation':[0,1,2,3]}
        row=[None]*4;row[f]={'tetrahedron':t,'permutation':[0,1,2,3]};raw['tetrahedra'].append(row)
        events=[];build=sector.build_sector_kernel;discover=sector._discover_in_kernel
        def tracked(k,**kwargs):
            r=discover(k,**kwargs);events.append((k,kwargs['phase'],r['status'],kwargs.get('corner_first',True)))
            return r
        with patch.object(sector,'build_sector_kernel',wraps=build)as builds,\
             patch.object(sector,'_discover_in_kernel',side_effect=tracked):
            answer=sector.sparse_disc_search(raw,max_active=1)
        self.assertEqual(answer['status'],'NO_VERTEX_DISC_UP_TO_SUPPORT')
        self.assertEqual(builds.call_count,answer['sectors_visited'])
        tails=[i for i,event in enumerate(events)if event[1]=='standard']
        self.assertTrue(tails)
        for i in tails:
            self.assertIs(events[i][0],events[i-1][0])
            self.assertEqual(events[i-1][2],'POSITIVE_EULER_ONLY')
            self.assertFalse(events[i][3])


if __name__=='__main__':unittest.main()
