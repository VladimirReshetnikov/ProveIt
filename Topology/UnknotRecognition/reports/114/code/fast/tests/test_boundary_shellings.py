from copy import deepcopy
import json
import unittest
from unittest.mock import patch
from fastunknot import Diagram, recognize
from fastunknot.diagram_exterior import diagram_exterior
from fastunknot.boundary_shellings import shell_boundary
from fastunknot.boundary_shellings_verify import verify_boundary_shellings
from fastunknot.normal_seed import normal_seed_decide
from fastunknot.normal_seed_verify import verify_normal_seed_certificate
from fastunknot.normal_cocycle import CocycleLimit
from fastunknot.normal_surface_geometry import _prepare
from fastunknot.integer_codec import json_safe
from normal_orbit_research.fixtures import layered_torus

ANNULUS_PD = [[0,0,1,6],[7,1,2,3],[2,4,5,3],[5,4,6,7]]


def remove_one(raw, t):
    rows=deepcopy(raw['tetrahedra'])
    for f,r in enumerate(rows[t]):
        if r is not None:rows[r['tetrahedron']][r['permutation'][f]]=None
    rows.pop(t)
    for row in rows:
        for r in row:
            if r is not None:r['tetrahedron']-=int(r['tetrahedron']>t)
    return dict(tetrahedra=rows)


class BoundaryShellingTests(unittest.TestCase):
    def test_every_prefix_and_immutable_source(self):
        raw=diagram_exterior(Diagram.from_braid(2,[1]));saved=deepcopy(raw)
        full=shell_boundary(raw)
        self.assertEqual(full['stats']['remaining_tetrahedra'],5)
        self.assertEqual([full['stats'][k] for k in ('boundary_one','boundary_two','boundary_three')],[2,12,1])
        for k in range(16):
            result=shell_boundary(raw,max_moves=k)
            self.assertEqual(result['moves'],full['moves'][:k])
            self.assertTrue(verify_boundary_shellings(raw,result['triangulation'],result['moves']))
            _prepare(result['triangulation'],lambda:None)
        self.assertEqual(raw,saved)
        # Generalized tetrahedra with identified corners are deliberately excluded.
        layered,_=layered_torus(8)
        self.assertEqual(shell_boundary(layered)['moves'],[])

    def test_stray_boundary_vertex_is_not_a_shelling(self):
        raw=shell_boundary(diagram_exterior(Diagram.from_braid(2,[1])),max_moves=1)['triangulation']
        p=_prepare(raw,lambda:None);t=3
        self.assertEqual(len(set(p['vertex_roots'][4*t:4*t+4])),4)
        self.assertEqual([f for f,r in enumerate(raw['tetrahedra'][t]) if r is None],[0])
        # Four distinct corners and a nonempty proper union of boundary facets
        # are insufficient: the opposite vertex also touches another boundary face.
        self.assertFalse(verify_boundary_shellings(raw,remove_one(raw,t),[t]))

    def test_trace_and_output_are_strictly_replayed(self):
        raw=diagram_exterior(Diagram.from_braid(2,[1]));r=shell_boundary(raw);after=r['triangulation'];moves=r['moves']
        for bad in (None,tuple(moves),[True],[-1],[20],moves+[moves[0]],moves[1:],list(reversed(moves))):
            self.assertFalse(verify_boundary_shellings(raw,after,bad))
        for bad in ({},dict(after,extra=1),{'tetrahedra':[]},raw):
            self.assertFalse(verify_boundary_shellings(raw,bad,moves))
        changed=deepcopy(after)
        for row in changed['tetrahedra']:
            for item in row:
                if item is not None:
                    item['tetrahedron']=True
                    self.assertFalse(verify_boundary_shellings(raw,changed,moves))
                    return
        self.fail('fixture has no paired face')

    def test_all_three_surface_kinds_and_producer_free_replay(self):
        fixtures=[(Diagram.from_pd([]),False,'disc'),(Diagram.from_pd(ANNULUS_PD),False,'annulus'),
                  (Diagram.from_braid(4,[-1,2,1,-2,3]),True,'planar')]
        for d,planar,kind in fixtures:
            r=normal_seed_decide(d,shellings=True,planar=planar);proof=r['certificate']
            self.assertEqual(proof['surface_certificate']['schema'],f'diagram-cocycle-{kind}-v1')
            with patch('fastunknot.boundary_shellings.shell_boundary',side_effect=AssertionError), \
                 patch('fastunknot.normal_seed.normal_seed_decide',side_effect=AssertionError), \
                 patch('fastunknot.diagram_exterior.diagram_exterior',side_effect=AssertionError), \
                 patch('fastunknot.normal_cocycle.rank_one_cocycle_seed',side_effect=AssertionError), \
                 patch('fastunknot.normal_planar.planar_cap_candidate',side_effect=AssertionError):
                self.assertTrue(verify_normal_seed_certificate(d,proof))
            self.assertFalse(verify_normal_seed_certificate(d,proof['surface_certificate']))
            for row in proof['surface_certificate']['heights']:
                for v in range(4):row[v]+=1<<20000
            self.assertTrue(verify_normal_seed_certificate(d,json.loads(json.dumps(json_safe(proof)))))

    def test_source_binding_and_malformed_envelopes(self):
        d=Diagram.from_pd(ANNULUS_PD);proof=normal_seed_decide(d,shellings=True)['certificate']
        self.assertFalse(verify_normal_seed_certificate(Diagram.from_braid(2,[1,1,1]),proof))
        for field in proof:
            bad=deepcopy(proof);del bad[field]
            self.assertFalse(verify_normal_seed_certificate(d,bad))
        for field,value in [('extra',0),('source_triangulation',{}),('shellings',[]),('surface_certificate',None)]:
            self.assertFalse(verify_normal_seed_certificate(d,dict(proof,**{field:value})))
        for field,value in [('input_pd',[]),('coordinates',[]),('heights',[]),('schema','diagram-cocycle-disc-v1')]:
            bad=deepcopy(proof);bad['surface_certificate'][field]=value
            self.assertFalse(verify_normal_seed_certificate(d,bad))
        self.assertEqual(normal_seed_decide(Diagram.from_braid(2,[1,1,1]),shellings=True)['status'],'INCONCLUSIVE')

    def test_limits_cancellation_and_opt_in_recognition(self):
        d=Diagram.from_pd(ANNULUS_PD);raw=diagram_exterior(d);r=shell_boundary(raw)
        self.assertEqual(shell_boundary(raw,max_work=r['stats']['work']),r)
        with self.assertRaises(CocycleLimit):shell_boundary(raw,max_work=r['stats']['work']-1)
        result=normal_seed_decide(d,shellings=True)
        self.assertEqual(normal_seed_decide(d,shellings=True,max_work=result['work'])['certificate'],result['certificate'])
        self.assertEqual(normal_seed_decide(d,shellings=True,max_work=result['work']-1)['status'],'INCONCLUSIVE')
        self.assertEqual(normal_seed_decide(d),normal_seed_decide(d,shellings=False))
        for operation in (lambda c:shell_boundary(raw,check=c),lambda c:verify_normal_seed_certificate(d,result['certificate'],check=c)):
            calls=[0]
            def tick():calls[0]+=1
            operation(tick);total=calls[0]
            for stop in (1,total//2,total):
                calls[0]=0
                def cancel():
                    tick()
                    if calls[0]==stop:raise RuntimeError('cancelled')
                with self.assertRaisesRegex(RuntimeError,'cancelled'):operation(cancel)
        for value in (0,1,None,'true'):
            with self.assertRaises(ValueError):normal_seed_decide(d,shellings=value)
            with self.assertRaises(ValueError):recognize(d,normal_seed_shellings=value)
        for value in (-1,True,1.5):
            with self.assertRaises(ValueError):shell_boundary(raw,max_moves=value)
        from normal_orbit_research.seeds import FORCED
        answer=recognize(d,**FORCED,normal_seed_shellings=True)
        self.assertEqual(answer.method,'native-normal-cocycle')
        self.assertEqual(answer.evidence['normal_seed']['certificate'],result['certificate'])
