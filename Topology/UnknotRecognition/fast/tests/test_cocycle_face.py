"""Optimal-face discovery, tie topology and independent source replay."""
from copy import deepcopy
from itertools import product
import json
import random
import unittest
from unittest.mock import patch
from fastunknot import Diagram, recognize
from fastunknot.cocycle_face import cocycle_face_candidates
from fastunknot.cocycle_span import minimize_cocycle_span
from fastunknot.cocycle_span_verify import verify_cocycle_span
from fastunknot.diagram_exterior import diagram_exterior
from fastunknot.normal_cocycle import rank_one_cocycle_seed
from fastunknot.normal_cocycle_verify import inspect_cocycle_certificate
from fastunknot.normal_seed import normal_seed_decide
from fastunknot.normal_seed_verify import verify_normal_seed_certificate
from tests.test_normal_seed import OPTIONS

NEW_DISC = [[9,11,0,1],[0,2,3,1],[13,4,5,2],[12,6,7,4],
            [5,8,9,3],[7,10,11,8],[10,6,12,13]]

class CocycleFaceTests(unittest.TestCase):
    def test_matching_inequalities_characterize_optima_on_exhaustive_grid(self):
        rng = random.Random(261009480)
        for _ in range(40):
            vertices = [[rng.randrange(3) for _ in range(4)] for _ in range(4)]
            heights = [[rng.randrange(-3,4) for _ in range(4)] for _ in vertices]
            certificate = minimize_cocycle_span(vertices, heights)['certificate']
            labels = certificate['vertex_ids']
            low = {t:i for t,i,s,j in certificate['matching']}
            high = {s:j for t,i,s,j in certificate['matching']}
            for values in product(range(-3,4), repeat=len(labels)-1):
                potential = dict(zip(labels,(0,)+values))
                rows = [[h+potential[v] for h,v in zip(hs,vs)] for hs,vs in zip(heights,vertices)]
                optimal = sum(max(r)-min(r) for r in rows)==certificate['disc_count']
                feasible = all(r[low[t]]==min(r) and r[high[t]]==max(r) for t,r in enumerate(rows))
                self.assertEqual(feasible,optimal)
            for candidate in cocycle_face_candidates(vertices,heights,certificate,roots=100):
                self.assertTrue(verify_cocycle_span(vertices,heights,candidate['certificate']))

    def test_disconnected_components_binary_heights_and_cancellation(self):
        vertices = [[0,1,1,0],[0,1,1,0],[8,9,9,8],[8,9,9,8]]
        heights = [[0,0,0,0],[0,2,2,0],[0,0,0,0],[0,3,3,0]]
        certificate = minimize_cocycle_span(vertices,heights)['certificate']
        original = deepcopy(certificate)
        candidates = list(cocycle_face_candidates(vertices,heights,certificate,roots=100))
        self.assertTrue(candidates)
        self.assertEqual(certificate,original)
        scale = 1 << 20000
        large = [[x*scale for x in row] for row in heights]
        big = minimize_cocycle_span(vertices,large)['certificate']
        other = list(cocycle_face_candidates(vertices,large,big,roots=100))
        self.assertEqual([(c['root'],c['direction']) for c in candidates],[(c['root'],c['direction']) for c in other])
        for small,large_candidate in zip(candidates,other):
            self.assertEqual([[x*scale for x in row] for row in small['coordinates']],large_candidate['coordinates'])
        calls = [0]
        def stop():
            calls[0] += 1
            if calls[0] == 80: raise RuntimeError('cancelled')
        with self.assertRaisesRegex(RuntimeError,'cancelled'):
            list(cocycle_face_candidates(vertices,heights,certificate,check=stop))

    def test_new_disc_after_four_root_trials_and_exact_caps(self):
        diagram = Diagram.from_pd(NEW_DISC)
        self.assertEqual(normal_seed_decide(diagram,face_roots=0)['status'],'INCONCLUSIVE')
        self.assertEqual(normal_seed_decide(diagram,face_roots=3)['status'],'INCONCLUSIVE')
        self.assertEqual(normal_seed_decide(diagram)['status'],'INCONCLUSIVE')
        result = normal_seed_decide(diagram,face_roots=4)
        self.assertEqual(result['status'],'UNKNOT')
        self.assertEqual(result['stages'][-1]['stage'],'face')
        self.assertEqual(result['stages'][-1]['root_trial'],4)
        self.assertEqual(result['stats']['face_search']['candidates'],6)
        self.assertEqual(normal_seed_decide(diagram,max_work=result['work'],face_roots=4)['certificate'],result['certificate'])
        short = normal_seed_decide(diagram,max_work=result['work']-1,face_roots=4)
        self.assertEqual(short['status'],'INCONCLUSIVE')
        self.assertNotIn('certificate',short)
        with patch('fastunknot.cocycle_face.cocycle_face_candidates',side_effect=AssertionError), \
             patch('fastunknot.cocycle_span.minimize_cocycle_span',side_effect=AssertionError):
            self.assertTrue(verify_normal_seed_certificate(diagram,json.loads(json.dumps(result['certificate']))))
        answer = recognize(diagram,**OPTIONS,normal_seed_face_roots=4)
        self.assertEqual(answer.method,'native-normal-cocycle')

    def test_equal_minimum_can_be_disc_or_annulus_and_early_success_skips_face(self):
        diagram = Diagram.from_braid(4,[-1,2,1,-2,3])
        raw = diagram_exterior(diagram);seed = rank_one_cocycle_seed(raw)
        cert = minimize_cocycle_span(seed['vertices'],seed['heights'])['certificate']
        values = [cert]+[c['certificate'] for c in cocycle_face_candidates(seed['vertices'],seed['heights'],cert)]
        chis = set()
        for c in values:
            proof = dict(schema='diagram-cocycle-disc-v1',input_pd=[list(r) for r in diagram.pd],
                         triangulation=raw,heights=seed['heights'],coordinates=c['coordinates'],span_certificate=c)
            summary = inspect_cocycle_certificate(diagram,proof)
            self.assertEqual(c['disc_count'],84)
            self.assertEqual(summary['components'],1)
            chis.add(summary['euler_characteristic'])
        self.assertEqual(chis,{0,1})
        with patch('fastunknot.normal_seed.cocycle_face_candidates',side_effect=AssertionError):
            self.assertEqual(normal_seed_decide(diagram,face_roots=4)['status'],'UNKNOT')
            self.assertEqual(normal_seed_decide(Diagram.from_pd([]),face_roots=4)['status'],'UNKNOT')
            self.assertEqual(normal_seed_decide(Diagram.from_pd(NEW_DISC),optimize=False,face_roots=4)['status'],'INCONCLUSIVE')

    def test_strict_options_and_reject_invalid_span_witness(self):
        vertices,heights = [[0,1,2,3]],[[0,1,2,3]]
        cert = minimize_cocycle_span(vertices,heights)['certificate']
        self.assertEqual(list(cocycle_face_candidates([],[],{},roots=0)),[])
        for value in (True,-1,1.0,None):
            with self.assertRaises(ValueError): list(cocycle_face_candidates(vertices,heights,cert,roots=value))
            with self.assertRaises(ValueError): normal_seed_decide(Diagram.from_pd([]),face_roots=value)
            with self.assertRaises(ValueError): recognize(Diagram.from_pd([]),normal_seed_face_roots=value)
        bad = deepcopy(cert);bad['disc_count'] += 1
        with self.assertRaises(ValueError): list(cocycle_face_candidates(vertices,heights,bad))

if __name__=='__main__': unittest.main()
