"""Exact Euler optimization: exhaustive arithmetic and independent topology."""
from copy import deepcopy
from itertools import product
import json
import random
import unittest
from unittest.mock import patch
from fastunknot import Diagram
from fastunknot.cocycle_euler import maximize_cocycle_face_euler, _euler_model
from fastunknot.cocycle_euler_flow import _minimize_difference
from fastunknot.cocycle_euler_verify import verify_difference_optimum
from fastunknot.cocycle_span import minimize_cocycle_span
from fastunknot.diagram_exterior import diagram_exterior
from fastunknot.integer_codec import json_safe
from fastunknot.normal_cocycle import rank_one_cocycle_seed, CocycleLimit
from fastunknot.normal_seed_verify import verify_normal_seed_certificate
from fastunknot.normal_surface_geometry import _prepare, NormalOrbitError
from tests.test_cocycle_face import NEW_DISC


class CocycleEulerTests(unittest.TestCase):
    def test_exhaustive_integer_optima_and_real_duality(self):
        rng = random.Random(261009510)
        for _ in range(240):
            n = rng.randrange(1, 5)
            edges = [[rng.randrange(n), rng.randrange(n), rng.randrange(-5, 6), rng.randrange(4)]
                     for _ in range(rng.randrange(1, 10))]
            constraints = [[0, v, 3] for v in range(1, n)]+[[v, 0, 3] for v in range(1, n)]
            constraints += [[rng.randrange(n), rng.randrange(n), rng.randrange(4)] for _ in range(4)]
            result = _minimize_difference(n, edges, constraints, [0]*n, lambda: None)
            c = result['certificate']
            oracle = min(sum(w*abs(z+p[b]-p[a]) for a,b,z,w in edges)
                         for tail in product(range(-3, 4), repeat=n-1)
                         for p in [(0,)+tail] if all(p[b]-p[a] <= d for a,b,d in constraints))
            self.assertEqual(c['objective'], oracle)
            self.assertTrue(verify_difference_optimum(n, edges, constraints, c))
            self.assertLessEqual(result['stats']['augmentations'], result['stats']['sent_units'])
            self.assertLessEqual(result['stats']['sent_units'], sum(e[3] for e in edges))

    def test_binary_scale_disconnected_zero_weight_and_cancellation(self):
        edges = [[0,1,3,2],[1,2,-7,3],[2,0,2,1],[3,3,-9,4],[0,0,6,0]]
        constraints = [[0,1,8],[1,0,8],[1,2,8],[2,1,8]]
        small = _minimize_difference(4,edges,constraints,[0]*4,lambda: None)
        scale = 1 << 20000
        big_edges = [[a,b,c*scale,w] for a,b,c,w in edges]
        big_constraints = [[a,b,d*scale] for a,b,d in constraints]
        big = _minimize_difference(4,big_edges,big_constraints,[0]*4,lambda: None)
        self.assertEqual(big['certificate']['objective'],small['certificate']['objective']*scale)
        self.assertEqual(big['stats'],small['stats'])
        encoded = json.loads(json.dumps(json_safe(big['certificate'])))
        with patch('fastunknot.cocycle_euler_flow._minimize_difference',side_effect=AssertionError):
            self.assertTrue(verify_difference_optimum(4,big_edges,big_constraints,encoded))
        def cancel():raise RuntimeError('cancelled')
        with self.assertRaisesRegex(RuntimeError,'cancelled'):
            _minimize_difference(4,edges,constraints,[0]*4,cancel)
        with self.assertRaisesRegex(RuntimeError,'cancelled'):
            verify_difference_optimum(4,edges,constraints,small['certificate'],check=cancel)
        empty = _minimize_difference(2,[],[],[3,-9],lambda: None)
        self.assertEqual(empty['certificate']['objective'],0)
        self.assertTrue(verify_difference_optimum(2,[],[],empty['certificate']))

    def test_reject_tampered_dual_and_invalid_models(self):
        edges = [[0,1,3,2]];constraints = [[0,1,0],[1,0,0]]
        c = _minimize_difference(2,edges,constraints,[0,0],lambda: None)['certificate']
        mutations = [dict(c,objective=7),dict(c,potential=[0,1]),dict(c,edge_flows=[3]),
                     dict(c,edge_flows=[0]),dict(c,constraint_flows=[-1,0]),
                     dict(c,constraint_flows=[0,0]),dict(c,extra=0),dict(c,potential=[False,0]),
                     dict(c,potential=[]),dict(c,schema='other')]
        for bad in mutations:self.assertFalse(verify_difference_optimum(2,edges,constraints,bad))
        for bad_edges in ([[0,2,3,2]],[[0,1,3,-1]],[[0,1,3,True]],[[False,1,3,2]]):
            self.assertFalse(verify_difference_optimum(2,bad_edges,constraints,c))
        with self.assertRaises(ValueError):
            _minimize_difference(2,edges,[[0,1,-1]],[0,0],lambda: None)

    def test_source_positive_and_certified_restricted_miss(self):
        for name,diagram,expected in [('face-disc',Diagram.from_pd(NEW_DISC),1),
              ('trefoil',Diagram.from_braid(2,[1,1,1]),-1),
              ('unknot-miss',Diagram.from_braid(2,[1,1,-1]),-1)]:
            raw = diagram_exterior(diagram);seed = rank_one_cocycle_seed(raw)
            span = minimize_cocycle_span(seed['vertices'],seed['heights'])['certificate']
            result = maximize_cocycle_face_euler(raw,seed['heights'],span)
            self.assertEqual(result['euler_characteristic'],expected,name)
            model = _euler_model(_prepare(raw,lambda:None),seed['heights'],span,lambda:None)
            self.assertTrue(verify_difference_optimum(len(model[4]),model[2],model[3],result['optimality_certificate']))
            if expected == 1:
                c = result['certificate']
                proof = dict(schema='diagram-cocycle-disc-v1',input_pd=[list(r) for r in diagram.pd],
                    triangulation=raw,heights=seed['heights'],coordinates=c['coordinates'],span_certificate=c)
                with patch('fastunknot.cocycle_euler.maximize_cocycle_face_euler',side_effect=AssertionError):
                    self.assertTrue(verify_normal_seed_certificate(diagram,proof))
                work = result['stats']['work']
                self.assertEqual(maximize_cocycle_face_euler(raw,seed['heights'],span,max_work=work),result)
                with self.assertRaises(CocycleLimit):
                    maximize_cocycle_face_euler(raw,seed['heights'],span,max_work=work-1)

    def test_invalid_span_incoherent_heights_and_negative_weight_guard(self):
        raw = diagram_exterior(Diagram.from_braid(2,[1,1,1]));seed = rank_one_cocycle_seed(raw)
        span = minimize_cocycle_span(seed['vertices'],seed['heights'])['certificate']
        transported = deepcopy(span)
        for key in ('vertex_ids','potential'):
            transported[key] = [hex(x) for x in transported[key]]
        transported['coordinates'] = [[hex(x) for x in row] for row in transported['coordinates']]
        transported['disc_count'] = hex(transported['disc_count'])
        self.assertEqual(maximize_cocycle_face_euler(raw,seed['heights'],transported)['euler_characteristic'],-1)
        bad = deepcopy(span);bad['disc_count'] += 1
        with self.assertRaises(ValueError):maximize_cocycle_face_euler(raw,seed['heights'],bad)
        heights = deepcopy(seed['heights']);heights[0][0] += 1
        bad_span = minimize_cocycle_span(seed['vertices'],heights)['certificate']
        with self.assertRaisesRegex(NormalOrbitError,'global cocycle'):
            maximize_cocycle_face_euler(raw,heights,bad_span)
        prepared = _prepare(raw,lambda:None)
        prepared['pairs'] = [];prepared['boundary_faces'] = []
        with self.assertRaisesRegex(NormalOrbitError,'negative edge weight'):
            _euler_model(prepared,seed['heights'],span,lambda:None)

if __name__ == '__main__':unittest.main()
