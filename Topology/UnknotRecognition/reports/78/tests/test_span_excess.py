import copy
import unittest
from itertools import product
from dataclasses import replace
from span_excess import *
from span_excess.model import Budget
from span_excess.prepare import prepare_model
from span_excess.strata import enumerate_strata
from span_excess.network import feasibility, minimize_difference
from span_excess.checker import check_feasible, check_negative_cycle, check_optimum, check_model
from span_excess.geometry import product_solid_torus, expand_surface


def interval_model(L=7):
    return prepare_model(4, [(0,1,2,3)]*2, [(0,0,0,0), (L,0,0,0)],
                         [(0,1,-L//3,2), (1,2,1,1), (2,3,-2,2)])


class NetworkTests(unittest.TestCase):
    def test_feasible(self):
        a=[(0,1,-5),(1,2,1),(2,0,7)]
        r=feasibility(3,a)
        self.assertTrue(check_feasible(3,a,r['potential']))
    def test_negative_cycle(self):
        a=[(0,1,-5),(1,2,1),(2,0,2)]
        r=feasibility(3,a)
        self.assertTrue(check_negative_cycle(3,a,r))
    def test_negative_loop(self):
        a=[(0,0,-1)]; r=feasibility(1,a)
        self.assertTrue(check_negative_cycle(1,a,r))
    def test_zero_cycle(self):
        self.assertEqual(feasibility(2,[(0,1,-2),(1,0,2)])['status'],'FEASIBLE')
    def test_cycle_mutation(self):
        a=[(0,1,-3),(1,0,1)];r=feasibility(2,a)
        r['cycle'].pop();self.assertFalse(check_negative_cycle(2,a,r))
    def test_single_objective(self):
        e=[(0,1,4,3)];r=minimize_difference(2,e,[])['certificate']
        self.assertEqual(r['objective'],0)
        self.assertTrue(check_optimum(2,e,[],r))
    def test_forced_nonzero(self):
        e=[(0,1,4,3)];a=[(0,1,0),(1,0,0)]
        r=minimize_difference(2,e,a)['certificate']
        self.assertEqual(r['objective'],12)
    def test_loop_objective(self):
        e=[(0,0,-9,3)];r=minimize_difference(1,e,[])['certificate']
        self.assertEqual(r['objective'],27)
        self.assertTrue(check_optimum(1,e,[],r))
    def test_zero_weights(self):
        r=minimize_difference(2,[(0,1,7,0)],[(0,1,-3)])
        self.assertEqual(r['certificate']['objective'],0)
        self.assertEqual(r['stats']['augmentations'],0)
    def test_infeasible_objective(self):
        r=minimize_difference(1,[],[(0,0,-1)])
        self.assertEqual(r['certificate']['status'],'INFEASIBLE')
    def test_flow_mutation(self):
        e=[(0,1,4,3)];a=[(0,1,0),(1,0,0)]
        r=minimize_difference(2,e,a)['certificate'];r['edge_flows'][0]+=1
        self.assertFalse(check_optimum(2,e,a,r))
    def test_objective_mutation(self):
        e=[(0,1,4,3)];r=minimize_difference(2,e,[])['certificate'];r['objective']=1
        self.assertFalse(check_optimum(2,e,[],r))
    def test_bad_initial(self):
        with self.assertRaises(ValueError): minimize_difference(2,[],[(0,1,-1)],[0,0])
    def test_negative_weight_rejected(self):
        with self.assertRaises(ValueError): minimize_difference(2,[(0,1,0,-1)],[])
    def test_large_bits(self):
        e=[(0,1,1<<10000,3)];r=minimize_difference(2,e,[])['certificate']
        self.assertTrue(check_optimum(2,e,[],r))
        self.assertEqual(r['objective'],0)


class StratumTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls): cls.m=interval_model()
    def test_balanced_witness(self): self.assertTrue(check_model(self.m))
    def test_unbalanced_witness(self):
        m=replace(self.m,low=(0,0));self.assertFalse(check_model(m))
        with self.assertRaises(ValueError): m.validate()
    def test_wrong_optimum(self):
        with self.assertRaises(ValueError): replace(self.m,optimum=100).validate()
    def test_gap_identity(self):
        for p in product(range(-2,3),repeat=4):
            self.assertEqual(self.m.span(p)-self.m.optimum,sum(self.m.defects(p)))
    def test_count(self):
        for k in range(5):
            rows=list(enumerate_strata(self.m,k))
            self.assertEqual(len(rows),stratum_count(2,k))
            self.assertEqual(len(set(rows)),len(rows))
    def test_containing_cell(self):
        for p in product(range(-1,2),repeat=4):
            cell=containing_stratum(self.m,p)
            self.assertTrue(check_feasible(4,constraints_for(self.m,cell),p))
    def test_anchor_not_witness(self):
        with self.assertRaises(ValueError):
            constraints_for(self.m,Stratum(((0,1,self.m.high[0]),)))
    def test_duplicate_slot(self):
        with self.assertRaises(ValueError):
            constraints_for(self.m,Stratum(((0,1,1),(0,1,2))))
    def test_negative_radius(self):
        with self.assertRaises(ValueError): optimize_band(self.m,-1)
    def test_bool_radius(self):
        with self.assertRaises(ValueError): optimize_band(self.m,True)
    def test_json_roundtrip(self):
        self.assertEqual(HeightModel.from_dict(self.m.to_dict()),self.m)
    def test_unknown_json_field(self):
        data=self.m.to_dict();data['trust_me']=True
        with self.assertRaises(ValueError): HeightModel.from_dict(data)


class BandTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.m=interval_model(4);cls.a=optimize_band(cls.m,2)
    def test_complete_replay(self): self.assertTrue(replay_band(self.m,self.a))
    def test_full_box_optimum(self):
        best=-10**9;profiles={}
        # Proven exhaustive range for the two-tetrahedron interval family.
        for tail in product(range(-2,7),repeat=3):
            p=(0,)+tail;q=self.m.span(p)-4
            if q<=2:
                score=self.m.score2(p);best=max(best,score)
                profiles[str(q)]=max(profiles.get(str(q),score),score)
        self.assertEqual(best,self.a['best']['score2'])
        self.assertEqual(profiles,{q:x['score2'] for q,x in self.a['profile'].items()})
    def test_missing_cell(self):
        a=copy.deepcopy(self.a);a['cells'].pop()
        self.assertFalse(replay_band(self.m,a))
    def test_duplicated_cell(self):
        a=copy.deepcopy(self.a);a['cells'][-1]=a['cells'][0]
        self.assertFalse(replay_band(self.m,a))
    def test_changed_radius(self):
        a=copy.deepcopy(self.a);a['radius']=3
        self.assertFalse(replay_band(self.m,a))
    def test_wrong_best(self):
        a=copy.deepcopy(self.a);a['best']=None
        self.assertFalse(replay_band(self.m,a))
    def test_missing_profile(self):
        a=copy.deepcopy(self.a);a['profile'].pop(next(iter(a['profile'])))
        self.assertFalse(replay_band(self.m,a))
    def test_extra_constraints(self):
        a=optimize_band(self.m,1,extra=((0,1,0),(1,0,0)))
        self.assertTrue(replay_band(self.m,a))
    def test_infeasible_chamber(self):
        a=optimize_band(self.m,1,extra=((0,0,-1),))
        self.assertIsNone(a['best']);self.assertTrue(replay_band(self.m,a))
    def test_work_limit(self):
        with self.assertRaises(WorkLimit): optimize_band(self.m,2,max_work=3)
    def test_cancellation(self):
        def cancel(): raise RuntimeError('cancelled')
        with self.assertRaisesRegex(RuntimeError,'cancelled'): optimize_band(self.m,2,check=cancel)
    def test_streamed_not_complete_certificate(self):
        rows=[];a=optimize_band(self.m,1,save_cells=False,on_cell=rows.append)
        self.assertEqual(len(rows),a['stats']['strata'])
        self.assertFalse(replay_band(self.m,a))


class GeometryTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls): cls.g=product_solid_torus();cls.m=cls.g.model()
    def test_solid_torus_size(self):
        self.assertEqual(len(self.g.tetrahedra),9);self.assertEqual(self.m.optimum,3)
    def test_fiber_disk(self):
        s=expand_surface(self.g,[0]*9)
        self.assertEqual(s['components'],[dict(pieces=3,vertices=6,edges=8,euler=1,boundary=1,genus=0,**{'class':1})])
    def test_additional_null_disk(self):
        s=expand_surface(self.g,[0,-1,-1,-1,-1,-1,-1,-1,-1])
        self.assertEqual(s['euler'],2);self.assertEqual(s['pieces'],7)
        self.assertEqual([r['class'] for r in s['components']],[0,1])
    def test_sharp_opposite_pair(self):
        s=expand_surface(self.g,[0,-1,-1,-1,0,0,-1,-1,-1])
        self.assertEqual(s['pieces']-self.m.optimum,2*self.m.optimum)
        self.assertEqual([r['class'] for r in s['components']],[-1,1,1])
    def test_arbitrarily_many_opposite_pairs(self):
        for q in range(8):
            # Slice values 0,q+1,0 give increments q+1,-q-1,1.
            # Use 0,q,0 instead: q,-q,1 => q negative and q+1 positive.
            p=[0]*3+[q]*3+[0]*3
            s=expand_surface(self.g,p)
            self.assertEqual(s['pieces'],3*(2*q+1))
            self.assertEqual(sum(r['class']==-1 for r in s['components']),q)
    def test_interior_vertices(self):
        g=product_solid_torus(3,True);m=g.model();s=expand_surface(g,m.initial)
        self.assertEqual(m.optimum,9);self.assertEqual(s['euler'],1)
    def test_euler_cell_identity(self):
        for i in range(9):
            for x in (-2,-1,0,1,2):
                p=[0]*9;p[i]=x;s=expand_surface(self.g,p)
                self.assertEqual(2*s['euler'],self.m.score2(p))
    def test_component_piece_budget(self):
        for p in ([0,-1,-1,-1,-1,-1,-1,-1,-1], [0]*3+[3]*3+[0]*3):
            s=expand_surface(self.g,p);k=s['pieces']-self.m.optimum
            for f in s['components']:
                if f['class']==1:
                    self.assertLessEqual(s['pieces']-f['pieces'],k)
            self.assertLessEqual(len(s['components']),k+1)
    def test_radius_two_product_search(self):
        a=optimize_band(self.m,2)
        self.assertTrue(replay_band(self.m,a))
        self.assertEqual(a['best']['score2'],2)
        for row in a['profile'].values():
            self.assertEqual(2*expand_surface(self.g,row['proof']['potential'])['euler'],row['score2'])
    def test_expansion_limit(self):
        with self.assertRaises(ValueError): expand_surface(self.g,[0]*3+[100]*3+[0]*3,max_pieces=5)
    def test_circle_size_rejected(self):
        with self.assertRaises(ValueError): product_solid_torus(2)


if __name__=='__main__': unittest.main()
