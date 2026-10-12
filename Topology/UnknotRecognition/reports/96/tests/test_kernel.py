import copy
from fractions import Fraction as F
from itertools import product
import random
import unittest
from scalar_separators import *
from scalar_separators.exact import *
from scalar_separators.fixtures import *
from scalar_separators.solver import local_rays

class ExactTests(unittest.TestCase):
    def test_empty_matrices(self):
        self.assertEqual(rank([],4),0)
        self.assertEqual(len(nullspace([],4)),4)
        self.assertEqual(rays_by_zeros([],0)[0],())
        self.assertEqual(rays_by_zeros([],2)[0],((0,1),(1,0)))
    def test_forced_zeros_and_degeneracy(self):
        A=((1,1,0,0),(0,0,1,-1))
        self.assertEqual(rays_by_zeros(A,4)[0],((0,0,1,1),))
        self.assertEqual(rays_by_zeros(A,4)[0],rays_by_supports(A,4))
    def test_rational_and_large_coefficients(self):
        B=10**80+7
        rays,_=rays_by_zeros(((F(1,3),-B),),2)
        self.assertEqual(rays,((3*B,1),))
    def test_ray_oracle_random(self):
        rng=random.Random(87311)
        for _ in range(100):
            n=rng.randrange(1,7)
            A=[[rng.randrange(-2,3) for _ in range(n)] for __ in range(rng.randrange(5))]
            pairs=tuple((i,j) for i in range(n) for j in range(i+1,n) if rng.random()<0.08)
            self.assertEqual(rays_by_zeros(A,n,pairs)[0],rays_by_supports(A,n,pairs))

class SolverTests(unittest.TestCase):
    def test_gain_chain_positive_negative(self):
        for m in (1,2,4,8):
            for delta in (-1,0,1):
                model,c=gain_chain(m,3**m+delta)
                packet=Prepared(model).solve(c)
                self.assertEqual(packet['status'],'POSITIVE' if delta<0 else 'NONPOSITIVE')
                self.assertTrue(verify(model,c,packet))
    def test_signed_fluxes(self):
        m=scalar_star()
        p=Prepared(m)
        for c in ({'a':1},{'b':1},{'a':-1,'b':-1,'c':-1,'d':-1}):
            a=p.solve(c)
            self.assertTrue(verify(m,c,a))
        a=p.solve({'a':1})
        self.assertTrue(any(F(t)<0 for t in a['fluxes'].values()))
    def test_zero_port_positive_subtree(self):
        m=Model((-1,0),(Node(('a',),(1,),((1,0),(0,1))),
                              Node(('b',),(1,),((0,1),)))).validate()
        a=Prepared(m).solve({'b':1})
        self.assertEqual(a['origin_node'],1)
        self.assertEqual(F(a['coordinates']['a']),0)
        self.assertTrue(verify(m,{'b':1},a))
    def test_unavailable_port_direction(self):
        m=Model((-1,0),(Node(('a',),(1,),((1,1),)),Node(('b',),(1,),((1,-1),)))).validate()
        a=Prepared(m).solve({'a':1,'b':1})
        self.assertEqual(a['status'],'NONPOSITIVE')
        self.assertTrue(verify(m,{'a':1,'b':1},a))
    def test_zero_objective(self):
        m,c=gain_chain(3)
        a=Prepared(m).solve({})
        self.assertEqual(a['status'],'NONPOSITIVE')
        self.assertTrue(verify(m,{},a))
    def test_coordinate_deletions_reuse(self):
        m,c=gain_chain(4,2**4)
        p=Prepared(m)
        a=p.solve(c,zeros=[f'v{i}' for i in range(1,5)])
        self.assertEqual(a['status'],'NONPOSITIVE')
        self.assertTrue(verify(m,c,a,[f'v{i}' for i in range(1,5)]))
    def test_minimal_support(self):
        m=scalar_star(); c={'a':1,'b':1,'c':1,'d':1}
        p=Prepared(m)
        a,z,calls=p.minimal_positive_support(c)
        self.assertTrue(verify(m,c,a,z))
        self.assertLessEqual(calls,len(m.names())+1)
        for s,v in a['coordinates'].items():
            if F(v):
                self.assertEqual(p.solve(c,set(z)|{s})['status'],'NONPOSITIVE')
    def test_large_binary_message(self):
        m,c=gain_chain(128)
        p=Prepared(m); a=p.solve(c)
        self.assertEqual(a['status'],'NONPOSITIVE')
        self.assertEqual(sum(s['rays'] for s in p.stats),258)
    def test_positive_tampering(self):
        m,c=gain_chain(3,26); a=Prepared(m).solve(c)
        for kind in range(4):
            b=copy.deepcopy(a)
            if kind==0: b['coordinates']['end']='0'
            if kind==1: b['fluxes']['1']='-17'
            if kind==2: b['objective']='0'
            if kind==3: b['coordinates']['unknown']='1'
            self.assertFalse(verify(m,c,b))
    def test_negative_tampering(self):
        m,c=gain_chain(3); a=Prepared(m).solve(c)
        b=copy.deepcopy(a); b['local_rays'][1].pop()
        self.assertFalse(verify(m,c,b))
        b=copy.deepcopy(a); b['messages']['1']['1']='999'
        self.assertFalse(verify(m,c,b))
        b=copy.deepcopy(a); b['messages'].pop('0')
        self.assertFalse(verify(m,c,b))
    def test_invalid_models(self):
        with self.assertRaises(ValueError):
            Model((-1,1),(Node((),(),()),Node((),(1,),()))).validate()
        with self.assertRaises(ValueError):
            Model((-1,0),(Node(('a',),(1,),()),Node(('a',),(1,),()))).validate()
        with self.assertRaises(ValueError):
            Model((-1,),(Node(('a',),(),((1.0,),)),)).validate()
    def test_unknown_coordinates(self):
        m,c=gain_chain(1)
        with self.assertRaises(ValueError):
            Prepared(m).solve({'misspelled':1})
        self.assertFalse(verify(m,{'unknown':1},{'status':'NONPOSITIVE'}))

class SourceTests(unittest.TestCase):
    def test_rank_one_compiler(self):
        A=((1,-1,-1,0),(0,0,1,-1))
        m,w=compile_source(A,4,[(0,1),(2,3)],[-1,0],[(0,1)])
        self.assertEqual(len(w),1)
        for c in ({'0':1},{'0':-1,'1':-1,'2':-1,'3':-1}):
            a=Prepared(m).solve(c)
            self.assertTrue(verify(m,c,a))
            if a['status']=='POSITIVE':
                x=[F(a['coordinates'][str(j)]) for j in range(4)]
                self.assertTrue(all(dot(row,x)==0 for row in A))
    def test_source_compilation_replay_and_tamper(self):
        A=((1,-1,-1,0),(0,0,1,-1)); bags=[(0,1),(2,3)]; parents=[-1,0]
        m,w=compile_source(A,4,bags,parents,[(0,1)])
        self.assertTrue(verify_source_compilation(A,4,bags,parents,[(0,1)],m,w))
        bad=dict(w);bad[1]=tuple(z+1 for z in bad[1])
        self.assertFalse(verify_source_compilation(A,4,bags,parents,[(0,1)],m,bad))
        self.assertFalse(verify_source_compilation(A,4,bags,parents,[],m,w))
    def test_rank_two_rejected(self):
        A=((1,0,-1,0),(0,1,0,-1))
        with self.assertRaisesRegex(ValueError,'exceeds one'):
            compile_source(A,4,[(0,1),(2,3)],[-1,0])
    def test_crossing_conflict_rejected(self):
        with self.assertRaisesRegex(ValueError,'crosses'):
            compile_source(((1,-1),),2,[(0,),(1,)],[-1,0],[(0,1)])
    def test_zero_intersection(self):
        m,w=compile_source(((1,0),(0,1)),2,[(0,),(1,)],[-1,0])
        self.assertEqual(w[1],(0,0))
        a=Prepared(m).solve({'0':1,'1':1})
        self.assertEqual(a['status'],'NONPOSITIVE')
        self.assertTrue(verify(m,{'0':1,'1':1},a))
    def test_source_projection(self):
        m=scalar_star()
        A,names,pairs=source_from_model(m)
        rays=rays_by_supports(A,len(names),pairs)
        self.assertEqual(set(rays),{(0,1,1,0),(1,0,0,1)})
    def test_actual_normal_meridian(self):
        A,n,pairs=normal_matching(solid_torus())
        m,w=compile_source(A,n,[tuple(range(n))],[-1],pairs)
        a=Prepared(m).solve({'6':1},zeros=['2'])
        self.assertTrue(verify(m,{'6':1},a,['2']))
        self.assertEqual(tuple(F(a['coordinates'][str(i)]) for i in range(n)),(1,1,0,0,0,0,1))
    def test_capped_matching_coordinates(self):
        A,n,pairs=normal_matching(capped_solid_torus())
        x=(1,1,0,0,0,0,1,1,2,0,0,0,0,0)
        self.assertTrue(all(dot(row,x)==0 for row in A))
        self.assertFalse(any(x[i] and x[j] for i,j in pairs))
    def test_euler_coefficients(self):
        for tri,x in [(solid_torus(),(1,1,0,0,0,0,1)),
                      (capped_solid_torus(),(1,1,0,0,0,0,1,1,2,0,0,0,0,0))]:
            self.assertEqual(dot(normal_euler(tri),x),1)
    def test_bad_source_gluing(self):
        t=solid_torus(); t['tetrahedra'][0][1]=None
        with self.assertRaises(ValueError): normal_matching(t)
    def test_signed_cut_artificial_ray(self):
        # Source cone R_+^2 has two rays. The redundant free scalar port
        # t=a-b creates the additional sign-chamber ray (a,b,t)=(1,1,0).
        m=Model((-1,0),(Node((),(1,),()),Node(('a','b'),(1,),((1,-1,-1),)))).validate()
        rays,_=local_rays(m.nodes[1])
        self.assertIn((1,1,0),rays)
        A,names,pairs=source_from_model(m)
        self.assertNotIn((1,1),rays_by_supports(A,2))
        a,z,calls=Prepared(m).minimal_positive_support({'a':1,'b':1})
        self.assertEqual(sum(F(x)>0 for x in a['coordinates'].values()),1)

if __name__=='__main__': unittest.main()
