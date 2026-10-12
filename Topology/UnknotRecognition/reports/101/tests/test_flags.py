from __future__ import annotations
import sys
from pathlib import Path
sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'code'))
import unittest
from dataclasses import replace
from collections import Counter
from itertools import permutations,product
from unittest.mock import patch
import random
from atlas import *
from flags import *
from replay import verify,flag_counts
from sources import *
from reference import *
from morse_adapter import convex_cone_certificate,packet_from_flags,rm


def catalog():
    result=[simplex(d) for d in range(4)]
    result.extend([
      Polytope('square',((0,0),(2,0),(2,2),(0,2))),
      Polytope('pentagon',((0,0),(2,0),(3,2),(1,3),(-1,2))),
      Polytope('cube',tuple(product((0,1),repeat=3))),
      Polytope('octahedron',((1,0,0),(-1,0,0),(0,1,0),(0,-1,0),(0,0,1),(0,0,-1))),
      Polytope('pyramid',((0,0,0),(2,0,0),(2,2,0),(0,2,0),(1,1,2))),
      Polytope('prism',tuple(p+(z,) for p in ((0,0),(2,0),(0,2)) for z in (0,1))),
      Polytope('truncated_tetrahedron',tuple(tuple((2 if j==a else 1 if j==b else 0) for j in (1,2,3))
                    for a in range(4) for b in range(4) if a!=b))])
    return result


def gauge(atlas,rng):
    changes={f.name:(rng.choice((-1,1)),rng.randint(-20,20)) for f in atlas.families}
    fam=[]; charts=[]; marks=[]
    for f in atlas.families:
        s,b=changes[f.name]; lo,hi=pullback(f.lo,f.hi,s,b)
        fam.append(replace(f,lo=lo,hi=hi))
    for c in atlas.charts:
        su,bu=changes[c.upper]; sl,bl=changes[c.lower]
        lo,hi=pullback(c.lo,c.hi,su,bu)
        charts.append(replace(c,lo=lo,hi=hi,slope=sl*c.slope*su,shift=sl*(c.slope*bu+c.shift-bl)))
    for m in atlas.marks:
        s,b=changes[m.family]; lo,hi=pullback(m.lo,m.hi,s,b)
        marks.append(replace(m,lo=lo,hi=hi))
    return Atlas(atlas.polytopes,tuple(fam),tuple(charts),tuple(marks))


def one_tetra_sources():
    yield [[None]*4]
    choices={}
    for a in range(4):
        for b in range(a+1,4):
            choices[a,b]=[p for p in permutations(range(4)) if p[a]==b]
    def make(pairs,maps):
        row=[None]*4
        for (a,b),p in zip(pairs,maps):
            inv=tuple(p.index(i) for i in range(4))
            row[a]={'tetrahedron':0,'permutation':list(p)}
            row[b]={'tetrahedron':0,'permutation':list(inv)}
        return [row]
    for pair,ps in choices.items():
        for p in ps: yield make((pair,),(p,))
    for pairs in (((0,1),(2,3)),((0,2),(1,3)),((0,3),(1,2))):
        for ps in product(*(choices[pair] for pair in pairs)):
            yield make(pairs,ps)


class ConvexTests(unittest.TestCase):
    def test_catalog_euler(self):
        for p in catalog():
            with self.subTest(p=p.name):
                p.faces()
                self.assertEqual(sum((-1)**p.face_dim(f) for f in p.faces()),1)
    def test_simplex_flag_counts(self):
        expected=((1,0,0,0),(1,2,0,0),(1,6,6,0),(1,14,36,24))
        for d in range(4): self.assertEqual(flag_counts(simplex(d)),expected[d])
    def test_polytopal_flag_counts(self):
        for p in catalog():
            c=Counter(len(x)-1 for x in combinatorial_flags(p) if x[-1]==p.full)
            self.assertEqual(flag_counts(p),tuple(c[d] for d in range(4)))
    def test_bad_convex_templates(self):
        bad=[Polytope('bad',()),Polytope('bad',((0,),(0,))),Polytope('bad',((0,),(1,),(2,))),
             Polytope('bad',((0,0),(1,0))),Polytope('bad',((False,),(1,)))]
        for p in bad:
            with self.assertRaises((ValueError,TypeError)): p.faces()
    def test_integer_affine_coordinates(self):
        for p in catalog():
            vertices=tuple(tuple(3*(j+1)+sum((int(i==j)+int(i<j))*v[i] for i in range(p.dim)) for j in range(p.dim)) for v in p.vertices)
            q=Polytope(p.name+'affine',vertices)
            self.assertEqual(p.faces(),q.faces())

class CompilerTests(unittest.TestCase):
    def test_catalog_regularization(self):
        for p in catalog():
            a=polytope_ball(p); c=compile_flags(a)
            self.assertTrue(verify(a,c)); compare_compiled(a,c)
    def test_loop_occurrences(self):
        a=line(1,True); c=compile_flags(a)
        d,f,af,m=expanded_cells(c.result)
        self.assertEqual(inventory(c.result)['cell_counts'],[2,2,0,0])
        self.assertEqual(homology(d,f),(1,1,0,0))
        self.assertFalse(abstract_simplex_check(d,f))
    def test_two_subdivisions(self):
        for a in (line(1,True),tetrahedral_atlas(solid_torus_source())[0]):
            c=compile_flags(a); d=compile_flags(c.result)
            self.assertTrue(verify(c.result,d))
            x=expanded_cells(d.result); regular_check(*x[:3])
            self.assertTrue(abstract_simplex_check(x[0],x[1]))
    def test_source_oracle(self):
        a,metadata=tetrahedral_atlas(solid_torus_source()); c=compile_flags(a)
        compare_source_oracle(solid_torus_source(),metadata,c)
        x=expanded_cells(c.result)
        for prime in (2,3,5):
            self.assertEqual(homology(x[0],x[1],prime),(1,1,0,0))
            self.assertEqual(homology(x[0],x[1],prime,x[3]['boundary']),(1,2,1,0))
    def test_all_source_relabellings(self):
        for p in permutations(range(4)):
            s=relabel_tetrahedra(solid_torus_source(),[p],[0]); a,meta=tetrahedral_atlas(s)
            c=compile_flags(a); self.assertTrue(verify(a,c)); compare_source_oracle(s,meta,c)
    def test_product_cells_and_boundary(self):
        for d in range(3):
            for periodic in (False,True):
                for n in (1,2,5):
                    a=product_with_line(polytope_ball(simplex(d)),n,periodic); c=compile_flags(a)
                    self.assertTrue(verify(a,c)); compare_compiled(a,c)
                    x=expanded_cells(c.result)
                    expected=(1,1,0,0) if periodic else (1,0,0,0)
                    self.assertEqual(homology(x[0],x[1]),expected)
    def test_reverse_coordinates(self):
        rng=random.Random(61012)
        for _ in range(20):
            a=gauge(product_with_line(polytope_ball(simplex(2)),rng.randint(1,7),bool(rng.randrange(2))),rng)
            c=compile_flags(a); self.assertTrue(verify(a,c)); compare_compiled(a,c)
    def test_large_binary_ranks(self):
        for b in (64,1024,4096,16384):
            a=product_with_line(polytope_ball(simplex(2)),(1<<b)+1,True); c=compile_flags(a)
            self.assertTrue(verify(a,c))
            self.assertEqual(len(c.result.families),196)
            self.assertEqual(len(c.result.charts),1289)
    def test_large_serialization(self):
        a=line((1<<16384)+1,True); c=compile_flags(a)
        restored=certificate_from_data(loads(dumps(certificate_data(c))))
        self.assertEqual(c,restored); self.assertTrue(verify(a,restored))
    def test_independent_replay(self):
        a=polytope_ball(simplex(3)); c=compile_flags(a)
        with patch('flags.compile_flags',side_effect=AssertionError('producer disabled')),patch('flags.ending_flags',side_effect=AssertionError('enumeration disabled')):
            self.assertTrue(verify(a,c))
    def test_refined_certificate_partitions(self):
        a=polytope_ball(simplex(2),10); c=compile_flags(a)
        chart=c.result.charts[0]
        charts=(replace(chart,hi=3),replace(chart,lo=3))+c.result.charts[1:]
        self.assertTrue(verify(a,replace(c,result=replace(c.result,charts=charts))))
    def test_marked_subcomplex(self):
        a=polytope_ball(simplex(2),10)
        top=next(f for f in a.families if f.name=='C7')
        self.assertRaises(ValueError,validate,replace(a,marks=(Mark('wrong',top.name,0,10),)))
    def test_cancellation_propagates(self):
        class Cancelled(Exception): pass
        def stop(): raise Cancelled()
        a=line(2); c=compile_flags(a)
        with self.assertRaises(Cancelled): compile_flags(a,stop)
        with self.assertRaises(Cancelled): verify(a,c,stop)
    def test_literal_caps(self):
        a=line(1<<100,True)
        with self.assertRaises(ValueError): literal_flags(a,100)
        with self.assertRaises(ValueError): expanded_cells(a,100)

class AdversarialTests(unittest.TestCase):
    def setUp(self):
        self.a=polytope_ball(simplex(2),3); self.c=compile_flags(self.a)
    def test_wrong_hash(self): self.assertFalse(verify(self.a,replace(self.c,source_sha256='0'*64)))
    def test_wrong_schema(self): self.assertFalse(verify(self.a,replace(self.c,schema='raw-cells')))
    def test_missing_and_duplicate_carriers(self):
        self.assertFalse(verify(self.a,replace(self.c,carriers=self.c.carriers[:-1])))
        self.assertFalse(verify(self.a,replace(self.c,carriers=self.c.carriers[:-1]+self.c.carriers[:1])))
    def test_wrong_source_carrier(self):
        carriers=list(self.c.carriers); carriers[-1]=replace(carriers[-1],source=self.a.families[0].name)
        self.assertFalse(verify(self.a,replace(self.c,carriers=tuple(carriers))))
    def test_wrong_chart_rank(self):
        charts=list(self.c.result.charts); charts[-1]=replace(charts[-1],shift=1)
        self.assertFalse(verify(self.a,replace(self.c,result=replace(self.c.result,charts=tuple(charts)))))
    def test_missing_source_chart(self):
        with self.assertRaises(ValueError): validate(replace(self.a,charts=self.a.charts[1:]))
        with self.assertRaises(ValueError): validate(replace(self.a,charts=self.a.charts+self.a.charts[:1]))
    def test_bad_nested_square(self):
        # Vertex targets can remain in range while violating a triangle-edge square.
        a=polytope_ball(simplex(2)); charts=list(a.charts)
        j=next(j for j,c in enumerate(charts) if c.upper=='C7' and c.face==1)
        charts[j]=replace(charts[j],lower='C2')
        with self.assertRaisesRegex(ValueError,'incoherent'): validate(replace(a,charts=tuple(charts)))
    def test_false_marking(self):
        self.assertFalse(verify(self.a,replace(self.c,result=replace(self.c.result,marks=()))))
    def test_bool_rank_rejected(self):
        families=list(self.a.families); families[0]=replace(families[0],lo=False)
        with self.assertRaises(ValueError): validate(replace(self.a,families=tuple(families)))
    def test_reciprocal_source_required(self):
        s=solid_torus_source(); s[0][1]=None
        with self.assertRaises(ValueError): tetrahedral_atlas(s)

class MorseBridgeTests(unittest.TestCase):
    def test_all_convex_cones(self):
        for p in catalog():
            a=polytope_ball(p); c=compile_flags(a)
            packet,proof,counts=convex_cone_certificate(p,1,a,c)
            self.assertEqual(counts[0],1); prepared=rm.prepare(packet)
            self.assertTrue(rm.explicit_acyclic(prepared)); self.assertTrue(rm.explicit_collapse(prepared))
    def test_large_critical_multiplicity(self):
        n=1<<16384; p=simplex(3); a=polytope_ball(p,n); c=compile_flags(a)
        packet,proof,counts=convex_cone_certificate(p,n,a,c)
        self.assertEqual(counts,(n,0,0,0)); self.assertFalse(rm.one_critical_vertex(rm.prepare(packet)))
    def test_generic_export_is_not_ball(self):
        a=tetrahedral_atlas(solid_torus_source())[0]; c=compile_flags(a)
        packet=packet_from_flags(a,c); prepared=rm.prepare(packet)
        self.assertFalse(rm.one_critical_vertex(prepared))
        with self.assertRaises(ValueError): convex_cone_certificate(simplex(3),1,a,c)

if __name__=='__main__': unittest.main(verbosity=2)
