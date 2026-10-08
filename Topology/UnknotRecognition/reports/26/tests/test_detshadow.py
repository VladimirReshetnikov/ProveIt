import itertools
import random
import unittest
from dataclasses import replace
from types import SimpleNamespace as NS
from detshadow.linalg import (bareiss, rational_det, signed_laplacian, quotient_cofactor,
                              TerminalKernel, verify_kernel)
from detshadow.diagram import Diagram, from_braid, complete_matching
from detshadow.continuation import (dot_degree, overlay_circles, recover_quantum_shifts,
                                   norm_four, shift_four, observe_scan)
from detshadow.cube import reduced_homology


def partitions(n):
    if n == 0:
        yield ()
        return
    def visit(seq):
        if len(seq) == n:
            yield tuple(seq)
        else:
            for a in range(max(seq) + 2):
                yield from visit(seq + [a])
    yield from visit([0])


class LinearTests(unittest.TestCase):
    def test_empty_determinant(self):
        self.assertEqual(bareiss([]), 1)
    def test_pivot_and_singular(self):
        self.assertEqual(bareiss([[0, 2], [3, 1]]), -6)
        self.assertEqual(bareiss([[1, 2], [2, 4]]), 0)
    def test_permutation_oracle(self):
        rng = random.Random(412)
        for n in range(1, 6):
            for _ in range(15):
                a = [[rng.randrange(-3, 4) for _ in range(n)] for _ in range(n)]
                expected = 0
                for p in itertools.permutations(range(n)):
                    sign = (-1)**sum(p[i] > p[j] for i in range(n) for j in range(i+1,n))
                    value = sign
                    for i in range(n):
                        value *= a[i][p[i]]
                    expected += value
                self.assertEqual(bareiss(a), expected)
    def test_signed_singular_interior(self):
        lap = signed_laplacian(3, [(0,1,1),(0,2,-1)])
        k = TerminalKernel.build(lap, [1,2])
        self.assertEqual(k.nullity, 1)
        self.assertEqual(k.query([0,1]), -1)
        self.assertEqual(k.query([0,0]), 0)
    def test_two_by_two_pivot(self):
        a = [[0,1,2],[1,0,3],[2,3,4]]
        k = TerminalKernel.build(a, [2])
        self.assertEqual(k.selected, (0,1))
        self.assertEqual(k.factor, -1)
        self.assertEqual(k.query([0]), -1)
        self.assertTrue(verify_kernel(a,k))
    def test_all_terminals(self):
        a = signed_laplacian(3, [(0,1,2),(1,2,-3),(0,2,4)])
        k = TerminalKernel.build(a,[0,1,2])
        for p in partitions(3):
            self.assertEqual(k.query(p), bareiss(quotient_cofactor(a,[0,1,2],p)))
    def test_nullity_gate(self):
        a = [[0]*5 for _ in range(5)]
        k = TerminalKernel.build(a,[3,4])
        self.assertEqual(k.nullity,3)
        for p in partitions(2):
            self.assertIsNone(k.reduced_matrix(p))
            self.assertEqual(k.query(p),0)
    def test_random_symmetric_all_partitions(self):
        rng = random.Random(42)
        for n in range(2,10):
            for _ in range(5):
                a = [[0]*n for _ in range(n)]
                for i in range(n):
                    for j in range(i,n):
                        a[i][j]=a[j][i]=rng.randrange(-2,3)
                b = rng.sample(range(n),min(n,4))
                k=TerminalKernel.build(a,b)
                self.assertTrue(verify_kernel(a,k))
                for p in partitions(len(b)):
                    self.assertEqual(k.query(p),bareiss(quotient_cofactor(a,b,p)))
    def test_tamper_detection(self):
        a=signed_laplacian(4,[(0,1,1),(1,2,-1),(2,3,1),(3,0,1)])
        k=TerminalKernel.build(a,[2,3])
        self.assertTrue(verify_kernel(a,k))
        self.assertFalse(verify_kernel(a,replace(k,factor=k.factor+1)))
    def test_sharp_nullity_family(self):
        # A subdivided star with opposite edge weights at each interior vertex.
        for r in range(1,13):
            edges=[(j,r,1) for j in range(r)]+[(j,r+j+1,-1) for j in range(r)]
            lap=signed_laplacian(2*r+1,edges)
            terminals=list(range(r,2*r+1))
            k=TerminalKernel.build(lap,terminals)
            self.assertEqual(k.nullity,r)
            self.assertEqual(k.query(list(range(r+1))),(-1)**r)
            if r:
                self.assertEqual(k.query([0,0]+list(range(2,r+1))),0)
    def test_critical_square_law(self):
        rng=random.Random(177)
        for r,b in [(1,5),(2,5),(3,5)]:
            # Weighted pendant edge of weight 2 makes det(P)=2.
            n=1+r+b; terminals=list(range(1+r,n))
            edges=[(0,terminals[0],2)]
            for j in range(r):
                weights=[rng.randrange(-3,4) for _ in range(b-1)]
                weights.append(-sum(weights))
                edges.extend((1+j,t,w) for t,w in zip(terminals,weights))
            edges.extend((terminals[j],terminals[j+1],1) for j in range(b-1))
            lap=signed_laplacian(n,edges); k=TerminalKernel.build(lap,terminals)
            self.assertEqual(k.nullity,r)
            self.assertEqual(k.factor,2)
            for part in partitions(b):
                if max(part)+1 != r+1: continue
                small=k.reduced_matrix(part)
                det=rational_det([row[r:] for row in small[:r]])
                expected=k.factor*(-1)**r*det**2
                self.assertEqual(k.query(part),expected)
                self.assertEqual(k.query(part),bareiss(quotient_cofactor(lap,terminals,part)))
    def test_invalid_matrix(self):
        with self.assertRaises(ValueError): TerminalKernel.build([[0,1],[2,0]],[1])
        with self.assertRaises(ValueError): TerminalKernel.build([[1]],[0,0])
    def test_graph_loops(self):
        self.assertEqual(signed_laplacian(1,[(0,0,-1)]),[[0]])


class DiagramTests(unittest.TestCase):
    def test_unlinks(self):
        for n in range(1,7):
            d=from_braid(n,[])
            self.assertEqual(d.euler_one(),2**(n-1))
            self.assertEqual(d.euler_i(),(1,0) if n==1 else (0,0))
    def test_curls_and_mirrors(self):
        for word in ([1],[-1],[1]*3,[-1]*3,[1,-1,1]):
            d=from_braid(2,word); poly=d.cube_polynomial()
            self.assertEqual(d.shadow_four(),tuple(sum(v for q,v in poly.items() if q%4==r) for r in range(4)))
    def test_named_ranks(self):
        for strands,word,rank in [(2,[1]*3,3),(3,[1,-2]*2,5),(3,[1,2]*5,7)]:
            self.assertEqual(reduced_homology(from_braid(strands,word))['rank'],rank)
    def test_disconnected_shadow(self):
        d=from_braid(4,[1,1,3,3])
        self.assertGreater(d.shadow_components(),1)
        self.assertEqual(d.euler_i(),(0,0))
    def test_cube_bound(self):
        rng=random.Random(35)
        for _ in range(40):
            b=rng.randrange(2,5)
            word=[rng.choice((-1,1))*rng.randrange(1,b) for _ in range(rng.randrange(1,8))]
            d=from_braid(b,word)
            h=reduced_homology(d)
            self.assertLessEqual(norm_four(d.shadow_four()),h['rank'])
    def test_invalid_incidence(self):
        with self.assertRaises(ValueError): Diagram(((0,1,2,3),))
        with self.assertRaises(ValueError): Diagram(())
    def test_positive_genus_rejected(self):
        with self.assertRaises(ValueError): Diagram(((0,1,0,1),))
    def test_complete_smoothing(self):
        d=from_braid(3,[1,-2,1,-2])
        from detshadow.diagram import SMOOTHINGS
        crossing=d.pd[0]
        for sm in SMOOTHINGS:
            pairs=[(crossing[a],crossing[b]) for a,b in sm]
            complete_matching(d.pd[1:],pairs).shadow_four()
    def test_geometry_certificate(self):
        from detshadow.geometry_certificate import verify_quotient_geometry
        for d in [from_braid(2,[1]*3),from_braid(3,[1,-2]*2),from_braid(3,[1,2]*5)]:
            v,edges,phase=d.tait_data(); lap=signed_laplacian(v,edges)
            self.assertEqual(verify_quotient_geometry(lap,list(range(v)),list(range(v)),d,list(range(v-1))),phase)
    def test_geometry_certificate_tamper(self):
        from detshadow.geometry_certificate import verify_quotient_geometry
        d=from_braid(2,[1]*3);v,edges,_=d.tait_data();lap=signed_laplacian(v,edges)
        lap[-1][-1]+=1
        with self.assertRaises(ValueError):
            verify_quotient_geometry(lap,list(range(v)),list(range(v)),d,list(range(v-1)))
    def test_reference_budget(self):
        with self.assertRaises(ValueError): from_braid(2,[1]*19).cube_polynomial()


class ContinuationTests(unittest.TestCase):
    def test_homogeneous_support(self):
        self.assertEqual(dot_degree((1<<1)|(1<<2)),1)
        with self.assertRaises(ValueError): dot_degree(3)
    def test_overlay(self):
        a=((0,1),(2,3)); b=((0,3),(1,2))
        self.assertEqual(overlay_circles(a,a),2)
        self.assertEqual(overlay_circles(a,b),1)
    def test_quantum_recovery(self):
        a=((0,1),)
        self.assertEqual(recover_quantum_shifts([a,a,a],[(0,1,2),(1,2,2)]),[0,2,4])
    def test_potential_cycle_failure(self):
        a=((0,1),)
        with self.assertRaises(ValueError): recover_quantum_shifts([a]*3,[(0,1,2),(1,2,2),(0,2,2)])
    def test_shift_isometry(self):
        v=(5,-7,3,1)
        for h in range(-4,4):
            for q in range(-8,8):
                self.assertEqual(norm_four(v),norm_four(shift_four(v,h,q)))
    def test_triangle(self):
        rng=random.Random(6)
        for _ in range(100):
            a=[rng.randrange(-10,11) for _ in range(4)]
            b=[rng.randrange(-10,11) for _ in range(4)]
            self.assertLessEqual(norm_four([x+y for x,y in zip(a,b)]),norm_four(a)+norm_four(b))
    def test_initial_observer(self):
        d=from_braid(2,[1]*3)
        scan=NS(mid=[0],deg=[0],out=[{}],algebra=NS(pairs=[()]))
        result=observe_scan(scan,d.pd,marked_label=d.pd[-1][0])
        self.assertEqual(result['reduced_rank_lower_bound'],3)
        self.assertEqual(result['reduced_euler_lower_bound'],1)
    def test_missing_mark(self):
        d=from_braid(2,[1])
        scan=NS(mid=[0],deg=[0],out=[{}],algebra=NS(pairs=[()]))
        with self.assertRaises(ValueError): observe_scan(scan,d.pd,marked_label=999)
    def test_multiplicity_not_f2(self):
        d=from_braid(2,[1]*3)
        scan=NS(mid=[0],deg=[0],out=[{}],algebra=NS(pairs=[()]),owner=[0],weights=[{0:2}])
        self.assertEqual(observe_scan(scan,d.pd,marked_label=d.pd[-1][0])['reduced_rank_lower_bound'],6)
    def test_saturated_threshold_metadata(self):
        d=from_braid(2,[1])
        scan=NS(mid=[0],deg=[0],out=[{}],algebra=NS(pairs=[()]),owner=[0],weights=[{0:3}],rank_cap=3)
        result=observe_scan(scan,d.pd,marked_label=d.pd[-1][0])
        self.assertEqual(result['reduced_rank_lower_bound_capped'],2)
        self.assertTrue(result['multiplicities_saturated'])
        self.assertEqual(result['monotonicity_applies_to'],'capped_at_two')
        scan.rank_cap=1
        with self.assertRaises(ValueError): observe_scan(scan,d.pd,marked_label=d.pd[-1][0])
    def test_abstract_strict_witness(self):
        # A connected dotted block closes to Euler 1-q^2. Two shifted copies
        # and an interval have total shadow norm 1 but split shadow norm 5.
        v=(1,0,-1,0); w=shift_four(v,1,4); unit=(1,0,0,0)
        self.assertEqual(norm_four(tuple(a+b+c for a,b,c in zip(v,w,unit))),1)
        self.assertEqual(norm_four(v)+norm_four(w)+norm_four(unit),5)
        self.assertEqual(abs(sum(v))+abs(sum(w))+abs(sum(unit)),1)


if __name__=='__main__': unittest.main()
