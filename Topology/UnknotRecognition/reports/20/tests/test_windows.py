from __future__ import annotations
import random
import unittest
from itertools import product
from collections import Counter
from unknot_windows import Diagram, DiagramError, ScanLimit, low_window, probe, adaptive_probe
from unknot_windows.cube import cube_ranks
from unknot_windows.algebra import BitAlgebra, bits
from unknot_windows.orders import nice_order, certify, OrderError
from unknot_windows.scanner import ScanComplex
from unknot_windows.windows import erase_above

def matchings(points):
    if not points:
        yield frozenset()
        return
    a = points[0]
    for j in range(1, len(points), 2):
        for x in matchings(points[1:j]):
            for y in matchings(points[j+1:]):
                yield x | y | frozenset((frozenset((a, points[j])),))

def random_knots(seed=20261007, count=80, max_crossings=9):
    rng = random.Random(seed)
    out, seen = [], set()
    while len(out) < count:
        b = rng.randint(2, 4)
        n = rng.randint(max(1, b-1), max_crossings)
        word = tuple(rng.choice((-1, 1)) * rng.randint(1, b-1) for _ in range(n))
        if (b,word) in seen:
            continue
        seen.add((b,word))
        try:
            d = Diagram.from_braid(b,word)
        except DiagramError:
            continue
        out.append((b,word,d))
    return out

class AlgebraTests(unittest.TestCase):
    def test_weight_homogeneity_exhaustive(self):
        for m in range(4):
            aa = list(matchings(tuple(range(2*m))))
            alg = BitAlgebra()
            for a,b,c in product(aa,repeat=3):
                p,q,r = [len(alg.basis(x,y)[0]) for x,y in ((a,b),(b,c),(a,c))]
                for f in range(1<<p):
                    for g in range(1<<q):
                        result = alg.compose(1<<f,1<<g,a,b,c)
                        weight = 2*m-p-q+2*(f.bit_count()+g.bit_count())
                        for h in bits(result):
                            self.assertEqual(m-r+2*h.bit_count(),weight)
    def test_endomorphism_units(self):
        for m in range(4):
            a=next(matchings(tuple(range(2*m))))
            alg=BitAlgebra()
            for f in range(1<<(1<<m)):
                self.assertEqual(alg.compose(f,f,a,a,a),f&1)
    def test_off_diagonal_backtracks_are_radical(self):
        for m in range(1,4):
            aa=list(matchings(tuple(range(2*m))))
            alg=BitAlgebra()
            for a,b in product(aa,repeat=2):
                if a==b: continue
                p=len(alg.basis(a,b)[0])
                for f in range(1<<p):
                    for g in range(1<<p):
                        self.assertFalse(alg.compose(1<<f,1<<g,a,b,a)&1)

class WindowTests(unittest.TestCase):
    def test_known_knots(self):
        expected=[(2,[1],{1:2}), (2,[-1],{0:2}),
                  (2,[1]*3,{0:2,1:2,3:2}),
                  (3,[1,-2]*2,{0:2,1:2,2:2,3:2,4:2})]
        for b,w,ranks in expected:
            d=Diagram.from_braid(b,w)
            self.assertEqual(cube_ranks(d),ranks)
            self.assertEqual(low_window(d,len(w)).ranks,ranks)
    def test_crossing_free(self):
        d=Diagram.from_pd([])
        self.assertEqual(low_window(d,0).ranks,{0:2})
        self.assertEqual(probe(d,0).verdict,'UNKNOT')
    def test_halodegree_is_not_reported(self):
        d=Diagram.from_braid(2,[1])
        self.assertEqual(low_window(d,0).ranks,{})
        # Omitting degree k+1 produces a spurious rank 2 in degree zero.
        s=ScanComplex(); s.add_crossing(d.pd[0],reduce_now=False)
        erase_above(s,0); s.eliminate()
        self.assertEqual(s.linear_ranks(),{0:2})
        self.assertNotEqual(s.linear_ranks(),low_window(d,0).ranks)
    def test_random_cubes_and_all_small_windows(self):
        rng=random.Random(99)
        for b,w,d in random_knots():
            full=cube_ranks(d)
            n=len(w)
            order=list(range(n)); rng.shuffle(order)
            for k in sorted({0,1,2,min(3,n),n}):
                expected={h:v for h,v in full.items() if h<=k}
                self.assertEqual(low_window(d,k).ranks,expected,(b,w,k))
                self.assertEqual(low_window(d,k,order=order,pivot='lifo').ranks,expected,(b,w,k,order))
            self.assertEqual(low_window(d.mirror(),n).ranks,{n-h:v for h,v in full.items()})
    def test_pivot_independent_matching_profiles(self):
        for _,w,d in random_knots(seed=88,count=30,max_crossings=8):
            for k in (1,len(w)):
                a=low_window(d,k,pivot='minfill',trace=True)
                b=low_window(d,k,pivot='lifo',trace=True)
                self.assertEqual([x['matching_profile'] for x in a.stages],
                                 [x['matching_profile'] for x in b.stages])
    def test_nice_order_binomial_invariant(self):
        successful=0
        for _,w,d in random_knots(seed=73,count=60,max_crossings=9):
            try: cert=nice_order(d.pd)
            except OrderError: continue
            if not cert.nice: continue
            successful+=1
            self.assertTrue(cert.nice)
            for k in (0,1,2,len(w)):
                low_window(d,k,order=cert.order,trace=True,assert_binomial=True)
        self.assertGreater(successful,5)
    def test_signs_from_pd_not_braid_word(self):
        # The audited converter's generator naming and its derived sign
        # convention differ. Never substitute sum(g<0) for PD-derived n_minus.
        for w in ([1],[-1],[1,1,-1]):
            d=Diagram.from_braid(2,w)
            ranks=cube_ranks(d)
            nneg=sum(s<0 for s in d.signs())
            self.assertEqual(ranks,{nneg:2})
            self.assertEqual(adaptive_probe(d).verdict,'UNKNOT')
    def test_probe_never_infers_unknot_from_partial_agreement(self):
        found_unknown=False
        for _,w,d in random_knots(seed=2026,count=50,max_crossings=8):
            ranks=cube_ranks(d)
            expected='UNKNOT' if sum(ranks.values())==2 else 'NONTRIVIAL'
            r=probe(d,0)
            if r.verdict=='UNKNOWN': found_unknown=True
            else: self.assertEqual(r.verdict,expected)
            self.assertEqual(adaptive_probe(d).verdict,expected)
        self.assertTrue(found_unknown)
    def test_limits_are_unknown(self):
        d=Diagram.from_braid(2,[1]*3)
        self.assertEqual(probe(d,2,max_objects=0).verdict,'UNKNOWN')
    def test_bad_inputs(self):
        with self.assertRaises(DiagramError): Diagram.from_pd([[1,2,3,4]])
        with self.assertRaises(DiagramError): Diagram.from_braid(2,[1,1])
        d=Diagram.from_braid(2,[1]*3)
        with self.assertRaises(ValueError): low_window(d,-1)
        with self.assertRaises(OrderError): low_window(d,1,order=[0,0,1])
        with self.assertRaises(ValueError): probe(d,1,seconds=-1)
        with self.assertRaises(ValueError): adaptive_probe(d,max_depth=2.5)
        with self.assertRaises(ValueError): adaptive_probe(d,seconds=-1)
    def test_explicit_examples(self):
        d=Diagram.from_braid(3,[1,2]*4)
        self.assertEqual(probe(d,0).verdict,'UNKNOWN')
        self.assertEqual(adaptive_probe(d).verdict,'NONTRIVIAL')

if __name__=='__main__': unittest.main()
