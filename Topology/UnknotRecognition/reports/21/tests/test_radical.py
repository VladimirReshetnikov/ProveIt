from pathlib import Path
import copy
import random
import sys
import unittest
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'experiments'))
from common import *
from fastunknot.planar import Planar
from fastunknot.geometry import ScanLimit
from radical import *
from disk_frontier import *


def matchings(points):
    if not points:
        yield ()
        return
    a = points[0]
    for pos in range(1, len(points), 2):
        for left in matchings(points[1:pos]):
            for right in matchings(points[pos + 1:]):
                yield tuple(sorted(((a, points[pos]),) + left + right))


def category(b):
    alg = Planar(False)
    ids = [alg.intern(x) for x in matchings(tuple(range(2*b)))]
    return alg, ids


def two_term(b, size, seed, mixed=False):
    rng = random.Random(seed)
    alg, ids = category(b)
    mids = [rng.choice(ids) if mixed else ids[0] for _ in range(2*size)]
    out = [{} for _ in mids]
    for j in range(size):
        for k in range(size, 2*size):
            circles = alg.basis(mids[j], mids[k])[1]
            f = rng.getrandbits(1 << circles)
            if f:
                out[j][k] = f
    return alg, Complex(mids, [0]*size+[1]*size, out)


def as_scan(c, alg):
    scan = FastScan(shape_cache=False)
    scan.algebra = alg
    scan.mid, scan.deg, scan.out = c.mid[:], c.deg[:], copy.deepcopy(c.out)
    scan.inc = [set() for _ in c.mid]
    for j, row in enumerate(c.out):
        for k in row:
            scan.inc[k].add(j)
    scan.live = c.n
    scan.points = frozenset(x for pair in alg.pairs[c.mid[0]] for x in pair) if c.n else frozenset()
    return scan


def conjugated_three_term(seed):
    rng = random.Random(seed)
    alg, ids = category(2)
    m = ids[0]
    # Degrees 0,1,2 have three objects each. Two disjoint scalar pairs
    # and a three-term residual x-complex (x*x=0).
    c = Complex([m]*9, [0]*3+[1]*3+[2]*3, [{} for _ in range(9)])
    c.out[0][3] = 1
    c.out[4][6] = 1
    c.out[1][5] = 2
    c.out[5][7] = 2
    identity = [{j:1} for j in range(9)]
    T = [{} for _ in range(9)]
    for j in range(9):
        for k in range(9):
            if c.deg[j] == c.deg[k]:
                value = rng.getrandbits(4) & ~1
                if value:
                    T[j][k] = value
    U = add_maps(identity,T)
    T2 = compose_maps(c.mid,c.mid,c.mid,T,T,alg)
    inv = add_maps(identity,T,T2)  # diagonal radical cubed = 0 for b=2
    assert compose_maps(c.mid,c.mid,c.mid,U,inv,alg) == identity
    out = compose_maps(c.mid,c.mid,c.mid,inv,c.out,alg)
    out = compose_maps(c.mid,c.mid,c.mid,out,U,alg)
    return alg, Complex(c.mid,c.deg,out)


class BinaryTests(unittest.TestCase):
    def test_basis_coordinates(self):
        basis=BinaryBasis()
        self.assertTrue(basis.add(3,1)[0]); self.assertTrue(basis.add(6,2)[0])
        self.assertEqual(basis.solve(5),3)
        with self.assertRaises(ArithmeticError): basis.solve(1)

    def test_off_diagonal_bit_zero_is_not_scalar(self):
        alg,ids=category(2)
        c=Complex(ids[:2],[0,1],[{1:1},{}])
        self.assertEqual(scalar_part(c),[0,0])
        red=reduce_complex(c,alg,certificate=True)
        self.assertEqual(red.complex.out,c.out)
        verify_reduction(c,red,alg)

    def test_binary_profile_closed(self):
        c=Complex([0]*4,[0,0,1,1],[{2:1,3:1},{2:1,3:1},{},{}])
        self.assertEqual(binary_profile(c),{(0,0):1,(0,1):1})

    def test_scalar_contractions_random(self):
        for seed in range(40):
            alg,c=two_term(0,1+seed%9,seed)
            sc=contract_scalar(c,verify=True)
            self.assertEqual(sc.r,sum(binary_profile(c).values()))

    def test_three_term_scalar_splitting(self):
        for seed in range(15):
            alg,c=conjugated_three_term(seed)
            contract_scalar(c,verify=True)

    def test_reject_d0_squared(self):
        c=Complex([0]*3,[0,1,2],[{1:1},{2:1},{}])
        with self.assertRaises(ArithmeticError): contract_scalar(c)

    def test_empty(self):
        alg=Planar(False); c=Complex([],[],[])
        red=reduce_complex(c,alg,certificate=True)
        self.assertEqual(red.complex.n,0)
        verify_reduction(c,red,alg)

    def test_bad_homological_degree(self):
        with self.assertRaises(ValueError):
            contract_scalar(Complex([0,0],[0,0],[{1:1},{}]))


class AlgebraTests(unittest.TestCase):
    def test_grading_exhaustive_up_to_six_points(self):
        for b in range(4):
            alg,ids=category(b)
            for a in ids:
                for middle in ids:
                    k1=alg.basis(a,middle)[1]
                    for c in ids:
                        k2=alg.basis(middle,c)[1]
                        k3=alg.basis(a,c)[1]
                        for f in range(1<<k1):
                            for g in range(1<<k2):
                                v=alg.compose(a,middle,c,1<<f,1<<g)
                                degree=2*b-k1-k2+2*(f.bit_count()+g.bit_count())
                                for monomial in bits(v):
                                    self.assertEqual(b-k3+2*monomial.bit_count(),degree)

    def test_identity_and_square_free_ring(self):
        for b in range(1,6):
            alg,ids=category(b); a=ids[0]
            for j in range(b):
                x=1<<(1<<j)
                self.assertEqual(alg.compose(a,a,a,1,x),x)
                self.assertEqual(alg.compose(a,a,a,x,x),0)
            f=(1<<(1<<b))-1
            self.assertEqual(alg.compose(a,a,a,f,f),1)

    def test_radical_nilpotence_random_products(self):
        rng=random.Random(1903)
        for b in range(1,5):
            alg,ids=category(b)
            for rep in range(100):
                source=middle=rng.choice(ids); value=1
                for _ in range(2*b):
                    target=rng.choice(ids)
                    g=rng.getrandbits(1<<alg.basis(middle,target)[1])
                    if middle==target: g &= ~1
                    value=alg.compose(source,middle,target,value,g)
                    middle=target
                self.assertEqual(value,0)

    def test_sharp_radical_index(self):
        for b in range(1,9):
            alg=Planar(False); ids=[]
            for r in range(b):
                pairs=[(0,2*r+1)]+[(2*j-1,2*j) for j in range(1,r+1)]
                pairs += [(2*j,2*j+1) for j in range(r+1,b)]
                ids.append(alg.intern(tuple(sorted(pairs))))
            path=ids+list(reversed(ids))
            factors=[1]*(b-1)+[2]+[1]*(b-1)
            value=1
            for j,g in enumerate(factors):
                value=alg.compose(ids[0],path[j],path[j+1],value,g)
            self.assertEqual(value,1<<((1<<b)-1))
            self.assertEqual(len(factors),2*b-1)

    def test_same_profile_does_not_mean_same_complex(self):
        alg,ids=category(1); a=ids[0]
        c=Complex([a,a],[0,1],[{1:2},{}])
        z=Complex([a,a],[0,1],[{},{}])
        self.assertEqual(binary_profile(c),binary_profile(z))
        self.assertNotEqual(c.out,z.out)
        # Closing the arc makes x multiplication on A: matrix [[0,0],[1,0]].
        closed_x=Complex([0]*4,[0,0,1,1],[{3:1},{},{},{}])
        closed_z=Complex([0]*4,[0,0,1,1],[{},{},{},{}])
        self.assertEqual(sum(binary_profile(closed_x).values()),2)
        self.assertEqual(sum(binary_profile(closed_z).values()),4)


class PerturbationTests(unittest.TestCase):
    def test_random_ring_certificates(self):
        for seed in range(60):
            alg,c=two_term(1+seed%3,1+seed%4,seed)
            red=reduce_complex(c,alg,certificate=True)
            verify_reduction(c,red,alg)
            self.assertEqual(red.complex.n,sum(binary_profile(c).values()))

    def test_random_multimatching_certificates(self):
        for seed in range(60):
            alg,c=two_term(2+seed%2,1+seed%4,1000+seed,True)
            red=reduce_complex(c,alg,certificate=True)
            verify_reduction(c,red,alg)

    def test_nontrivial_three_term_certificates(self):
        for seed in range(30):
            alg,c=conjugated_three_term(seed)
            red=reduce_complex(c,alg,certificate=True)
            verify_reduction(c,red,alg)
            self.assertEqual(red.complex.n,5)

    def test_against_scalar_pivots(self):
        for seed in range(50):
            alg,c=two_term(2,2+seed%5,seed,True)
            expected=binary_profile(c)
            scan=as_scan(c,alg)
            scan.eliminate(); scan.check_d_squared()
            got=defaultdict(int)
            for j,m in enumerate(scan.mid):
                if m is not None: got[m,scan.deg[j]]+=1
            self.assertEqual(dict(got),expected)

    def test_minimal_unchanged(self):
        alg,ids=category(1); a=ids[0]
        c=Complex([a,a],[0,1],[{1:2},{}])
        red=reduce_complex(c,alg,certificate=True)
        self.assertEqual(red.complex.out,c.out)
        verify_reduction(c,red,alg)

    def test_acyclic_unit_plus_dot(self):
        alg,ids=category(1); a=ids[0]
        c=Complex([a,a],[0,1],[{1:3},{}])
        red=reduce_complex(c,alg,certificate=True)
        self.assertEqual(red.complex.n,0)
        verify_reduction(c,red,alg)

    def test_reject_out_of_basis(self):
        alg,ids=category(1); a=ids[0]
        with self.assertRaises(ValueError):
            reduce_complex(Complex([a,a],[0,1],[{1:4},{}]),alg)

    def test_nilpotence_failure_is_not_silent(self):
        alg,ids=category(1); a=ids[0]
        c=Complex([a]*4,[0,0,1,1],[{2:3,3:2},{2:2},{},{}])
        with self.assertRaises(ArithmeticError):
            reduce_complex(c,alg,compose=lambda *args: 2)

    def test_corrupt_certificate_rejected(self):
        alg,c=two_term(2,3,22,True)
        red=reduce_complex(c,alg,certificate=True)
        red.homotopy[0][0]=1
        with self.assertRaises(ArithmeticError): verify_reduction(c,red,alg)

    def test_no_certificate_has_no_dense_maps(self):
        alg,c=two_term(2,4,5)
        red=reduce_complex(c,alg)
        self.assertIsNone(red.inclusion)
        self.assertIsNone(red.projection)
        self.assertIsNone(red.homotopy)


class DiagramTests(unittest.TestCase):
    def test_named_diagrams_all_modes(self):
        for s,w in [(2,[1]),(2,[1]*3),(3,[1,-2]*2),(2,[1,-1]),(3,[1,2]*2)]:
            pd=braid_pd(s,w); expected=cube_ranks(pd)
            for mode in ('always','auto','terminal'):
                scan=scan_pd(pd,RadicalScan,mode=mode,check=True)
                self.assertEqual(scan.ranks_by_degree(),expected)

    def test_random_diagrams_against_independent_cube(self):
        rng=random.Random(20261007)
        for sample in range(100):
            s=rng.choice((2,3,4))
            n=rng.randint(s-1,8)
            word=list(range(1,s))+[rng.choice((-1,1))*rng.randint(1,s-1) for _ in range(n-s+1)]
            rng.shuffle(word)
            pd=braid_pd(s,word); expected=cube_ranks(pd)
            order=list(range(n)); rng.shuffle(order)
            for cls,kwargs in [(FastScan,{}),(RadicalScan,dict(mode='always'))]:
                scan=scan_pd(pd,cls,order=order,check=True,**kwargs)
                self.assertEqual(scan.ranks_by_degree(),expected,(s,word,order))

    def test_prefix_profiles_are_identical(self):
        rng=random.Random(481)
        for sample in range(40):
            s=3; word=[1,2]+[rng.choice((-2,-1,1,2)) for _ in range(6)]
            pd=braid_pd(s,word)
            a=FastScan(shape_cache=False); b=RadicalScan(shape_cache=False,mode='always')
            order=list(range(len(pd))); rng.shuffle(order)
            for j in order:
                a.add_crossing(pd[j]); b.add_crossing(pd[j])
                self.assertEqual(profile(a),profile(b))

    def test_prefix_full_homotopy_certificates(self):
        scan=FastScan(shape_cache=False)
        prefix=[]
        for crossing in braid_pd(3,[1,-2,1,-2,1]):
            prefix.append(crossing)
            scan.add_crossing(crossing,reduce_now=False)
            c=snapshot(scan)
            red=reduce_complex(c,scan.algebra,certificate=True,cyclic_order=certify_disk(prefix).cyclic_order)
            verify_reduction(c,red,scan.algebra)
            scan.eliminate()

    def test_long_trefoil_family(self):
        local=open_edge(braid_pd(2,[1,1,1]))
        for k in range(1,6):
            pd,_=concatenate_tangles([local]*k)
            scan=scan_pd(pd,RadicalScan,mode='always',check=True)
            self.assertEqual(scan.live,3**k)
            self.assertFalse(any(scan.out))
            self.assertLessEqual(scan.stats['max_boundary'],6)

    def test_shape_cache(self):
        pd=braid_pd(3,[1,2,-1,-2]*3)
        a=FastScan(shape_cache=True); b=RadicalScan(shape_cache=True,mode='always')
        for crossing in pd:
            a.add_crossing(crossing); b.add_crossing(crossing)
        self.assertEqual(a.ranks_by_degree(),b.ranks_by_degree())

    def test_auto_gate_falls_back(self):
        scan=scan_pd(braid_pd(3,[1,-2]*3),RadicalScan,mode='auto',min_objects=0,residual_fraction=0)
        self.assertGreater(scan.stats['radical_fallbacks'],0)

    def test_object_limit(self):
        scan=RadicalScan(max_objects=0,mode='always')
        with self.assertRaises(ScanLimit): scan.add_crossing((0,1,2,3))

    def test_deadline_or_hook_preserves_original(self):
        scan=RadicalScan(mode='always',shape_cache=False)
        scan.add_crossing((0,1,2,3),reduce_now=False)
        before=copy.deepcopy((scan.mid,scan.deg,scan.out,scan.inc,scan.live))
        calls=[0]
        def hook():
            calls[0]+=1
            if calls[0]>=3: raise ScanLimit('test cancellation')
        scan.hook=hook
        with self.assertRaises(ScanLimit): scan.eliminate()
        self.assertEqual((scan.mid,scan.deg,scan.out,scan.inc,scan.live),before)

    def test_invalid_mode(self):
        with self.assertRaises(ValueError): RadicalScan(mode='guess')

    def test_no_knot_verdict_for_links(self):
        scan=scan_pd(braid_pd(2,[1,-1]),RadicalScan,mode='always')
        self.assertEqual(scan.total_rank(),4)
        # Adapter has deliberately no recognize/verdict method.
        self.assertFalse(hasattr(scan,'recognize'))

if __name__=='__main__': unittest.main()
