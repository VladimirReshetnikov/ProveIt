from pathlib import Path
import sys, unittest, random
ROOT=Path(__file__).resolve().parents[1]
sys.path[:0]=[str(ROOT/'code'),str(ROOT/'vendor'),str(ROOT/'tests')]
from radical import *
from braid_scan import scan_braid
from reference_cube import cube_homology
from fixtures import sharp_transfer_complex, gauge_complex

class RadicalTests(unittest.TestCase):
    def test_zero_complex(self):
        a=ArcAlgebra(); d=zero((),()); t=transfer(d,a,certificate=True)
        self.assertTrue(all(check_contraction(t,a).values()))
    def test_zero_boundary(self):
        a=ArcAlgebra(); obs=(Obj(0,0),Obj(0,1),Obj(0,1)); d=Mat(obs,obs,[{1:1},{},{}])
        t=transfer(d,a,certificate=True); self.assertEqual(len(t.d.src),1)
        check_contraction(t,a)
    def test_nilpotent_dot(self):
        a=ArcAlgebra(); m=a.intern(((0,1),)); self.assertEqual(a.compose(m,m,m,2,2),0)
    def test_bad_shape(self):
        with self.assertRaises(ValueError): Mat((Obj(0,0),),(),[])
    def test_negative_entry(self):
        with self.assertRaises(ValueError): Mat((Obj(0,0),),(Obj(0,0),),[{0:-1}])
    def test_wrong_degree(self):
        a=ArcAlgebra(); obs=(Obj(0,0),)
        with self.assertRaises(ValueError): transfer(Mat(obs,obs,[{0:1}]),a)
    def test_not_a_complex(self):
        a=ArcAlgebra(); obs=tuple(Obj(0,j) for j in range(3))
        with self.assertRaises(ValueError): transfer(Mat(obs,obs,[{1:1},{2:1},{}]),a)
    def test_wrong_morphism_basis(self):
        a=ArcAlgebra(); obs=(Obj(0,0),Obj(0,1))
        with self.assertRaises(ValueError): transfer(Mat(obs,obs,[{1:2},{}]),a)
    def test_resource_limit(self):
        a=ArcAlgebra(); d=zero((Obj(0,0),),(Obj(0,0),))
        with self.assertRaises(MemoryError): transfer(d,a,survivor_limit=0)
        with self.assertRaises(ValueError): transfer(d,a,survivor_limit=-1)
        with self.assertRaises(ValueError): transfer(d,a,survivor_limit=True)
    def test_sharp_series(self):
        for k in range(1,7):
            a=ArcAlgebra(); d=sharp_transfer_complex(a,k); t=transfer(d,a,certificate=True)
            self.assertEqual(t.series_depth,2*k-2); check_contraction(t,a)
    def test_random_certificate(self):
        for seed in range(20):
            a=ArcAlgebra(); d=gauge_complex(a,3,seed); t=transfer(d,a,certificate=True)
            check_contraction(t,a)
            self.assertEqual(survivor_profile(d),survivor_profile(pivot_reduce(d,a)))
    def test_block_units_are_not_involutions(self):
        a=ArcAlgebra(); m=a.intern(((0,1),(2,3))); obs=(Obj(m,0),Obj(m,0))
        N=Mat(obs,obs,[{1:2},{0:4}]); one=identity(obs); N2=mul(N,N,a)
        self.assertFalse(N2.is_zero()); self.assertTrue(mul(N2,N,a).is_zero())
        unit=add(one,N); inv=add(unit,N2)
        self.assertNotEqual(mul(unit,unit,a),one); self.assertEqual(mul(unit,inv,a),one)
    def test_derivative_squared(self):
        rng=random.Random(456)
        for _ in range(100): self.assertEqual(derivative(derivative(rng.getrandbits(64))),0)
    def test_marked_splitting(self):
        a=ArcAlgebra(); rng=random.Random(789)
        for k in range(1,5):
            ms=[a.intern(m) for m in matchings(tuple(range(2*k)))]
            for _ in range(60):
                u,v=rng.choice(ms),rng.choice(ms); own,c=a.basis(u,v)
                f=rng.getrandbits(1<<c); df=derivative(f); bit=1<<own[0]
                def z(g):
                    out=0
                    for S in bits(g):
                        if not S&bit: out ^= 1<<(S|bit)
                    return out
                self.assertEqual(derivative(z(f))^z(df),f)
                f0=f^z(df); self.assertEqual(derivative(f0),0)
                self.assertEqual(f0^z(df),f)
    def test_braid_known(self):
        for b,w,rank in [(1,[],2),(2,[1,1,1],6),(3,[1,-2,1,-2],10),(3,[1,2,-1,-2],2)]:
            r=scan_braid(b,w,certificate=True); self.assertEqual(r['unreduced_rank'],rank)
    def test_braid_invalid(self):
        for b,w in [(0,[]),(2,[0]),(2,[2]),(2,[1.0])]:
            with self.assertRaises(ValueError): scan_braid(b,w)
    def test_missing_certificate(self):
        a=ArcAlgebra(); d=zero((),())
        with self.assertRaises(ValueError): check_contraction(transfer(d,a),a)

if __name__=='__main__': unittest.main()
