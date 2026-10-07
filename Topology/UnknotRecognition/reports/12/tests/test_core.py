from __future__ import annotations
import itertools, random, unittest
from unknot_frobenius.subset import *
from unknot_frobenius.kernel import *
from unknot_frobenius.blocks import *

class SubsetTests(unittest.TestCase):
    def test_exhaustive_three_variables(self):
        # 65,536 products, including dense and correlated polynomials.
        b=3
        for f in range(1 << (1 << b)):
            for g in range(1 << (1 << b)):
                expected=subset_product_sparse(f,g,b,polarize=False)
                self.assertEqual(subset_product_fast(f,g,b),expected)
                self.assertEqual(subset_product_sparse(f,g,b),expected)

    def test_random_larger(self):
        rng=random.Random(20261007)
        for b in range(0,10):
            for _ in range(20):
                f,g=rng.getrandbits(1<<b),rng.getrandbits(1<<b)
                self.assertEqual(subset_product(f,g,b),subset_product_fast(f,g,b))
                self.assertEqual(subset_product_sparse(f,g,b),subset_product_fast(f,g,b))

    def test_validation_and_budget(self):
        for f,b in [(-1,2),(16,2),(True,2),(1,-1)]:
            with self.assertRaises(ValueError): subset_product(f,1,b)
        with self.assertRaises(MemoryError): subset_product(2,3,4,method="fast",dense_limit=3)
        def stop(): raise TimeoutError("test cancellation")
        with self.assertRaises(TimeoutError): subset_product_fast(7,11,3,check=stop)
        with self.assertRaises(TimeoutError): subset_product_sparse(7,11,3,check=stop)

    def test_representation(self):
        for b in range(9):
            f=random.Random(b).getrandbits(1<<b)
            self.assertEqual(pack(support(f),b),f)
        self.assertEqual(pack([1,1],2),0)
        with self.assertRaises(ValueError): pack([4],2)

class PlanTests(unittest.TestCase):
    def test_closed_and_fixed_dots(self):
        for left,right,boundary in [(1,1,0),(3,1,3),(0,0,1),(0,0,0),(3,3,7)]:
            for extra in range(3):
                p=((left,right,boundary,extra),)
                cp=CompiledPlan.from_plan(p)
                for f in range(1 << (1 << left.bit_length())):
                    for g in range(1 << (1 << right.bit_length())):
                        expected=contract_reference(p,f,g)
                        self.assertEqual(cp.apply(f,g,method="fast"),expected)
                        self.assertEqual(cp.apply(f,g,method="sparse"),expected)

    def test_random_tensor_plans(self):
        rng=random.Random(982734)
        for _ in range(150):
            c=rng.randrange(1,5)
            masks=[[0]*c for _ in range(3)]
            for axis in range(3):
                for bit in range(rng.randrange(0,7)):
                    masks[axis][rng.randrange(c)] |= 1 << bit
            p=tuple((masks[0][j],masks[1][j],masks[2][j],rng.randrange(2)) for j in range(c))
            cp=CompiledPlan.from_plan(p)
            for _ in range(6):
                f=rng.getrandbits(1<<len(cp.left_owner));g=rng.getrandbits(1<<len(cp.right_owner))
                self.assertEqual(cp.apply(f,g,method="fast"),contract_reference(p,f,g))

    def test_quotient_collisions_and_lift_injectivity(self):
        p=((3,1,3,0),(4,2,4,0))
        cp=CompiledPlan.from_plan(p)
        # x0+x1 becomes z0+z0=0.
        self.assertEqual(cp.project((1<<1)^(1<<2),0),0)
        self.assertEqual(cp.project(1<<3,0),0)
        images=[cp.lift(1<<s) for s in range(4)]
        for i in range(4):
            for j in range(i): self.assertEqual(images[i]&images[j],0)
        self.assertTrue(all(images))

    def test_invalid_plans(self):
        for p in [((1,0,1,0),(1,0,2,0)),((2,0,1,0),),((1,0,1,-1),),((1,2,3),)]:
            with self.assertRaises(ValueError): CompiledPlan.from_plan(p)
        self.assertEqual(contract(None,1,1),0)
        with self.assertRaises(ValueError): contract(None,-1,1)
        with self.assertRaises(ValueError): contract((),1,1,dense_limit=-1)
        self.assertEqual(contract((),1,1),1)

class BlockTests(unittest.TestCase):
    def test_scalar_involutions(self):
        rng=random.Random(20261)
        for b in range(5):
            for _ in range(30):
                f=rng.getrandbits(1<<b)|1
                self.assertEqual(unit_inverse(((f,),),b),((f,),))

    def test_matrix_not_an_involution(self):
        x,y=1<<1,1<<2
        a=matrix([[1,x,0],[0,1,y],[0,0,1]])
        inv=unit_inverse(a,2)
        self.assertNotEqual(inv,a)
        self.assertEqual(inv[0][2],1<<3)

    def test_sharp_nilpotence(self):
        for b in range(1,8):
            n=b+1
            a=matrix([[int(i==j) ^ ((1<<(1<<i)) if j==i+1 else 0) for j in range(n)] for i in range(n)])
            inv=unit_inverse(a,b)
            self.assertEqual(inv[0][-1],1<<((1<<b)-1))

    def test_random_inverses(self):
        rng=random.Random(7745)
        for b in range(5):
            for n in range(1,5):
                for _ in range(5):
                    const=[list(row) for row in identity(n)]
                    for _ in range(10):
                        i,j=rng.randrange(n),rng.randrange(n)
                        if i!=j: const[i]=[x^y for x,y in zip(const[i],const[j])]
                    a=matrix([[const[i][j] | (rng.getrandbits(1<<b)&~1) for j in range(n)] for i in range(n)])
                    inv=unit_inverse(a,b)
                    self.assertEqual(mul(a,inv,b),identity(n))

    def test_interface_equals_full_schur(self):
        rng=random.Random(443256)
        for b in range(1,5):
            for n,r,p,q in [(4,1,2,3),(6,2,3,2),(3,3,2,2)]:
                u=matrix([[rng.getrandbits(1<<b)&~1 for _ in range(r)] for _ in range(n)])
                v=matrix([[rng.getrandbits(1<<b) for _ in range(n)] for _ in range(r)])
                c=matrix([[rng.getrandbits(1<<b) for _ in range(q)] for _ in range(n)])
                d=matrix([[rng.getrandbits(1<<b) for _ in range(n)] for _ in range(p)])
                e=matrix([[rng.getrandbits(1<<b) for _ in range(q)] for _ in range(p)])
                a=add(identity(n),mul(u,v,b))
                self.assertEqual(low_rank_interface(identity(n),u,v,c,d,e,b).evaluate(b),schur(a,c,d,e,b))

    def test_rejections(self):
        with self.assertRaises(ValueError): unit_inverse(((2,),),1)
        with self.assertRaises(ValueError): matrix([[1],[1,2]])
        with self.assertRaises(ValueError): InterfaceData(((1,),),((1,),),((1,),),((0,),)).evaluate(1)

if __name__ == '__main__': unittest.main()
