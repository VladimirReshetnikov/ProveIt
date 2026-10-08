import random,unittest
from unknot_frobenius.tensors import *
from unknot_frobenius.blocks import *
from unknot_frobenius.subset import subset_product

def make_vector(rng,b,m,s,radical=False):
    # Factors with at least one unit make useful nontrivial long examples.
    terms=[]
    for _ in range(s):
        weight=rng.getrandbits(1<<b)
        if radical: weight&=~1
        factors=[]
        for _ in range(m):
            # Constant binary factors avoid accidental nilpotent extinction
            # while retaining a nontrivial product-tensor sum representation.
            factors.append(rng.choice(((1,0),(0,1),(1,1))))
        terms.append(TensorTerm(weight,tuple(factors)))
    return TensorVector(b,m,tuple(terms))

class TensorTests(unittest.TestCase):
    def test_pairings_against_expansion(self):
        rng=random.Random(903200)
        for b in range(4):
            for m in range(7):
                for _ in range(3):
                    def general():
                        return TensorVector(b,m,tuple(TensorTerm(rng.getrandbits(1<<b),tuple((rng.getrandbits(1<<b),rng.getrandbits(1<<b)) for _ in range(m))) for _ in range(3)))
                    a,z=general(),general();expected=0
                    for x,y in zip(a.expand(),z.expand()): expected^=subset_product(x,y,b)
                    self.assertEqual(a.pairing(z),expected)

    def test_schur_against_full_matrix(self):
        rng=random.Random(80932)
        for m in range(5):
            b=3;r=2;p=q=2;n=1<<m
            u=tuple(make_vector(rng,b,m,3,True) for _ in range(r))
            v=tuple(make_vector(rng,b,m,3) for _ in range(r))
            c=tuple(make_vector(rng,b,m,3) for _ in range(q))
            d=tuple(make_vector(rng,b,m,3) for _ in range(p))
            e=matrix([[rng.getrandbits(1<<b) for _ in range(q)] for _ in range(p)])
            def cols(vs):return matrix(zip(*(z.expand() for z in vs)))
            U,V,C,D=cols(u),matrix(z.expand() for z in v),cols(c),matrix(z.expand() for z in d)
            expected=schur(add(identity(n),mul(U,V,b)),C,D,e,b)
            self.assertEqual(tensor_interface(u,v,c,d,e).evaluate(b),expected)

    def test_billion_coordinate_nonzero_example(self):
        # delta_0 in 2^30 dimensions: coordinate 0 is the only support.
        m=30;b=2
        delta=lambda weight: TensorVector(b,m,(TensorTerm(weight,((1,0),)*m),))
        x=1<<1;y=1<<2
        data=tensor_interface((delta(x),),(delta(1),),(delta(y),),(delta(1),),((0,),))
        self.assertEqual(data.core,((x,),))
        self.assertEqual(data.evaluate(b),((y^(1<<3),),))
        with self.assertRaises(MemoryError): delta(1).expand()

    def test_dense_support_without_enumeration(self):
        # v_i = product (1 + x*bit_j). Every coordinate is a unit.
        # Pair with delta_0 to extract a nonzero exact core at 2^40 indices.
        b=2;m=40;x=1<<1;y=1<<2
        dense=TensorVector(b,m,(TensorTerm(1,((1,1^x),)*m),))
        delta=lambda w: TensorVector(b,m,(TensorTerm(w,((1,0),)*m),))
        data=tensor_interface((delta(x),),(dense,),(delta(y),),(dense,),((0,),))
        self.assertEqual(data.evaluate(b),((y^(1<<3),),))

    def test_validation(self):
        with self.assertRaises(ValueError): TensorVector(1,2,(TensorTerm(1,((0,1),)),))
        v=TensorVector(1,2,(TensorTerm(1,((0,1),(1,0))),))
        with self.assertRaises(ValueError): tensor_interface((v,),(v,),(v,),(v,),((0,),))
        with self.assertRaises(ValueError): v.coordinate(4)

class SeparableAndCertificateTests(unittest.TestCase):
    def test_separable_background(self):
        rng=random.Random(5481);b=2;m=3;n=1<<m
        factors=tuple(matrix([[1,rng.getrandbits(1<<b)],[0,1]]) for _ in range(m))
        u=tuple(make_vector(rng,b,m,2,True) for _ in range(2))
        v=tuple(make_vector(rng,b,m,2) for _ in range(2))
        c=tuple(make_vector(rng,b,m,2) for _ in range(2))
        d=tuple(make_vector(rng,b,m,2) for _ in range(2));e=zero(2,2)
        a0=[]
        for i in range(n):
            row=[]
            for j in range(n):
                x=1
                for k,t in enumerate(factors): x=subset_product(x,t[(i>>k)&1][(j>>k)&1],b)
                row.append(x)
            a0.append(row)
        U=matrix(zip(*(z.expand() for z in u)));V=matrix(z.expand() for z in v)
        C=matrix(zip(*(z.expand() for z in c)));D=matrix(z.expand() for z in d)
        answer=schur(add(matrix(a0),mul(U,V,b)),C,D,e,b)
        self.assertEqual(separable_background_interface(factors,u,v,c,d,e).evaluate(b),answer)

    def test_succinct_certificate_and_tampering(self):
        from benchmarks.succinct_example import specification
        from unknot_frobenius.verify import verify_spec
        s=specification(40)
        self.assertEqual(verify_spec(s)['schur'],((8,),))
        s['expected_schur']=[[0]]
        with self.assertRaises(ValueError): verify_spec(s)

    def test_flattening_obstruction(self):
        # Equality tensor's flattening is I_(2^k), hence tensor rank >=2^k.
        for k in range(1,7):
            rows=[1<<i for i in range(1<<k)]
            self.assertEqual(len({r.bit_length()-1 for r in rows}),1<<k)
