import copy, json, random, unittest
from types import SimpleNamespace
from closure_reset.binary import rank, apply, compose, add, identity
from closure_reset.dots import parity, derivative, multiply, quotient
from closure_reset.diagram import braid_pd, validate, component_count, splice
from closure_reset.cube import Cube, interval_rank, quiver_rank
from closure_reset.pure import certify, inspect
from closure_reset.driver import recognize_pd, replay


def fixture(theta, dims, arrows, p=3):
    offsets=[]; total=0
    for n in dims: offsets.append(total); total+=n
    deg=[]; out=[{} for _ in range(total)]; inc=[set() for _ in range(total)]
    for h,n in enumerate(dims):
        deg += [h]*n
        if h==len(dims)-1: continue
        for j,vec in enumerate(arrows[h]):
            while vec:
                bit=vec & -vec; vec ^= bit
                u=offsets[h]+j; v=offsets[h+1]+bit.bit_length()-1
                out[u][v]=theta; inc[v].add(u)
    return SimpleNamespace(mid=[0]*total, deg=deg, out=out, inc=inc,
                           algebra=SimpleNamespace(pairs=[tuple((2*i,2*i+1) for i in range(p))]))

class AlgebraTests(unittest.TestCase):
    def test_all_three_variable_polynomials(self):
        for f in range(0,256,2):
            self.assertEqual(multiply(f,f),0)
            self.assertEqual(derivative(derivative(f)),0)
            self.assertEqual(derivative(f)&1,parity(f))
            if parity(f): self.assertEqual(multiply(derivative(f),derivative(f)),1)
            self.assertEqual(quotient(f,[0,0,0]),2*parity(f))
    def test_random_leibniz(self):
        rng=random.Random(817)
        for _ in range(600):
            f,g=rng.randrange(1<<16),rng.randrange(1<<16)
            self.assertEqual(derivative(multiply(f,g)),multiply(derivative(f),g)^multiply(f,derivative(g)))
    def test_parity_not_support_parity(self):
        self.assertEqual(parity((1<<1)|(1<<3)),1)
        self.assertEqual(parity(1<<3),0)
        self.assertEqual(parity((1<<1)|(1<<2)),0)
    def test_binary_rank(self):
        self.assertEqual(rank([3,5,6]),2)
        self.assertEqual(rank([]),0)
        with self.assertRaises(ValueError): rank([-1])
    def test_beta_noncomplex(self):
        s=fixture(2,[1,1,1],[(1,),(1,)])
        d=certify(s,(0,1,2))
        self.assertEqual(d.beta,1); self.assertEqual(d.lower_bound,2)
    def test_even_obstruction(self):
        s=fixture(6,[1,1,1],[(1,),(1,)])
        d=certify(s,(0,1,2)); self.assertEqual(d.lower_bound,4)
    def test_odd_multiple_intervals(self):
        s=fixture(2,[1,2],[(3,)])
        d=certify(s,(0,1,2)); self.assertEqual(d.beta,2); self.assertEqual(d.lower_bound,4)
    def test_attachments_rejected(self):
        s=fixture(2,[1,1,1],[(1,),(1,)])
        with self.assertRaises(ValueError): certify(s,(0,1))
    def test_mixed_coefficient_ineligible(self):
        s=fixture(2,[1,1,1],[(1,),(1,)]); s.out[1][2]=6
        self.assertIsNone(certify(s,(0,1,2)))
    def test_empty_matching_ineligible(self):
        s=fixture(0,[1],[],p=0); self.assertIsNone(certify(s,(0,)))
    def test_singleton_sum(self):
        s=fixture(0,[2],[]); self.assertEqual(inspect(s)[2],4)

class CubeTests(unittest.TestCase):
    cases=[(2,[1]),(2,[1,1]),(2,[1,1,1]),(3,[1,-2,1,-2]),(3,[1,2])]
    def test_reference_ranks(self):
        for (s,w),r in zip(self.cases,[2,4,6,10,2]):
            c=Cube(braid_pd(s,w)); self.assertTrue(c.check()); self.assertEqual(c.homology_rank(),r)
    def test_derivation_and_local_reverse_saddles(self):
        for s,w in self.cases:
            c=Cube(braid_pd(s,w)); z=(0,)*c.dimension
            self.assertEqual(compose(c.nu,c.nu),z)
            self.assertEqual(add(compose(c.d,c.nu),compose(c.nu,c.d)),z)
            dots={a:c.polynomial(2,[a]) for a in c.labels}
            for x in dots.values():
                self.assertEqual(add(compose(c.nu,x),compose(x,c.nu)),identity(c.dimension))
            for j,crossing in enumerate(c.pd):
                h=c.reverse(j); delta=add(dots[crossing[0]],dots[crossing[2]])
                self.assertEqual(add(compose(c.d,h),compose(h,c.d)),delta)
                self.assertEqual(compose(h,h),z); self.assertEqual(compose(h,delta),z)
                self.assertEqual(compose(delta,h),z)
                for x in dots.values(): self.assertEqual(compose(h,x),compose(x,h))
    def test_exact_parity_interval_formula(self):
        for s,w in [(2,[1]),(2,[1,1,1]),(3,[1,-2,1,-2])]:
            c=Cube(braid_pd(s,w)); marks=(c.labels*3)[:3]; r=c.homology_rank()
            for f in range(0,256,2):
                x=c.polynomial(f,marks)
                for l in (1,2,3,4):
                    self.assertEqual(interval_rank(c,x,l),r if parity(f) else l*r,(w,f,l))
    def test_random_quivers(self):
        rng=random.Random(418)
        for _ in range(90):
            s,w=rng.choice([(2,[1]),(2,[1,1,1]),(3,[1,-2,1,-2])])
            c=Cube(braid_pd(s,w)); marks=(c.labels*3)[:3]
            dims=[rng.randrange(1,4) for _ in range(rng.randrange(1,5))]
            arrows=[tuple(rng.randrange(1<<b) for _ in range(a)) for a,b in zip(dims,dims[1:])]
            f=rng.randrange(128)*2; beta=sum(dims)-sum(rank(a) for a in arrows)
            got=quiver_rank(c,c.polynomial(f,marks),dims,arrows,check=True)
            self.assertEqual(got,(beta if parity(f) else sum(dims))*c.homology_rank())
    def test_links_and_monotonicity(self):
        c=Cube(braid_pd(2,[1,1])); marks=(c.labels*3)[:3]; r=c.homology_rank()
        for f in range(0,256,2):
            vals=[interval_rank(c,c.polynomial(f,marks),l) for l in range(1,6)]
            self.assertEqual(vals[0],r)
            self.assertTrue(all(b>=a for a,b in zip(vals,vals[1:])))
            diffs=[b-a for a,b in zip(vals,vals[1:])]
            self.assertTrue(all(a>=b for a,b in zip(diffs,diffs[1:])))
            if parity(f): self.assertEqual(vals,[r]*5)
            else: self.assertTrue(all(x>=4 for x in vals))
    def test_gauge_with_nonsquarezero_quiver_arrow(self):
        c=Cube(braid_pd(3,[1,-2,1,-2])); H=c.reverse(0)
        # K=H X_a, and a three-vertex interval B with B^2 != 0.
        a,b=c.pd[0][0],c.pd[0][2]
        xa=c.polynomial(2,[a]); xb=c.polynomial(2,[b]); P=xa
        K=compose(H,P); deltaP=compose(add(xa,xb),P)
        D=c.dimension; n=3*D
        G=tuple((1<<j) ^ ((K[j%D] << (D*(j//D+1))) if j//D<2 else 0) for j in range(n))
        from closure_reset.cube import quiver_columns
        before=quiver_columns(c.d,xa,[1,1,1],[(1,),(1,)])
        after=quiver_columns(c.d,add(xa,deltaP),[1,1,1],[(1,),(1,)])
        self.assertEqual(compose(G,G),identity(n))
        self.assertEqual(compose(G,compose(before,G)),after)

class DriverTests(unittest.TestCase):
    def test_basic_and_replay(self):
        for s,w in [(2,[1]),(2,[1,1,1]),(3,[1,-2,1,-2]),(3,[1,2])]:
            pd=braid_pd(s,w); result=recognize_pd(pd,check_d_squared=True)
            self.assertTrue(replay(pd,json.loads(json.dumps(result))))
    def test_corrupt_certificate(self):
        pd=braid_pd(3,[1,2]); r=recognize_pd(pd)
        r['events'][0]['stage']+=1
        with self.assertRaises(ValueError): replay(pd,r)
    def test_unknown_is_not_verdict(self):
        pd=braid_pd(2,[1,1,1])
        self.assertEqual(recognize_pd(pd,max_objects=0)['status'],'UNKNOWN')
        self.assertEqual(recognize_pd(pd,seconds=0)['status'],'UNKNOWN')
        with self.assertRaises(ValueError): replay(pd,{'status':'UNKNOWN'})
    def test_invalid_inputs(self):
        for pd in [[(0,1,2,3)],[(0,1,0,1)],[(0,0,1,1),(2,2,3,3)]]:
            with self.assertRaises(ValueError): recognize_pd(pd)
        for limit in [-1,True,1.3]:
            with self.assertRaises(ValueError): recognize_pd([],max_objects=limit)
    def test_unknot_reset(self):
        r=recognize_pd(braid_pd(8,list(range(1,8))),check_d_squared=True)
        self.assertEqual(r['status'],'UNKNOT'); self.assertEqual(r['stats']['max_gap'],1)
        self.assertEqual(r['stats']['resets'],6)
    def test_seeded_braids(self):
        rng=random.Random(731024); cases=0
        while cases<100:
            s=rng.choice([2,3,4]); n=rng.randrange(1,8)
            w=[rng.choice([-1,1])*rng.randrange(1,s) for _ in range(n)]
            try: pd=braid_pd(s,w)
            except ValueError: continue
            if component_count(pd)!=1: continue
            rng.shuffle(pd); expected='UNKNOT' if Cube(pd).homology_rank()==2 else 'NONTRIVIAL'
            for reset in (False,True):
                r=recognize_pd(pd,reset=reset,check_d_squared=True)
                self.assertEqual(r['status'],expected,(s,w,reset))
            cases+=1


class FirstJetTests(unittest.TestCase):
    def test_mixed_coefficients_generalize_purity(self):
        from closure_reset.jet import certify_jet
        s=fixture(2,[1,1,1],[(1,),(1,)])
        s.out[1][2]=(1<<1)|(1<<3)  # x1 + x1*x2
        self.assertIsNone(certify(s,(0,1,2)))
        self.assertEqual(certify_jet(s,(0,1,2)).kappa,1)
    def test_multi_component_counterexample_to_knot_formula(self):
        a=braid_pd(2,[1]); b=[tuple(x+2 for x in c) for c in a]; c=Cube(a+b)
        theta=c.polynomial(6,[0,2])  # x+y, even parity, two different link components
        self.assertEqual(c.homology_rank(),4)
        self.assertEqual(interval_rank(c,theta,3),4)
        self.assertNotEqual(interval_rank(c,theta,3),3*c.homology_rank())
    def test_random_mixed_radical_blocks(self):
        from closure_reset.jet import certify_jet
        from closure_reset.dots import multiply
        rng=random.Random(4311)
        for _ in range(150):
            c=Cube(braid_pd(2,[1,1,1])); marks=c.labels[:3]
            dims=[2,2,2]; s=fixture(2,dims,[(3,3),(3,3)])
            # Every entry is a multiple of x1: all matrix products vanish.
            for row in s.out:
                for v in row: row[v]=rng.choice([2,8,32,128,10,34,130,42,170])
            j=certify_jet(s,tuple(range(6))); D=c.dimension; cols=[]
            maps={f:c.polynomial(f,marks) for row in s.out for f in row.values()}
            for v,row in enumerate(s.out):
                for x in range(D):
                    col=c.d[x]<<(D*v)
                    for w,f in row.items(): col^=maps[f][x]<<(D*w)
                    cols.append(col)
            self.assertFalse(any(apply(cols,col) for col in cols))
            self.assertEqual(len(cols)-2*rank(cols),j.kappa*c.homology_rank())
    def test_nonpure_gauge_identity(self):
        # Matrix derivative rather than a single common scalar coefficient.
        from closure_reset.dots import monomials
        c=Cube(braid_pd(3,[1,-2,1,-2])); a,b=c.pd[0][0],c.pd[0][2]
        marks=[a,c.labels[-1]]; shifted=[b,c.labels[-1]]
        entries={(0,1):2,(0,2):8,(1,3):8,(2,3):2} # products cancel, and are zero here
        D=c.dimension; n=4*D; H=c.reverse(0)
        def matrix(which):
            maps={f:c.polynomial(f,which) for f in entries.values()}; cols=[]
            for v in range(4):
                for x in range(D):
                    col=c.d[x]<<(D*v)
                    for (u,w),f in entries.items():
                        if u==v: col^=maps[f][x]<<(D*w)
                    cols.append(col)
            return tuple(cols)
        G=list(identity(n))
        for (v,w),f in entries.items():
            partial=0
            for mon in monomials(f):
                if mon&1: partial^=1<<(mon^1)
            hp=compose(H,c.polynomial(partial,marks))
            for x in range(D): G[D*v+x]^=hp[x]<<(D*w)
        self.assertEqual(compose(G,G),identity(n))
        self.assertEqual(compose(G,compose(matrix(marks),G)),matrix(shifted))

class ScalarJetTests(unittest.TestCase):
    def test_scalar_homology_and_induced_map(self):
        from closure_reset.jet import first_jet_survivors
        self.assertEqual(first_jet_survivors([2,0,0],[0,0,0]),dict(scalar_homology=1,induced_linear_rank=0,kappa=1))
        self.assertEqual(first_jet_survivors([0,0,0],[2,4,0])['kappa'],1)
        self.assertEqual(first_jet_survivors([2,0],[0,0])['kappa'],0)
        with self.assertRaises(ValueError): first_jet_survivors([2,1],[0,0])
    def test_random_scalar_unit_plus_radical_blocks(self):
        from closure_reset.jet import first_jet_survivors
        rng=random.Random(338)
        c=Cube(braid_pd(2,[1,1,1])); D=c.dimension; marks=c.labels[:3]
        # Contractible unit pair, two isolated scalar homology generators, and
        # an arbitrary radical arrow between those generators.
        for _ in range(90):
            unit=1+2*rng.randrange(128); radical=2*rng.randrange(128)
            entries={(0,1):unit,(2,3):radical}; n=4
            A=[0]*n; B=[0]*n
            for (v,w),f in entries.items():
                if f&1: A[v]^=1<<w
                if parity(f): B[v]^=1<<w
            expected=first_jet_survivors(A,B)['kappa']*c.homology_rank()
            maps={f:c.polynomial(f,marks) for f in entries.values()}; cols=[]
            for v in range(n):
                for x in range(D):
                    col=c.d[x]<<(v*D)
                    for (u,w),f in entries.items():
                        if u==v: col^=maps[f][x]<<(w*D)
                    cols.append(col)
            self.assertFalse(any(apply(cols,col) for col in cols))
            self.assertEqual(len(cols)-2*rank(cols),expected)

if __name__=='__main__': unittest.main()
