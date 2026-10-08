import copy
import random
import unittest
from terminal_updates.linear import *
from terminal_updates.terminal import *

def partitions(n):
    if n == 0:
        yield ()
        return
    def rec(out):
        if len(out) == n:
            yield tuple(out); return
        for k in range(max(out,default=-1)+2):
            yield from rec(out+[k])
    yield from rec([0])

class TerminalTests(unittest.TestCase):
    def test_single_vertex_empty_cofactor(self):
        g=SignedGraph(1,())
        o=ExactObserver(g,(0,))
        self.assertEqual(o.cursor().value,1)
        self.assertTrue(verify_exact_certificate(o.cursor().certificate()))

    def test_laplacian_round_trip(self):
        g=SignedGraph(4,((0,1,2),(0,1,-1),(1,2,-3),(3,3,9)))
        h=SignedGraph.from_laplacian(g.laplacian())
        self.assertEqual(g.laplacian(),h.laplacian())

    def test_signed_singular_interior(self):
        g=SignedGraph(3,((0,1,1),(1,2,-1)))
        for p in (2,3,5,101):
            k=TerminalKernel(g,(0,2),p)
            self.assertEqual(k.nullity,1)
            c=k.cursor()
            self.assertEqual(c.residue,(-1)%p)
            self.assertEqual(c.merged(0,1).residue,0)
            self.assertEqual(c.residue,(-1)%p)

    def test_bad_prime_is_not_discarded(self):
        g=SignedGraph(3,((0,1,1),(1,2,1)))
        k2=TerminalKernel(g,(0,2),2)
        k3=TerminalKernel(g,(0,2),3)
        self.assertEqual((k2.nullity,k3.nullity),(1,0))
        self.assertEqual(k2.cursor().residue,1)
        o=ExactObserver(g,(0,2))
        self.assertEqual(o.cursor().merged(0,1).value,2)

    def test_prime_specific_all_zero(self):
        g=SignedGraph(3,((0,1,1),(1,2,1),(2,0,1)))
        self.assertTrue(TerminalKernel(g,(0,),3).all_zero)
        self.assertFalse(TerminalKernel(g,(0,),5).all_zero)
        self.assertEqual(ExactObserver(g,(0,)).cursor().value,3)

    def test_random_all_partitions(self):
        rng=random.Random(981)
        for n in range(2,8):
            for trial in range(4):
                g=SignedGraph(n,tuple((i,j,rng.choice((-2,-1,1,2)))
                    for i in range(n) for j in range(i+1,n) if rng.random()<.5))
                terms=tuple(rng.sample(range(n), min(n,4)))
                kernels=[TerminalKernel(g,terms,p) for p in (2,3,5,101)]
                for labels in partitions(len(terms)):
                    value=bareiss(quotient_cofactor(g,terms,labels))
                    self.assertLessEqual(abs(value),g.uniform_bound)
                    for k in kernels:
                        self.assertEqual(k.query(labels),value%k.p)

    def test_dynamic_random_merges(self):
        rng=random.Random(992)
        for n in range(2,9):
            g=SignedGraph(n,tuple((i,j,rng.choice((-1,1)))
                for i in range(n) for j in range(i+1,n) if rng.random()<.6))
            terms=tuple(range(n))
            for p in (2,3,5,101):
                c=TerminalKernel(g,terms,p).cursor()
                while len(c.blocks)>1:
                    b=rng.choice([x for x in c.blocks if x])
                    a=rng.choice([x for x in c.blocks if x!=b])
                    old=c
                    c=c.merged(a,b)
                    expected=bareiss(quotient_cofactor(g,terms,c.labels))%p
                    self.assertEqual(c.residue,expected)
                    self.assertEqual(old.residue,old.kernel.query(old.labels))
                    if c.normal: self.assertTrue(verify_normal_form(c.kernel.matrix_for(c.blocks),c.normal.certificate()))

    def test_rank_two_update_identity(self):
        rng=random.Random(81)
        g=SignedGraph(9,tuple((i,j,rng.choice((-1,1))) for i in range(9) for j in range(i+1,9)))
        c=TerminalKernel(g,tuple(range(7)),101).cursor()
        for a,b in [(3,2),(3,5),(0,3),(4,1)]:
            k=c.kernel;r=k.nullity;n=k.dimension;p=k.p
            old=k.matrix_for(c.blocks)
            group=c.blocks[b]
            e=[0]*n;e[r+b-1]=1
            if a:e[r+a-1]=-1
            w=[sum(k.base[r+i-1][j] for i in group)%p for j in range(n)]
            chi=[0]*n
            for i in group:chi[r+i-1]=1
            nxt=c.merged(a,b);new=k.matrix_for(nxt.blocks)
            expected=[[(old[i][j]-e[i]*w[j]+chi[i]*e[j])%p for j in range(n)] for i in range(n)]
            self.assertEqual(new,expected)
            c=nxt

    def test_nonminimum_anchor_certificate(self):
        g=SignedGraph(4,((0,1,1),(1,2,-1),(2,3,1),(3,0,1),(1,3,2)))
        c=ExactObserver(g,(0,1,2,3)).cursor().merged(3,1).merged(3,2)
        self.assertEqual(c.labels,(0,3,3,3))
        self.assertTrue(verify_exact_certificate(c.certificate()))

    def test_exact_reconstruction(self):
        for bound in (1,4,41,1000):
            pp=enough_primes(bound)
            for z in (-bound,-1,0,1,bound):
                self.assertEqual(reconstruct([z%p for p in pp],pp,bound),z)

    def test_mixed_sign_trap(self):
        self.assertEqual((4%3,4%5),(1,4))
        self.assertTrue(all(4%p in (1,p-1) for p in (3,5)))
        self.assertGreater(3*5,2*4)
        self.assertEqual(reconstruct((1,4),(3,5),4),4)

    def test_insufficient_crt(self):
        with self.assertRaises(ValueError):reconstruct((1,),(3,),4)
        with self.assertRaises(ValueError):reconstruct((1,1),(3,3),1)
        with self.assertRaises(ArithmeticError):reconstruct((2,),(7,),1)

    def test_certificate_tampering(self):
        g=SignedGraph(4,((0,1,1),(1,2,-1),(2,3,1),(3,0,1),(1,3,2)))
        cert=ExactObserver(g,(0,1,2)).cursor().merged(1,2).certificate()
        self.assertTrue(verify_exact_certificate(cert))
        bad=copy.deepcopy(cert);bad['value']+=1
        self.assertFalse(verify_exact_certificate(bad))
        bad=copy.deepcopy(cert);bad['graph']['edges'][0][2]+=1
        self.assertFalse(verify_exact_certificate(bad))
        bad=copy.deepcopy(cert);bad['bound']+=1
        self.assertFalse(verify_exact_certificate(bad))
        bad=copy.deepcopy(cert);bad['fields']=bad['fields'][:1]
        self.assertFalse(verify_exact_certificate(bad))
        bad=copy.deepcopy(cert);bad['fields'][0]['endpoint']['normal']['scale']+=1
        self.assertFalse(verify_exact_certificate(bad))

    def test_transactional_budget_failures(self):
        g=SignedGraph(5,tuple((i,j,1) for i in range(5) for j in range(i+1,5)))
        parent=TerminalKernel(g,tuple(range(5)),101).cursor()
        saved=parent.certificate()
        success=parent.merged(1,2,Budget(units_left=100000))
        self.assertNotEqual(success.labels,parent.labels)
        for cap in range(0,250,7):
            try: parent.merged(1,2,Budget(units_left=cap))
            except BudgetExceeded: pass
            self.assertEqual(parent.certificate(),saved)
        with self.assertRaises(BudgetExceeded):parent.merged(1,2,Budget(deadline=0))
        self.assertEqual(parent.certificate(),saved)

    def test_validation(self):
        edges=[[0,1,1]]
        frozen=SignedGraph(2,edges)
        edges[0][2]=9
        self.assertEqual(frozen.edges,((0,1,1),))
        one=ExactObserver(frozen,(0,1)).cursor().certificate()
        one['value']=True
        self.assertFalse(verify_exact_certificate(one))
        with self.assertRaises(ValueError):SignedGraph(0,())
        with self.assertRaises(ValueError):SignedGraph(2,((0,2,1),))
        with self.assertRaises(ValueError):SignedGraph.from_laplacian([[1,0],[0,1]])
        g=SignedGraph(2,((0,1,1),))
        with self.assertRaises(ValueError):TerminalKernel(g,(0,0),3)
        with self.assertRaises(ValueError):TerminalKernel(g,(0,),9)
        c=TerminalKernel(g,(0,1),3).cursor()
        for a,b in ((0,0),(1,0),(0,2)):
            with self.assertRaises(ValueError):c.merged(a,b)
        with self.assertRaises(ValueError):c.kernel.query((0,))

    def test_weighted_parallel_loops(self):
        g=SignedGraph(3,((0,1,4),(0,1,-3),(1,2,2),(2,0,-1),(0,0,99)))
        o=ExactObserver(g,(0,1,2))
        for labels in partitions(3):
            self.assertEqual(o.query(labels),bareiss(quotient_cofactor(g,(0,1,2),labels)))
