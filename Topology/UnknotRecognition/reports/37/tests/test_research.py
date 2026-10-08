import copy, itertools, random, unittest
from separator_transfer.core import *
from separator_transfer.cube import *
from separator_transfer.closure import *
from separator_transfer.budgets import sharp_rank_budget
from separator_transfer.certificates import *


def flatten_rank(rows, sources, targets, dims):
    a = sum(dims[v] for v in sources); cols = [0]*a; ro = 0
    for ti,t in enumerate(targets):
        co = 0
        for si,s in enumerate(sources):
            value = rows[ti][si]
            for r in range(dims[t]):
                for c in range(dims[s]):
                    if (value >> (r*dims[s]+c))&1: cols[co+c] |= 1 << (ro+r)
            co += dims[s]
        ro += dims[t]
    return len(binary_basis(cols))


def random_graph(rng, n, adapter='f2'):
    dims = [rng.randrange(1,4) for _ in range(n)]
    ops = F2() if adapter == 'f2' else DotAlgebra(3) if adapter == 'dot' else MatrixCategory(dims)
    edges = []
    for u in range(n-2):
        for v in range(max(u+1,2),n):
            if rng.random() < .35:
                bound = 2 if adapter == 'f2' else 256 if adapter == 'dot' else 1 << (dims[u]*dims[v])
                edges.append((u,v,rng.randrange(1,bound)))
    return DAG(n,tuple(edges),(0,1),(n-2,n-1)),ops,dims

class FactorTests(unittest.TestCase):
    def test_first_hit_non_antichain(self):
        g = DAG(4,((0,1,1),(1,2,1),(2,3,1)),(0,),(3,))
        f = factor_at_cut(g,(1,2),F2())
        self.assertEqual(f.A,[[1],[0]]); self.assertEqual(f.expand(F2()),[[1]])
        # Unrestricted prefix times unrestricted suffix would count this path twice.
        self.assertEqual((1&1) ^ (1&1),0)
    def test_noncommutative_order(self):
        ops = MatrixCategory([2,2,2]); a,b = 2,4
        g = DAG(3,((0,1,a),(1,2,b)),(0,),(2,))
        f = factor_at_cut(g,(1,),ops)
        self.assertEqual(f.expand(ops),[[ops.mul(0,1,2,b,a)]])
        self.assertNotEqual(ops.mul(0,1,2,b,a),ops.mul(0,1,2,a,b))
    def test_dot_square_zero(self):
        ops = DotAlgebra(2)
        g = DAG(3,((0,1,2),(1,2,2)),(0,),(2,))
        self.assertEqual(factor_at_cut(g,(1,),ops).expand(ops),[[0]])
    def test_all_small_cuts_three_categories(self):
        rng = random.Random(7441)
        for mode in ('f2','dot','matrix'):
            for _ in range(25):
                g,ops,dims = random_graph(rng,6,mode)
                reference,_ = dense_transfer(g,ops); reverse,_ = dense_transfer(g,ops,True)
                self.assertEqual(reference,reverse)
                for bits in range(1 << g.n):
                    cut = tuple(v for v in range(g.n) if bits >> v & 1)
                    if not g.separates(cut): continue
                    f = factor_at_cut(g,cut,ops)
                    self.assertEqual(f.expand(ops),reference)
                    if mode == 'matrix': self.assertEqual(f.binary_rank(dims),flatten_rank(reference,g.sources,g.targets,dims))
                    elif mode == 'f2': self.assertEqual(f.binary_rank(),flatten_rank(reference,g.sources,g.targets,[1]*g.n))
    def test_empty_cut_disconnected(self):
        g = DAG(2,(),(0,),(1,))
        f = factor_at_cut(g,(),F2())
        self.assertEqual(f.expand(F2()),[[0]]); self.assertEqual(f.binary_rank(),0)
    def test_invalid_cut(self):
        g = DAG(2,((0,1,1),),(0,),(1,))
        with self.assertRaises(ValueError): factor_at_cut(g,(),F2())
    def test_cycle_rejected(self):
        with self.assertRaises(ValueError): DAG(2,((0,1,1),(1,0,1)),(),())
    def test_terminals_can_be_cut(self):
        g = DAG(4,((0,2,1),(0,3,1),(1,2,1)),(0,1),(2,3))
        for cut in (g.sources,g.targets):
            self.assertEqual(factor_at_cut(g,cut,F2()).expand(F2()),dense_transfer(g,F2())[0])
    def test_capacity_not_cardinality(self):
        dims = [3]*3; ops = MatrixCategory(dims); identity = ops.one(0)
        g = DAG(3,((0,1,identity),(1,2,identity)),(0,),(2,))
        self.assertEqual(factor_at_cut(g,(1,),ops).binary_rank(dims),3)
        self.assertEqual(minimum_vertex_cut(g,dims).capacity,3)

class CutTests(unittest.TestCase):
    def test_weighted_cuts_exhaustively(self):
        rng = random.Random(777)
        for _ in range(100):
            g,_,_ = random_graph(rng,6)
            caps = [rng.randrange(0,7) for _ in range(g.n)]
            cert = minimum_vertex_cut(g,caps)
            truth = min(sum(caps[v] for v in range(g.n) if bits >> v & 1)
                        for bits in range(1 << g.n)
                        if g.separates(tuple(v for v in range(g.n) if bits >> v & 1)))
            self.assertEqual(cert.capacity,truth)
            self.assertTrue(verify_cut_certificate(g,caps,cert))
    def test_huge_binary_capacities(self):
        g = DAG(3,((0,1,1),(1,2,1)),(0,),(2,)); caps = [1 << 1000,3,1 << 1000]
        c = minimum_vertex_cut(g,caps)
        self.assertEqual(c.cut,(1,)); self.assertEqual(c.capacity,3)
    def test_bad_flow_rejected(self):
        g = DAG(3,((0,1,1),(1,2,1)),(0,),(2,)); c = minimum_vertex_cut(g)
        flows = list(c.flows); flows[0] += 1
        self.assertFalse(verify_cut_certificate(g,[1]*3,CutCertificate(c.cut,c.capacity,tuple(flows))))
    def test_bad_capacity_rejected(self):
        g = DAG(2,((0,1,1),),(0,),(1,)); c = minimum_vertex_cut(g)
        self.assertFalse(verify_cut_certificate(g,[1,1],CutCertificate(c.cut,2,c.flows)))

class BudgetTests(unittest.TestCase):
    def test_sharp_path_budget_exhaustive_oracle(self):
        rng = random.Random(190)
        for _ in range(500):
            length = rng.randrange(2,7); dims = [rng.randrange(0,5) for _ in range(length)]
            caps = [rng.randrange(0,4) for _ in range(length-1)]
            expected = max(sum(r) for r in itertools.product(*(range(k+1) for k in caps))
                           if all((r[h-1] if h else 0)+(r[h] if h < length-1 else 0) <= dims[h]
                                  for h in range(length)))
            got = sharp_rank_budget({(i,0):d for i,d in enumerate(dims)},
                                    {(i,0):k for i,k in enumerate(caps)})
            self.assertEqual(got['maximum_rank_sum'],expected)
    def test_strict_budget_improvement(self):
        dims={(0,0):2,(1,0):1,(2,0):2}; caps={(0,0):1,(1,0):1}
        self.assertEqual(sharp_rank_budget(dims,caps)['homology_lower'],3)
    def test_large_degree_gaps(self):
        dims={(0,0):3,(10**100,0):5}; caps={}
        self.assertEqual(sharp_rank_budget(dims,caps)['homology_lower'],8)

class ClosureTests(unittest.TestCase):
    def test_binomial_dimensions(self):
        a=(1,0,3,2,5,4)
        self.assertEqual(closure_circles(a,a),3)
        self.assertEqual(reduced_closure_dimension(a,a),4)
        self.assertEqual([reduced_closure_dimension(a,a,quantum=j) for j in (-2,0,2)],[1,2,1])
    def test_overlay(self):
        self.assertEqual(closure_circles((1,0,3,2),(3,2,1,0)),1)
    def test_crossed_pairing_rejected(self):
        with self.assertRaises(ValueError): validate_matching((2,3,0,1))

class KnotTests(unittest.TestCase):
    def test_known_small_knots(self):
        cases=[(1,[],1),(2,[1],1),(2,[-1],1),(2,[1]*3,3),(3,[1,-2]*2,5),(2,[1]*5,5)]
        for s,w,rank in cases:
            c=reduced_cube(s,w); self.assertTrue(c.validate())
            self.assertEqual(sum(c.homology().values()),rank)
            for limit in (0,5,None):
                result=analyze_complex(c,acyclic_matching(c,limit))
                self.assertEqual(result['homology'],c.homology())
                self.assertLessEqual(result['sharp_lower'],rank)
    def test_reidemeister_two(self):
        for word in ([1]*3,[1,-2,1,-2],[1,2]):
            s=max(map(abs,word))+1
            self.assertEqual(reduced_cube(s,word).homology(),reduced_cube(s,[1,-1]+list(word)).homology())
    def test_braid_relation(self):
        for sign in (1,-1):
            a=[sign*x for x in [1,2,1,2]]; b=[sign*x for x in [2,1,2,2]]
            self.assertEqual(reduced_cube(3,a).homology(),reduced_cube(3,b).homology())
    def test_stabilization(self):
        for word in ([1],[1]*3,[-1]*3):
            for sign in (1,-1):
                self.assertEqual(reduced_cube(2,word).homology(),reduced_cube(3,list(word)+[2*sign]).homology())
    def test_mirror(self):
        word=[1,-2,1,2,1,2]
        a=reduced_cube(3,word).homology(); b=reduced_cube(3,[-x for x in word]).homology()
        self.assertEqual({(-h,-j):v for (h,j),v in a.items()},b)
    def test_random_knots_partial_morse(self):
        rng=random.Random(414)
        checked=0
        while checked<40:
            s=rng.randrange(2,5); w=[rng.choice((-1,1))*rng.randrange(1,s) for _ in range(rng.randrange(1,8))]
            if closure_components(s,w)!=1: continue
            c=reduced_cube(s,w); result=analyze_complex(c,acyclic_matching(c,20))
            self.assertEqual(c.homology(),result['homology']); checked+=1
    def test_matching_tamper(self):
        c=reduced_cube(2,[1]*3); pairs=acyclic_matching(c)
        self.assertFalse(verify_matching(c,pairs+pairs[:1]))
    def test_reference_resource_cap(self):
        with self.assertRaises(ValueError): reduced_cube(2,[1]*12)

class CertificateTests(unittest.TestCase):
    def test_accept_and_reject(self):
        for s,w in ((2,[1]),(3,[1,-2]*2)):
            cert=make_braid_certificate(s,w,5)
            self.assertTrue(verify_braid_certificate(cert))
    def test_tampered_rank(self):
        cert=make_braid_certificate(2,[1]*3,3); cert['reduced_rank']=1
        self.assertFalse(verify_braid_certificate(cert))
    def test_tampered_input(self):
        cert=make_braid_certificate(2,[1]*3,3); cert['word']=[-1]*3
        self.assertFalse(verify_braid_certificate(cert))
    def test_tampered_cut(self):
        cert=make_braid_certificate(3,[1,-2]*2,0)
        self.assertTrue(cert['maps']); cert['maps'][0]['cut']['capacity']+=1
        self.assertFalse(verify_braid_certificate(cert))
    def test_links_not_knots(self):
        with self.assertRaises(ValueError): make_braid_certificate(2,[1]*2)

class MinimumCutFirstHitTests(unittest.TestCase):
    def test_nonantichain_unique_minimum_cut(self):
        g=DAG(4,((0,1,1),(1,2,1),(2,3,1),(0,2,1),(1,3,1)),(0,),(3,))
        cert=minimum_vertex_cut(g,(3,1,1,3))
        self.assertEqual(cert.cut,(1,2))
        self.assertEqual(cert.capacity,2)
        self.assertEqual(factor_at_cut(g,cert.cut,F2()).expand(F2()),[[1]])
        self.assertEqual(dense_transfer(g,F2())[0],[[1]])

class TerminalDecisionTests(unittest.TestCase):
    def test_certified_rejection_does_not_evaluate_maps(self):
        from unittest.mock import patch
        from separator_transfer.decision import terminal_rank_one_test
        c=reduced_cube(2,[1]*3); pairs=acyclic_matching(c,12)
        with patch('separator_transfer.decision.factor_at_cut',side_effect=AssertionError('must not evaluate')):
            result=terminal_rank_one_test(c,pairs)
        self.assertGreater(result['lower'],1)
        self.assertEqual(result['evaluated_maps'],0)
    def test_bound_one_does_not_imply_rank_one(self):
        from separator_transfer.cube import ChainComplex
        from separator_transfer.decision import terminal_rank_one_test
        c=ChainComplex((0,0,0,0,1,1,1),(0,)*7,
            ((2,4),(3,5),(0,4),(0,5),(1,4),(1,5),(2,6),(3,6)))
        result=terminal_rank_one_test(c,((2,4),(3,5)))
        self.assertEqual(result['lower'],1)
        self.assertEqual(result['exact_rank'],3)
        self.assertEqual(result['status'],'RANK_NOT_ONE')
    def test_rank_one_requires_exact_phase(self):
        from separator_transfer.cube import ChainComplex
        from separator_transfer.decision import terminal_rank_one_test
        c=ChainComplex((0,0,0,1,1),(0,)*5,((2,3),(0,3),(1,3),(2,4)))
        result=terminal_rank_one_test(c,((2,3),))
        self.assertEqual(result['lower'],1)
        self.assertEqual(result['exact_rank'],1)
        self.assertEqual(result['evaluated_maps'],1)

if __name__=='__main__': unittest.main()
