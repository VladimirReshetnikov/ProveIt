import unittest
import random
from dataclasses import replace
from unittest.mock import patch
from signed_continuations.core import *
from signed_continuations.verify import assignments, graph_compatible, verify_basis
from signed_continuations.transitions import reduce_buckets, join_families, optional_signed_edges


def expand_mask(p):
    return sum(1 << x for x in assignments(p))


def query_values(fam,r):
    return [None if (best:=optimum(fam,q)) is None else best.cost for q in partitions(r)]


class PartitionsTests(unittest.TestCase):
    def test_counts(self):
        self.assertEqual([sum(1 for _ in partitions(r)) for r in range(1,7)], [1,3,11,49,257,1539])
    def test_canonical(self):
        self.assertEqual(SignedPartition.canonical([8,2,8,2],[1,0,0,1]), SignedPartition((0,1,0,1),(0,0,1,1)))
    def test_reject_invalid(self):
        for labels,offsets in [((1,),(0,)),((0,),(1,)),((0,2),(0,0)),((0,),(True,)),((True,),(0,))]:
            with self.assertRaises((TypeError,ValueError)): SignedPartition(labels,offsets)
    def test_dsu_cycle(self):
        self.assertIsNone(SignedPartition.from_edges(3,[(0,1,1),(1,2,1),(0,2,1)]))
        p = SignedPartition.from_edges(3,[(0,1,1),(1,2,1),(0,2,0)])
        self.assertEqual(p.offsets,(0,1,0))
    def test_vectors_independent(self):
        for r in range(1,6):
            for p in partitions(r): self.assertEqual(p.vector(), expand_mask(p))
    def test_all_factorizations(self):
        for r in range(1,6):
            ps = list(partitions(r)); vs = [p.vector() for p in ps]
            for i,a in enumerate(ps):
                for j,b in enumerate(ps):
                    self.assertEqual((vs[i]&vs[j]).bit_count()%2,graph_compatible(a,b))
    def test_oneblock_identity(self):
        for r in range(1,7):
            vs = [p.vector() for p in partitions(r) if p.blocks == 1]
            self.assertEqual(set(vs), {1<<i for i in range(1<<(r-1))})
    def test_budget(self):
        with self.assertRaises(BudgetExceeded): SignedPartition.discrete(30).vector(max_dimension=1024)
        with self.assertRaises(BudgetExceeded): SignedPartition.discrete(3).vector(max_dimension=3)
        self.assertEqual(SignedPartition.discrete(1).vector(max_dimension=1),1)
    def test_permute_and_gauge(self):
        for p in partitions(4):
            for flips in ((0,1,0,1),(1,0,1,0)):
                out=p.gauge(flips)
                expected=0
                for x in assignments(p):
                    spin=[0]+[(x>>i)&1 for i in range(3)]
                    spin=[a^b for a,b in zip(spin,flips)]; spin=[v^spin[0] for v in spin]
                    j=sum(spin[i]<<(i-1) for i in range(1,4)); expected|=1<<j
                self.assertEqual(out.vector(),expected)
            out=p.restrict([3,1,0,2])
            self.assertEqual(out.blocks,p.blocks)


class BasisTests(unittest.TestCase):
    def test_exhaustive_weighted_queries(self):
        for r in range(1,5):
            fam=[Candidate(p, ((i*173)%97)-60, str(i)) for i,p in enumerate(partitions(r))]
            red=reduce_family(fam)
            self.assertLessEqual(len(red.candidates),1<<(r-1))
            self.assertTrue(verify_basis(fam,red.certificate))
            self.assertEqual(query_values(fam,r),query_values(red.candidates,r))
    def test_random_queries(self):
        rng=random.Random(90013); ps=list(partitions(4))
        for _ in range(80):
            fam=[Candidate(rng.choice(ps),rng.randrange(-1000,1001),str(i)) for i in range(rng.randrange(1,90))]
            red=reduce_family(fam)
            self.assertTrue(verify_basis(fam,red.certificate))
            self.assertEqual(query_values(fam,4),query_values(red.candidates,4))
    def test_ties_original_witness(self):
        p=SignedPartition.discrete(2)
        fam=[Candidate(p,3,"first"),Candidate(p,3,"second")]
        self.assertEqual(reduce_family(fam).candidates,(fam[0],))
    def test_huge_signed_cost(self):
        fam=[Candidate(p, -(1<<4096)+i, str(i)) for i,p in enumerate(partitions(3))]
        red=reduce_family(fam)
        self.assertTrue(verify_basis(fam,red.certificate))
        self.assertEqual(query_values(fam,3),query_values(red.candidates,3))
    def test_empty(self):
        red=reduce_family([])
        self.assertEqual(red.candidates,())
        self.assertTrue(verify_basis([],red.certificate))
    def test_geometry_buckets(self):
        fam=[Candidate(SignedPartition.discrete(2),0,"a","A"),Candidate(SignedPartition.discrete(2),-1,"b","B")]
        with self.assertRaises(ValueError): reduce_family(fam)
        self.assertEqual(len(reduce_buckets(fam)),2)
    def test_width_bucket(self):
        with self.assertRaises(ValueError): reduce_family([Candidate(SignedPartition.discrete(r),0,str(r)) for r in (2,3)])
    def test_candidate_budget(self):
        with self.assertRaises(BudgetExceeded): reduce_family([Candidate(SignedPartition.discrete(1),0,"x")],max_candidates=0)
    def test_boolean_cost_rejected(self):
        with self.assertRaises(TypeError): Candidate(SignedPartition.discrete(1),True,"x")
    def test_independent_replay(self):
        fam=[Candidate(p,i,"witness") for i,p in enumerate(partitions(4))]
        cert=reduce_family(fam).certificate
        with patch.object(SignedPartition,"vector",side_effect=AssertionError("producer disabled")), patch.object(SignedPartition,"from_edges",side_effect=AssertionError("producer disabled")):
            self.assertTrue(verify_basis(fam,cert))
    def test_certificate_mutations(self):
        fam=[Candidate(p,-p.blocks,str(i)) for i,p in enumerate(partitions(4))]
        cert=reduce_family(fam).certificate
        wrong=[replace(cert,width=5),replace(cert,geometry_key="wrong"),replace(cert,selected=cert.selected+(cert.selected[0],)),replace(cert,selected=(999,)),replace(cert,expressions=cert.expressions[:-1]),replace(cert,expressions=(cert.expressions[0]^1,)+cert.expressions[1:]),replace(cert,expressions=(True,)+cert.expressions[1:])]
        for c in wrong: self.assertFalse(verify_basis(fam,c))
    def test_dominance_mutation(self):
        p=SignedPartition.discrete(2); fam=[Candidate(p,0,"cheap"),Candidate(p,1,"expensive")]
        cert=BasisCertificate((1,),(1,1),2,"abstract")
        self.assertFalse(verify_basis(fam,cert))
    def test_parity_needed(self):
        a=SignedPartition((0,0),(0,0)); b=SignedPartition((0,0),(0,1))
        self.assertEqual(a.labels,b.labels)
        self.assertTrue(compatible(a,a)); self.assertFalse(compatible(a,b))
    def test_not_count_preserving(self):
        p=SignedPartition.discrete(1); fam=[Candidate(p,0,"a"),Candidate(p,0,"b")]
        red=reduce_family(fam)
        self.assertEqual(len(red.candidates),1)
        self.assertNotEqual(len(fam)%2,len(red.candidates)%2)
    def test_not_exact_cost_spectrum(self):
        p=SignedPartition.discrete(1); fam=[Candidate(p,0,"disk"),Candidate(p,2,"genus-one")]
        self.assertEqual([x.cost for x in reduce_family(fam).candidates],[0])
        self.assertIn(2,[x.cost for x in fam])


class TransitionTests(unittest.TestCase):
    def test_edge_hadamard(self):
        for p in partitions(4):
            for a,b,s in ((0,1,0),(0,3,1),(1,2,1)):
                constraint=SignedPartition.from_edges(4,[(a,b,s)])
                out=p.add_edge(a,b,s)
                self.assertEqual(0 if out is None else out.vector(),p.vector()&constraint.vector())
    def test_introduce_linear(self):
        for p in partitions(4):
            v=p.vector(); self.assertEqual(p.introduce().vector(),v|(v<<8))
    def test_forget_xor(self):
        for p in partitions(4):
            for forgotten in (1,2,3):
                out=p.restrict([i for i in range(4) if i!=forgotten])
                expected=0
                for x in assignments(p):
                    bits=[(x>>j)&1 for j in range(3)]; bits.pop(forgotten-1)
                    y=sum(b<<j for j,b in enumerate(bits)); expected ^= 1<<y
                self.assertEqual(0 if out is None else out.vector(),expected)
    def test_orphan_rejection(self):
        p=SignedPartition.discrete(2)
        self.assertIsNone(p.restrict([0]))
        self.assertEqual(p.restrict([0],reject_orphans=False).blocks,1)
        self.assertFalse(compatible(p,SignedPartition.discrete(2)))
    def test_disjoint_bilinear(self):
        for a in partitions(2):
            for b in partitions(3):
                out=a.disjoint(b); expected=0
                for x in range(16):
                    spin=[0]+[(x>>i)&1 for i in range(4)]
                    xa=spin[1]
                    xb=(spin[3]^spin[2])|((spin[4]^spin[2])<<1)
                    if (a.vector()>>xa)&1 and (b.vector()>>xb)&1: expected|=1<<x
                self.assertEqual(out.vector(),expected)
    def test_join_families_preserves(self):
        rng=random.Random(71); ps=list(partitions(4))
        for _ in range(20):
            a=[Candidate(rng.choice(ps),rng.randrange(-12,14),str(i)) for i in range(17)]
            b=[Candidate(rng.choice(ps),rng.randrange(-12,14),str(i)) for i in range(11)]
            raw=join_families(a,b,key="joined",charge=7)
            small=join_families(reduce_family(a).candidates,reduce_family(b).candidates,key="joined",charge=7)
            self.assertEqual(query_values(raw,4),query_values(small,4))
    def test_full_transition_workloads(self):
        rng=random.Random(116)
        for r in range(2,6):
            edges=[(i,j,rng.randrange(-7,10),rng.randrange(-7,10)) for i in range(r) for j in range(i)]
            full,_=optional_signed_edges(r,edges,reduced=False)
            small,h=optional_signed_edges(r,edges,reduced=True)
            self.assertEqual(query_values(full,r),query_values(small,r))
            self.assertTrue(all(x['after']<=1<<(r-1) for x in h['history']))
