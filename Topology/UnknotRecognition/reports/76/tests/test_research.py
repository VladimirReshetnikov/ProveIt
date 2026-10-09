from __future__ import annotations
import copy
import itertools
import random
import sys
import unittest
from pathlib import Path
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'code'))
from disk_algebra import *
from compressed_search import *
from checker import check, independent_feature, independent_compose, independent_disk_cap
from mesh_oracle import replay_pair, replay_word
from star_search import star_summary
from sequential_baseline import run as one_sided


def example(b=2, w=5, q=2):
    return repeated_source(b, [
        {'partition': list(identity(b).partition), 'cost': 2, 'charge': 0},
        {'partition': list(identity(b).partition), 'cost': -1, 'charge': q-1},
        {'partition': [0]*(2*b), 'cost': -4, 'charge': 0},
        {'partition': list(range(2*b)), 'cost': 0, 'charge': 0},
    ], w, q)


def signatures(table, ps, q):
    return tuple(min((x.cost for x in table if x.charge == h and disk_cap(x.partition, cap)), default=None)
                 for cap in ps for h in range(q))


class AlgebraTests(unittest.TestCase):
    def test_canonical(self):
        self.assertEqual(canonical((7,4,7,9)), (0,1,0,2))
    def test_invalid_partitions(self):
        for p in ((), (1,), (0,-1), (0,2), (0,True)):
            with self.assertRaises(ValueError): feature(p)
    def test_partition_counts(self):
        self.assertEqual([len(list(partitions(n))) for n in range(1,7)], [1,2,5,15,52,203])
    def test_transversal_features(self):
        for n in range(1,7):
            for p in partitions(n): self.assertEqual(feature(p), independent_feature(p))
    def test_exact_rank(self):
        for n in range(1,7):
            self.assertEqual(binary_rank(feature(p) for p in partitions(n)), 1<<(n-1))
    def test_pairing(self):
        for n in range(1,6):
            for p in partitions(n):
                for q in partitions(n): self.assertEqual(cap_pairing(p,q), disk_cap(p,q))
    def test_dimension_validation(self):
        with self.assertRaises(ValueError): Morphism(0,2,(0,0))
        with self.assertRaises(ValueError): Morphism(1,2,(0,0))
    def test_identity(self):
        for p in partitions(4):
            x=Morphism(2,2,p)
            self.assertEqual(compose(identity(2),x),x)
            self.assertEqual(compose(x,identity(2)),x)
    def test_general_composition(self):
        for a,b,c in ((1,2,1),(2,1,2),(2,2,2)):
            for p in partitions(a+b):
                for q in partitions(b+c):
                    x=compose(Morphism(a,b,p),Morphism(b,c,q))
                    self.assertEqual(None if x is None else x.partition, independent_compose(p,q,a,b,c))
    def test_associativity(self):
        ps=[Morphism(2,2,p) for p in partitions(4)]
        for p,q,r in itertools.product(ps,repeat=3):
            self.assertEqual(compose(compose(p,q),r),compose(p,compose(q,r)))
    def test_nilpotent(self):
        e=Morphism(1,1,(0,1))
        self.assertIsNone(compose(e,e))
        self.assertEqual(matrix(e),((2,),))
    def test_cycle_zero(self):
        self.assertIsNone(compose(Morphism(1,2,(0,0,0)),Morphism(2,1,(0,0,0))))
    def test_sealed_zero(self):
        self.assertIsNone(compose(Morphism(1,2,(0,0,1)),Morphism(2,1,(0,1,0))))
    def test_splitter_orthogonality(self):
        for b in range(1,5):
            us,vs=splitters(b)
            for i,u in enumerate(us):
                for j,v in enumerate(vs): self.assertEqual(dual_scalar(compose(u,v)),int(i==j))
    def test_splitter_resolution(self):
        for b in range(1,5):
            us,vs=splitters(b);row=0
            for u,v in zip(us,vs): row^=feature(compose(v,u).partition)
            self.assertEqual(row,feature(identity(b).partition))
    def test_matrix_composition(self):
        ps=[Morphism(2,2,p) for p in partitions(4)]
        for p,q in itertools.product(ps,repeat=2):
            z=compose(p,q)
            actual=matrix(z) if z else ((0,0),(0,0))
            self.assertEqual(actual,matrix_product(matrix(q),matrix(p)))
    def test_trace_pairing(self):
        for p,q in itertools.product(partitions(4),repeat=2):
            x=matrix_trace_epsilon(matrix_product(matrix(flip(Morphism(2,2,q))),matrix(Morphism(2,2,p))))
            self.assertEqual(x,disk_cap(p,q))
    def test_tensor_interchange(self):
        rng=random.Random(100)
        ps=[Morphism(1,2,p) for p in partitions(3)]
        qs=[Morphism(2,1,p) for p in partitions(3)]
        for _ in range(500):
            p,r=rng.choices(ps,k=2);q,s=rng.choices(qs,k=2)
            self.assertEqual(compose(tensor(p,r),tensor(q,s)), tensor(compose(p,q),compose(r,s)))


class SearchTests(unittest.TestCase):
    def test_power_zero(self):
        r=solve(example(w=0)); self.assertEqual(r.tables[r.program.root][0].partition,identity(2).partition)
    def test_power_one(self):
        s=example(w=1);r=solve(s)
        self.assertEqual(r.program.root,0)
    def test_power_against_explicit(self):
        for w in range(9):
            s=example(w=w);r=solve(s);exact=sequential(s,w,exact=True)
            self.assertEqual(signatures(r.tables[r.program.root],list(partitions(4)),2),signatures(exact,list(partitions(4)),2))
    def test_negative_fixed_costs(self):
        s=repeated_source(1,[{'partition':[0,0],'cost':-3}],19)
        self.assertEqual(solve(s).query((0,1))['cost'],-57)
    def test_independent_repetition(self):
        s=repeated_source(1,[{'partition':[0,0],'cost':0,'charge':0},
                             {'partition':[0,0],'cost':-1,'charge':1}],4,2)
        r=solve(s);ans=r.query((0,1),[1])
        self.assertEqual(ans['cost'],-3)
        self.assertEqual(sorted(x['count'] for x in r.witness_statistics(ans['witness'])['atom_counts']),[1,3])
    def test_huge_exponent(self):
        w=2**1024+17;s=repeated_source(1,[{'partition':[0,0],'cost':7}],w)
        r=solve(s);ans=r.query((0,1))
        self.assertEqual(ans['cost'],7*w)
        stats=r.witness_statistics(ans['witness'])
        self.assertEqual(stats['expanded_length'],w)
        self.assertLess(stats['reachable_dag_nodes'],1100)
    def test_nested_power(self):
        s=example(b=1,w=7)
        s['nodes'].append({'kind':'power','base':1,'exponent':11})
        r=solve(s);self.assertEqual(r.program.rules[r.program.root].length,77)
    def test_union(self):
        s={'width':1,'nodes':[{'kind':'atoms','options':[{'partition':[0,0],'cost':4}]},
                             {'kind':'atoms','options':[{'partition':[0,0],'cost':1}]},
                             {'kind':'union','children':[0,1]}]}
        self.assertEqual(solve(s).query((0,1))['cost'],1)
    def test_empty_library(self):
        r=solve(repeated_source(1,[],50)); self.assertEqual(r.query((0,1))['status'],'NO_DISK_IN_GRAMMAR')
    def test_empty_zero_power(self):
        r=solve(repeated_source(1,[],0)); self.assertEqual(r.query((0,1))['cost'],0)
    def test_span_mismatch(self):
        s=example();s['nodes'].append({'kind':'union','children':[0,1]})
        with self.assertRaises(ValueError): solve(s)
    def test_future_reference(self):
        s={'width':1,'nodes':[{'kind':'concat','left':0,'right':0}]}
        with self.assertRaises(ValueError): solve(s)
    def test_bad_charge_group(self):
        s=example();s['charges']=3
        with self.assertRaises(ValueError): solve(s)
    def test_negative_exponent(self):
        s=example();s['nodes'][1]['exponent']=-1
        with self.assertRaises(ValueError): solve(s)
    def test_dimension_guard(self):
        with self.assertRaises(ResourceLimit): solve(example(),max_feature_dimension=1)
    def test_work_guard(self):
        with self.assertRaises(ResourceLimit): solve(example(),max_pairs=0)
    def test_expansion_guard(self):
        r=solve(example(b=1,w=100));a=r.query((0,1))
        with self.assertRaises(ResourceLimit):r.expand_witness(a['witness'],max_atoms=20)
    def test_witness_length(self):
        r=solve(example(b=1,w=17));a=r.query((0,1))
        self.assertEqual(len(r.expand_witness(a['witness'])),17)
    def test_one_sided_control(self):
        s=example(w=23);cap=(0,0,1,2)
        a=solve(s).query(cap,[1])['cost']
        b,_=one_sided(2,s['nodes'][0]['options'],23,(0,0),(0,1),[1])
        self.assertEqual(a,b)


class CertificateTests(unittest.TestCase):
    def test_valid_run(self):
        s=example();r=solve(s);v=check(s,r.certificate());self.assertEqual(v.tables,r.tables)
    def test_digest_tamper(self):
        s=example();c=solve(s).certificate();s['nodes'][0]['options'][0]['cost']=999
        with self.assertRaises(ValueError):check(s,c)
    def test_omitted_table(self):
        s=example();c=solve(s).certificate();c['selections'].pop()
        with self.assertRaises(ValueError):check(s,c)
    def test_omitted_independent_row(self):
        s=example();c=solve(s).certificate();c['selections'][0]=[]
        with self.assertRaises(ValueError):check(s,c)
    def test_duplicate_row(self):
        s=example();c=solve(s).certificate();c['selections'][0].append(c['selections'][0][0])
        with self.assertRaises(ValueError):check(s,c)
    def test_out_of_range(self):
        s=example();c=solve(s).certificate();c['selections'][0][0]=10000
        with self.assertRaises(ValueError):check(s,c)
    def test_cost_domination(self):
        s=repeated_source(1,[{'partition':[0,0],'cost':3},{'partition':[0,0],'cost':1}],1)
        c=solve(s).certificate();c['selections'][0]=[0]
        with self.assertRaises(ValueError):check(s,c)
    def test_wrong_root(self):
        s=example();c=solve(s).certificate();c['root']=0
        with self.assertRaises(ValueError):check(s,c)
    def test_huge_checked(self):
        s=example(b=1,w=2**256);r=solve(s);v=check(s,r.certificate())
        self.assertEqual(v.tables,r.tables)


class GeometryAndStarTests(unittest.TestCase):
    def test_mesh_all_small(self):
        for n in range(1,5):
            for p,q in itertools.product(partitions(n),repeat=2):
                self.assertEqual(replay_pair(p,q)['is_single_disk'],disk_cap(p,q))
    def test_mesh_annulus(self):
        x=replay_pair((0,0),(0,0))
        self.assertEqual(x['components'][0]['euler'],0)
        self.assertFalse(x['is_single_disk'])
    def test_mesh_word(self):
        r=solve(example(b=2,w=4));cap=(0,0,1,2);a=r.query(cap)
        word=[r.program.rules[n].args[i][0] for n,i in r.expand_witness(a['witness'])]
        self.assertTrue(replay_word(2,word,cap)['is_single_disk'])
    def test_star_negative_rejected(self):
        s=example(b=1);s['nodes']=s['nodes'][:1]
        with self.assertRaises(ValueError):star_summary(s)
    def test_star_parity(self):
        s={'width':1,'charges':2,'nodes':[{'kind':'atoms','options':[{'partition':[0,0],'cost':3,'charge':1}]}]}
        rows,stats=star_summary(s)
        self.assertEqual(min(x.cost for x in rows if x.charge==1),3)
        self.assertLess(stats['max_word_length'],4)
    def test_star_against_bounded(self):
        rng=random.Random(22)
        for _ in range(50):
            options=[{'partition':list(p),'cost':rng.randrange(5),'charge':rng.randrange(2)} for p in partitions(2)]
            s={'width':1,'charges':2,'nodes':[{'kind':'atoms','options':options}]}
            rows,_=star_summary(s)
            allrows=[]
            for w in range(4):allrows.extend(sequential(s,w,exact=True))
            self.assertEqual(signatures(rows,list(partitions(2)),2),signatures(allrows,list(partitions(2)),2))


if __name__=='__main__':unittest.main()
