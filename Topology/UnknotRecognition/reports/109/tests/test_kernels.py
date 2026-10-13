import copy
import itertools
import json
import random
import unittest
from ordered_kernel import *
from ordered_kernel.decomposition import validate
from ordered_kernel.two_incidence import reachable, reachability_graph
from scripts.oracles import optimal_subsets, sparse, maximum_positive_pivots
from scripts.fixtures import complete_blocks, ball_blocks, triangular, one_column
from reference.positive_predecessor.cancellation.deferred import deferred_plan, transport_exact_counts

class KernelTests(unittest.TestCase):
    def assert_opt(self, counts, weights=None, td=None):
        p = ordered_plan(counts, weights, td)
        self.assertEqual(p['status'], 'OPTIMAL_MATRIX_PLAN')
        self.assertTrue(verify_plan(counts, p, weights))
        ref, _ = optimal_subsets(counts, weights)
        self.assertEqual((p['cost'],len(p['deferred_rows'])), ref)
        return p

    def test_empty(self): self.assert_opt({})
    def test_isolated_rows(self): self.assert_opt({2:{},5:{},9:{}},{2:5,5:0,9:2})
    def test_one_unit(self): self.assert_opt({0:{0:1}})
    def test_nonunit(self): self.assertEqual(self.assert_opt({0:{0:2}})['cost'],1)
    def test_rectangular(self): self.assert_opt({0:{0:1,1:1},1:{1:1,2:1},2:{0:2,2:2}})
    def test_zero_weights(self): self.assert_opt(ball_blocks(2),{0:0,1:0,2:4,3:1})
    def test_sparse_labels(self): self.assert_opt({123:{900:1},9999:{900:1}},{123:12,9999:3})
    def test_huge_bits(self):
        p=self.assert_opt({0:{0:1<<16384},1:{0:1}},{0:1<<16384,1:1})
        self.assertEqual(p['deferred_rows'],[0])
    def test_all_binary_2x3(self):
        for a in itertools.product(range(2),repeat=6): self.assert_opt(sparse([a[:3],a[3:]]))
    def test_all_ternary_2x2(self):
        for a in itertools.product(range(3),repeat=4): self.assert_opt(sparse([a[:2],a[2:]]))
    def test_random_weighted(self):
        rng=random.Random(601)
        for _ in range(70):
            a={r:{c:rng.randrange(1,4) for c in range(5) if rng.random()<0.5} for r in range(5)}
            self.assert_opt(a,{r:rng.randrange(6) for r in a})
    def test_positive_pivot_language(self):
        for a in itertools.product(range(3),repeat=4):
            d=[a[:2],a[2:]]; p=self.assert_opt(sparse(d))
            self.assertEqual(2-p['cost'],maximum_positive_pivots(d))
    def test_join_cycle(self):
        a={0:{0:1,1:1},1:{0:1,1:1}}
        td=Decomposition([(2,3),(0,2,3),(1,2,3)],[None,0,0])
        p=self.assert_opt(a,td=td); self.assertEqual(p['cost'],1)
        self.assertGreater(p['stats']['joins'],0)
    def test_alternate_decompositions(self):
        a=complete_blocks(2); _,adj,_=Matrix.parse(a).graph()
        rng=random.Random(4)
        for _ in range(12):
            order=list(range(len(adj))); rng.shuffle(order)
            td=elimination_decomposition(adj,order)
            self.assert_opt(a,td=td)
    def test_invalid_bag_edge(self):
        with self.assertRaises(ValueError): ordered_plan({0:{0:1}},decomposition=Decomposition([(0,),(1,)],[None,0]))
    def test_invalid_running_intersection(self):
        td=Decomposition([(0,),(),(0,)],[None,0,1])
        with self.assertRaises(ValueError): validate(td,[set()])
    def test_invalid_tree(self):
        with self.assertRaises(ValueError): validate(Decomposition([(),(),()],[None,2,1]),[])
    def test_invalid_input(self):
        for a in ({True:{}},{0:{0:-1}},{0:{0:True}}, {0:[]}, []):
            with self.assertRaises(ValueError): ordered_plan(a)
    def test_invalid_weights(self):
        for w in ({},{0:-1},{0:True},{0:1,1:2}):
            with self.assertRaises(ValueError): ordered_plan({0:{}},w)
    def test_resource_limits(self):
        for lim in (Limits(max_states=0),Limits(max_work=0),Limits(max_width=0)):
            self.assertEqual(ordered_plan({0:{0:1}},limits=lim)['status'],'RESOURCE_LIMIT')
    def test_cancellation(self):
        def stop(): raise InterruptedError('requested')
        with self.assertRaises(InterruptedError): ordered_plan({0:{0:1}},check=stop)
    def test_bad_certificate_duplicate(self):
        a=ball_blocks(1); p=ordered_plan(a); p['deferred_rows']*=2
        self.assertFalse(verify_plan(a,p))
    def test_bad_certificate_unit(self):
        a={0:{0:1}}; p=ordered_plan(a); p['cancellations'][0][1]=4
        self.assertFalse(verify_plan(a,p))
    def test_bad_certificate_cost(self):
        a=ball_blocks(1); p=ordered_plan(a); p['cost']+=1
        self.assertFalse(verify_plan(a,p))
    def test_bad_certificate_source(self):
        p=ordered_plan({0:{0:1}})
        self.assertFalse(verify_plan({0:{0:2}},p))
    def test_predecessor_optimum(self):
        rng=random.Random(7)
        for _ in range(30):
            a={r:{c:rng.choice([1,2]) for c in range(4) if rng.random()<0.55} for r in range(4)}
            p=ordered_plan(a); old=deferred_plan(a,4)
            self.assertEqual(p['cost'],old['minimum_deferrals'])
    def test_passive_transport(self):
        a=complete_blocks(2); p=ordered_plan(a)
        self.assertEqual(transport_counts(a,p),transport_exact_counts(a,p['deferred_rows'],p['cancellations']))
    def test_two_incidence_weighted(self):
        rng=random.Random(18)
        for _ in range(80):
            a={r:{} for r in range(5)}
            for c in range(6):
                for r in rng.sample(list(a),rng.randrange(3)):
                    a[r][c]=rng.randrange(1,4)
            w={r:rng.randrange(7) for r in a}
            p=two_incidence_plan(a,w)
            self.assertEqual((p['cost'],len(p['deferred_rows'])),optimal_subsets(a,w)[0])
            self.assertTrue(verify_two_incidence_optimality(a,p,w))
    def test_two_incidence_reject_arity_three(self):
        with self.assertRaises(ValueError): two_incidence_plan(one_column(3))
    def test_scc_lower_certificate_mutation(self):
        a=ball_blocks(3); p=two_incidence_plan(a)
        p['lower_bound_certificate']['source_components'].pop()
        self.assertFalse(verify_two_incidence_optimality(a,p))
    def test_scc_false_lower_bound(self):
        a={0:{0:1},1:{0:1,1:1}}; p=two_incidence_plan(a)
        p['lower_bound_certificate']['source_components']=[[0,1]]
        self.assertFalse(verify_two_incidence_optimality(a,p))
    def test_scc_long_chain(self):
        a=triangular(3000); p=two_incidence_plan(a)
        self.assertEqual(p['cost'],0); self.assertTrue(verify_two_incidence_optimality(a,p))
    def test_scc_ball_separation(self):
        a=ball_blocks(500); p=two_incidence_plan(a)
        self.assertEqual(p['cost'],500); self.assertTrue(verify_two_incidence_optimality(a,p))
    def test_inert_columns(self):
        a={0:{0:1,8:9},1:{0:2,8:4},2:{8:6}}
        p=self.assert_opt(a); q=two_incidence_plan(a)
        self.assertEqual(q['cost'],p['cost'])
        self.assertTrue(verify_two_incidence_optimality(a,q))
        labels,_,_=Matrix.parse(a).graph()
        self.assertNotIn(('c',8),labels)
    def test_blocking_nonunit_retained(self):
        self.assertEqual(self.assert_opt({0:{0:1},1:{0:2}})['cost'],1)
    def test_generic_weighted_stopping_certificate(self):
        a={0:{0:1},1:{0:1},2:{0:1}}
        p=ordered_plan(a)
        self.assertFalse(verify_weighted_stopping_optimality(a,p,[[0,1,2]]))
        # The packing bound is not always tight; this is not a failed optimum.
        b=ball_blocks(2);q=ordered_plan(b)
        self.assertTrue(verify_weighted_stopping_optimality(b,q,[[0,1],[2,3]]))
    def test_chain_theorem(self):
        from scripts.fixtures import complete_chain_decomposition
        for q in (1,2,3,8,32):
            a=complete_blocks(q);p=ordered_plan(a,decomposition=complete_chain_decomposition(q))
            self.assertEqual(p['cost'],q+1);self.assertEqual(p['stats']['width'],3)
    def test_core_prepeeling(self):
        a={0:{0:1,1:2},1:{1:1,2:1},2:{1:1,2:2}}
        w={0:0,1:4,2:1}
        p=optimize_counts(a,w)
        self.assertEqual(p['cost'],1);self.assertEqual(p['deferred_rows'],[2])
        self.assertEqual(p['stats']['prepeeled_rows'],1)
        self.assertTrue(verify_plan(a,p,w));self.assertTrue(verify_two_incidence_optimality(a,p,w))
    def test_auto_zero(self):
        self.assertEqual(optimize_counts(complete_blocks(0))['method'],'full-private-peeling')
    def test_auto_dispatch(self):
        self.assertEqual(optimize_counts(ball_blocks(1))['method'],'two-incidence-scc')
        self.assertEqual(optimize_counts(complete_blocks(1))['method'],'ordered-interface-dp')

if __name__=='__main__': unittest.main()
