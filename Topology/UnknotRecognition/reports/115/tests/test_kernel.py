from __future__ import annotations
import copy
import itertools
import json
import random
import unittest
from unittest.mock import patch
from activation_forest import Instance, solve, verify_positive, verify_obstruction
from activation_forest.model import forest, extend_tree, peel
from activation_forest.closure import Activation
from activation_forest.matroid import representatives
from activation_forest.algebra import (vector_rank, wedge_extend, ExteriorBasis,
                                      sample_representation, choose_prime, is_prime,
                                      incidence_vectors)
from activation_forest.solve import search_projected, positive_certificate, WorkLimit
from experiments.fixtures import repository_loop, parallel_obstruction, generic_positive, generic_negative, choice_arms
from experiments.oracles import brute_solve, brute_representatives, brute_projected, deleted_closure


class ModelTests(unittest.TestCase):
    def test_empty(self):
        x=Instance(1,(),(),10**40)
        self.assertEqual(solve(x,try_incumbent=False)['status'],'SUCCESS')
    def test_huge_vertices_rejected_before_allocation(self):
        with self.assertRaises(ValueError): Instance(10**100,(),(),0)
    def test_negative_count(self):
        with self.assertRaises(ValueError): Instance(1,((0,0),),((-1,),),1)
    def test_boolean_count(self):
        with self.assertRaises(ValueError): Instance(1,((0,0),),((True,),),1)
    def test_disconnected(self):
        with self.assertRaises(ValueError): Instance(2,((0,0),),((1,),),1)
    def test_ragged(self):
        with self.assertRaises(ValueError): Instance(1,((0,0),),((1,),),2)
    def test_loops_and_parallel(self):
        x=repository_loop()
        self.assertFalse(forest(x,[4])); self.assertFalse(forest(x,[0,1])); self.assertTrue(forest(x,[2]))
    def test_huge_hex_roundtrip(self):
        x=Instance(1,((0,0),),((2**16384,),),1)
        y=Instance.from_dict(json.loads(json.dumps(x.to_dict())))
        self.assertEqual(x,y); self.assertEqual(x.digest(),y.digest())
    def test_source_digest_is_unsaturated(self):
        a=Instance(1,((0,0),),((2,),),1); b=Instance(1,((0,0),),((3,),),1)
        self.assertNotEqual(a.digest(),b.digest())
    def test_invalid_caps(self):
        for kw in ({'rounds':-1},{'max_b':True},{'seed':'x'},{'max_transitions':-1}):
            with self.assertRaises(ValueError): solve(repository_loop(),**kw)


class ClosureTests(unittest.TestCase):
    def test_pair_direction(self):
        x=Instance(2,((0,1),(0,1)),((1,),(2,)),1)
        a=Activation(x); self.assertEqual(a.mandatory,[{1}]); self.assertEqual(a.b,0)
        self.assertIsNone(peel(x,[0])); self.assertIsNotNone(peel(x,[1]))
    def test_high_nonunit_rows_retained(self):
        x=Instance(2,((0,1),)*3,((1,),(2,),(2,)),1)
        self.assertEqual(Activation(x).boundary,[0,1,2])
    def test_unusable_column_omitted(self):
        x=Instance(2,((0,1),)*3,((2,),(3,),(4,)),1)
        self.assertEqual(Activation(x).b,0)
    def test_horn_trigger(self):
        a=Activation(parallel_obstruction(3))
        self.assertEqual(a.close(1),1); self.assertEqual(a.close(3),7)
    def test_stopping_source(self):
        x=repository_loop(); self.assertIsNone(peel(x,[0])); self.assertIsNotNone(peel(x,[1]))
    def test_seed_mask_full(self):
        x=repository_loop(); a=Activation(x)
        self.assertNotEqual(a.seed_closure([0]),a.full); self.assertEqual(a.seed_closure([1]),a.full)
    def test_closure_idempotent(self):
        a=Activation(repository_loop())
        for mask in range(1<<a.b): self.assertEqual(a.close(a.close(mask)),a.close(mask))
    def test_invalid_mask(self):
        a=Activation(repository_loop())
        with self.assertRaises(ValueError): a.close(1<<a.b)
    def test_choice_arms(self):
        x=choice_arms(3); a=Activation(x)
        self.assertEqual(a.b,7); self.assertEqual(a.mandatory,[])
        self.assertEqual(a.seed_closure([1,4,7]),a.full)
        self.assertNotEqual(a.seed_closure([0,4,7]),a.full)


class AlgebraTests(unittest.TestCase):
    def test_prime_contract(self):
        for q,b in ((0,1),(100,20),(200,100)):
            p=choose_prime(q,b); self.assertTrue(is_prime(p)); self.assertGreater(p,2*(q+b))
    def test_wedge_sign(self):
        self.assertEqual(wedge_extend({2:1},(1,0),101),{3:100})
    def test_duplicate_wedge_zero(self):
        self.assertEqual(wedge_extend(wedge_extend({0:1},(2,3),101),(2,3),101),{})
    def test_basis_preserves_raw_witness(self):
        a=ExteriorBasis(101); a.add({1:1,2:1},(0,)); a.add({1:1,2:2},(1,))
        self.assertEqual(a.witnesses[1][0],{1:1,2:2}); self.assertNotEqual(a.rows[2],a.witnesses[1][0])
    def test_dependent_vector_discarded(self):
        a=ExteriorBasis(101); self.assertTrue(a.add({1:1},(0,))); self.assertFalse(a.add({1:2},(1,)))
    def test_binary_graph_rank(self):
        x=repository_loop(); self.assertEqual(vector_rank(incidence_vectors(x,2),2),1)
    def test_zero_sample_no_false_yes(self):
        class Zero:
            def randrange(self,p): return 0
        x=generic_positive(); self.assertIsNone(sample_representation(x,Activation(x).mandatory,3,101,Zero()))
    def test_random_projection_dimension(self):
        x=generic_positive(); a=Activation(x)
        v=sample_representation(x,a.mandatory,a.b,101,random.Random(42))
        self.assertEqual(len(v[0]),2)
    def test_representatives_shared_cycle(self):
        x=Instance(2,((0,1),(0,1)),((0,),(0,)),1)
        self.assertFalse(representatives(x,[{0},{1}])['complete'])
    def test_forced_representatives(self):
        x=generic_positive(); ans=representatives(x,[{3}],fixed=(0,1))
        self.assertTrue(ans['complete']); self.assertEqual(ans['edges'],[3])
    def test_overlap_rejected(self):
        with self.assertRaises(ValueError): representatives(repository_loop(),[{0},{0}])
    def test_dp_matches_direct(self):
        x=choice_arms(3); a=Activation(x); v=incidence_vectors(x,2)
        found,stats=search_projected(a,v,2)
        self.assertIsNotNone(found); self.assertIsNotNone(brute_projected(a,v,2,3))
        self.assertGreater(stats['discarded'],0)


class SolverTests(unittest.TestCase):
    def test_loop_fixed_source_success(self):
        x=repository_loop(); ans=solve(x,try_incumbent=False)
        self.assertEqual(ans['route'],'faithful-activation'); self.assertEqual(ans['certificate']['tree'],[1])
    def test_generic_success(self):
        ans=solve(generic_positive(),seed=7,try_incumbent=False)
        self.assertEqual(ans['status'],'SUCCESS'); self.assertEqual(ans['route'],'representative-activation')
    def test_generic_negative_is_unknown(self):
        self.assertEqual(solve(generic_negative(),seed=7,rounds=3,try_incumbent=False)['status'],'UNKNOWN')
    def test_exact_negative_frontier(self):
        x=parallel_obstruction(5); ans=solve(x,try_incumbent=False)
        self.assertEqual(ans['status'],'BLOCKED_EXACT'); self.assertTrue(verify_obstruction(x,ans['obstruction']))
    def test_exact_mandatory_negative(self):
        x=Instance(2,((0,1),(0,1)),((),()),0); ans=solve(x,try_incumbent=False)
        self.assertEqual(ans['route'],'mandatory-rank'); self.assertTrue(verify_obstruction(x,ans['obstruction']))
    def test_boundary_cap(self):
        self.assertEqual(solve(repository_loop(),max_b=0,try_incumbent=False)['status'],'UNKNOWN')
    def test_transition_cap(self):
        self.assertEqual(solve(repository_loop(),max_transitions=0,try_incumbent=False)['status'],'UNKNOWN')
    def test_round_cap(self):
        self.assertEqual(solve(generic_positive(),rounds=0,try_incumbent=False)['status'],'UNKNOWN')
    def test_interruption_propagates(self):
        def stop(): raise InterruptedError('test cancellation')
        with self.assertRaises(InterruptedError): solve(repository_loop(),check=stop)
    def test_bad_random_sample_is_unknown(self):
        with patch('activation_forest.solve.sample_representation',return_value=None):
            self.assertEqual(solve(generic_positive(),rounds=2,try_incumbent=False)['status'],'UNKNOWN')
    def test_reproducibility(self):
        x=generic_positive()
        self.assertEqual(solve(x,seed=781,try_incumbent=False),solve(x,seed=781,try_incumbent=False))


class CertificateTests(unittest.TestCase):
    def setUp(self):
        self.x=repository_loop(); self.cert=solve(self.x)['certificate']
    def test_positive(self): self.assertTrue(verify_positive(self.x,self.cert))
    def test_empty_malformed(self):
        for c in (None,[],{},'x'):
            self.assertFalse(verify_positive(self.x,c)); self.assertFalse(verify_obstruction(self.x,c))
    def test_loop_as_tree(self):
        c=copy.deepcopy(self.cert); c['tree']=[4]; self.assertFalse(verify_positive(self.x,c))
    def test_duplicate_tree(self):
        c=copy.deepcopy(self.cert); c['tree']=[1,1]; self.assertFalse(verify_positive(self.x,c))
    def test_forged_pivot(self):
        c=copy.deepcopy(self.cert); c['pivots'][0]=[0,0]; self.assertFalse(verify_positive(self.x,c))
    def test_wrong_dual_child(self):
        c=copy.deepcopy(self.cert); c['dual_order'][0][1]=0; self.assertFalse(verify_positive(self.x,c))
    def test_missing_pivot(self):
        c=copy.deepcopy(self.cert); c['pivots'].pop(); self.assertFalse(verify_positive(self.x,c))
    def test_wrong_digest(self):
        c=copy.deepcopy(self.cert); c['input_sha256']='0'*64; self.assertFalse(verify_positive(self.x,c))
    def test_checker_independent_of_producer(self):
        with patch('activation_forest.solve.peel',side_effect=RuntimeError),patch('activation_forest.algebra.wedge_extend',side_effect=RuntimeError):
            self.assertTrue(verify_positive(self.x,self.cert))
    def test_missing_frontier_state(self):
        x=parallel_obstruction(4); c=solve(x)['obstruction']; c['frontier'].pop()
        self.assertFalse(verify_obstruction(x,c))
    def test_forged_frontier_mask(self):
        x=parallel_obstruction(4); c=solve(x)['obstruction']; c['frontier'][1]['mask']=3
        self.assertFalse(verify_obstruction(x,c))
    def test_frontier_replay_independent(self):
        x=parallel_obstruction(4); c=solve(x)['obstruction']
        with patch('activation_forest.closure.Activation.close',side_effect=RuntimeError),patch('activation_forest.algebra.wedge_extend',side_effect=RuntimeError):
            self.assertTrue(verify_obstruction(x,c))
    def test_duplicate_rank_block(self):
        x=Instance(2,((0,1),(0,1)),((),()),0); c=solve(x)['obstruction']; c['blocks'].append(c['blocks'][0])
        self.assertFalse(verify_obstruction(x,c))
    def test_json_roundtrip(self):
        self.assertTrue(verify_positive(self.x,json.loads(json.dumps(self.cert))))


if __name__=='__main__': unittest.main()
