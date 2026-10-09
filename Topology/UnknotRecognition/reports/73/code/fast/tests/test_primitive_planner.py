"""Immutable eligibility caching, exact skip bounds and compressed singleton donors."""
import unittest
from unittest.mock import patch
from fastunknot.compressed_words import WordArena, CompressedLimit
from fastunknot.compressed_search import _search
from fastunknot.primitive_projection import projection_candidates, plan_projection
from fastunknot.primitive_forest import plan_forest
from fastunknot.primitive_power_verify import verify_compressed_terminal


class PrimitivePlannerTests(unittest.TestCase):
    def test_root_content_is_cached_but_slots_and_live_labels_are_fresh(self):
        a=WordArena();good=a.from_word([5,6]);bad=a.from_word([1,2,3]);cache={}
        first=plan_projection(a,[bad,0,good,good],{1,2,3,5,6},cache)
        self.assertEqual([p['relation'] for p in first],[2])
        nodes=a.stats['projection_metadata_nodes'];descriptors=a.stats['projection_candidate_roots']
        for roots,live,expected in (([good,bad,0],{5,6},[0]),([0,good],{5},[]),([bad,good],{5,6},[1])):
            self.assertEqual([p['relation'] for p in plan_projection(a,roots,live,cache)],expected)
        self.assertEqual(a.stats['projection_metadata_nodes'],nodes)
        self.assertEqual(a.stats['projection_candidate_roots'],descriptors)
        self.assertEqual(first[0]['relation'],2)
        raw=a.from_word([5,7,-7,6]);self.assertEqual(plan_projection(a,[raw],{5,6,7},cache),[])
        reduced=a.reduce(raw);self.assertEqual(len(plan_projection(a,[reduced],{5,6,7},cache)),1)

    def test_negative_profiles_and_nonunit_vectors_are_reused(self):
        a=WordArena();bad=a.from_word([1,1,2,2,2]);nonunit=a.from_word([3,4,3,4,4]);unit=a.from_word([5,6]);roots=[bad,nonunit,unit]
        cache={};self.assertEqual(len(plan_forest(a,roots,set(range(1,7)),cache)),1)
        first=plan_projection(a,roots,set(range(1,7)),cache);self.assertEqual([p['relation'] for p in first],[1,2])
        with patch('fastunknot.primitive_forest.gcd',side_effect=AssertionError),patch('fastunknot.primitive_forest.primitive_power_terminal',side_effect=AssertionError),patch('fastunknot.primitive_projection.primitive_power_terminal',side_effect=AssertionError):
            self.assertEqual(len(plan_forest(a,list(reversed(roots)),set(range(1,7)),cache)),1)
            self.assertEqual([p['relation'] for p in plan_projection(a,list(reversed(roots)),set(range(1,7)),cache)],[0,1])

    def test_huge_unit_donor_and_one_candidate_skip_are_exact(self):
        a=WordArena();root=a.concat(a.power(a.letter(1),1<<4096),a.letter(-2));roots=[0,root,0]
        with patch('fastunknot.primitive_projection.primitive_power_terminal',side_effect=AssertionError),patch('fastunknot.primitive_forest.plan_forest',side_effect=AssertionError),patch.object(a,'expand',side_effect=AssertionError):
            proofs=plan_projection(a,roots,{1,2})
            self.assertTrue(verify_compressed_terminal(a,roots,{1,2},proofs[0]))
            moves=[];terminal={}
            self.assertTrue(_search(a,roots,{1,2},moves,primitive_terminal=terminal,primitive_forest=True,rank_two_terminal=False))
        self.assertEqual(a.stats['forest_candidate_skips'],1)
        self.assertEqual(moves[0]['kind'],'primitive_projection')
        self.assertEqual(proofs[0]['primitive_vector'],[1<<4096,-1])
        self.assertEqual(proofs[0]['relation'],1)

    def test_shared_snapshot_preserves_original_donor_slots_and_limits(self):
        a=WordArena();roots=[0,a.from_word([1,2]),a.from_word([1,3]),a.from_word([4,5,4,5,5])];cache={}
        prepared=projection_candidates(a,roots,set(range(1,6)),cache)
        with patch('fastunknot.primitive_forest.projection_candidates',side_effect=AssertionError),patch('fastunknot.primitive_projection.projection_candidates',side_effect=AssertionError):
            self.assertEqual([e['proof']['relation'] for e in plan_forest(a,roots,set(range(1,6)),cache,_prepared=prepared)],[1,2])
            self.assertEqual([p['relation'] for p in plan_projection(a,roots,set(range(1,6)),cache,_prepared=prepared)],[1,3])
        a.left=1
        with self.assertRaises(CompressedLimit):projection_candidates(a,roots,set(range(1,6)),cache)
        def cancel():raise ValueError('caller cancelled')
        a.check=cancel
        with self.assertRaisesRegex(ValueError,'caller'):projection_candidates(a,roots,set(range(1,6)),cache)
