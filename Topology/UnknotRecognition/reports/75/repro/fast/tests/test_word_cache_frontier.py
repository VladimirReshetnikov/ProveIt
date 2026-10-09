"""Exact cached frontiers, partial completion and compressed-size work."""
import random
import unittest
from unittest.mock import patch

from fastunknot.compressed_words import WordArena, CompressedLimit
from test_compressed_words import explicit_reduce


class WordCacheFrontierTests(unittest.TestCase):
    def test_mixed_word_operations_match_literal_oracles(self):
        rng=random.Random(261008519)
        for _ in range(200):
            a=WordArena();nodes=[0];words=[[]]
            for _ in range(80):
                i=rng.randrange(len(nodes));word=words[i];node=nodes[i];op=rng.randrange(6)
                if op==0:
                    j=rng.randrange(len(nodes))
                    if len(word)+len(words[j])>1000:continue
                    result=a.concat(node,nodes[j]);expected=word+words[j]
                elif op==1:result=a.inverse(node);expected=[-x for x in reversed(word)]
                elif op==2:result=a.reduce(node);expected=explicit_reduce(word)
                elif op==3:result=a.cyclic_reduce(node);expected=explicit_reduce(word,True)
                elif op==4:
                    lo=rng.randrange(len(word)+1);hi=rng.randrange(lo,len(word)+1)
                    result=a.slice(node,lo,hi);expected=word[lo:hi]
                else:
                    expected=[rng.choice((-3,-2,-1,1,2,3)) for _ in range(rng.randrange(15))]
                    result=a.from_word(expected)
                self.assertEqual(a.expand(result),expected);nodes.append(result);words.append(expected)

    def test_reduced_slice_can_hide_uncached_source_descendants(self):
        a=WordArena();source=a.power(a.from_word([1,2]),1<<12);a.reduce(source)
        part=a.slice(source,3,a.lengths[source]-7)
        hidden=set(a._reachable([part]))-a._reduced.keys()
        self.assertTrue(hidden)
        root=a.concat(part,a.letter(3));before=a.stats.get('word_frontier_nodes',0)
        with patch.object(a,'_reachable',side_effect=AssertionError('cached descendants traversed')):
            result=a.reduce(root)
        self.assertEqual(a.stats['word_frontier_nodes']-before,1)
        self.assertTrue(hidden.isdisjoint(a._reduced))
        self.assertEqual(a.expand(result),([1,2]*(1<<12))[3:-7]+[3])

    def test_deep_growing_prefixes_have_linear_frontier_work(self):
        a=WordArena(max_nodes=20000);root=a.from_word([1,2]);a.reduce(root);a.inverse(root)
        start=a.stats['work'];before=a.stats['word_frontier_nodes']
        with patch.object(a,'_reachable',side_effect=AssertionError('full traversal')),patch.object(a,'expand',side_effect=AssertionError('expansion')):
            for i in range(2400):
                root=a.concat(root,a.letter(1+i%2));self.assertEqual(a.reduce(root),root)
                inv=a.inverse(root);self.assertEqual(a.inverse(inv),root)
        self.assertLess(a.stats['work']-start,40*2400)
        self.assertLessEqual(a.stats['word_frontier_nodes']-before,2*2400)
        self.assertEqual(a.expand(inv),[-x for x in reversed([1,2]+[1+i%2 for i in range(2400)])])

    def test_huge_cached_words_need_only_new_ancestors(self):
        a=WordArena(max_nodes=50000,max_work=1000000)
        word=a.power(a.from_word([1,2]),1<<2048);a.reduce(word);a.inverse(word)
        before=a.stats['work'];root=a.concat(word,a.letter(3))
        with patch.object(a,'expand',side_effect=AssertionError):
            self.assertEqual(a.reduce(root),root);inverse=a.inverse(root)
        self.assertLess(a.stats['work']-before,40)
        self.assertEqual(a.lengths[inverse],(2<<2048)+1)
        self.assertEqual((a.first[inverse],a.last[inverse]),(-3,-1))

    def test_interrupted_discovery_and_evaluation_leave_only_exact_cache_entries(self):
        class Cancelled(Exception):pass
        for operation in ('inverse','reduce'):
            for allowance in (1,25,90,180):
                a=WordArena();word=[1,2,-2,3,-1,2]*40;root=a.from_word(word)
                calls=0
                def check():
                    nonlocal calls
                    calls+=1
                    if calls==allowance:raise Cancelled()
                a.check=check
                try:getattr(a,operation)(root)
                except Cancelled:pass
                a.check=lambda:None
                for node,value in list((a._inverse if operation=='inverse' else a._reduced).items()):
                    source=a.expand(node)
                    expected=[-x for x in reversed(source)] if operation=='inverse' else explicit_reduce(source)
                    self.assertEqual(a.expand(value),expected)
                result=getattr(a,operation)(root)
                expected=[-x for x in reversed(word)] if operation=='inverse' else explicit_reduce(word)
                self.assertEqual(a.expand(result),expected)

    def test_work_and_node_limits_do_not_publish_partial_results(self):
        for operation in ('inverse','reduce'):
            a=WordArena();word=[1,2,-2,3,-1,2]*40;root=a.from_word(word)
            a.left=5
            with self.assertRaises(CompressedLimit):getattr(a,operation)(root)
            a.left=1000000
            result=getattr(a,operation)(root)
            self.assertEqual(a.expand(result),[-x for x in reversed(word)] if operation=='inverse' else explicit_reduce(word))
        a=WordArena();root=a.from_word([1,2,3]);a.max_nodes=len(a.rules)-1
        with self.assertRaises(CompressedLimit):a.inverse(root)
        self.assertNotIn(root,a._inverse);a.max_nodes=1000
        self.assertEqual(a.expand(a.inverse(root)),[-3,-2,-1])
