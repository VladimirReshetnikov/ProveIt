"""Persistent exact occurrence masks and supported substitution frontiers."""
from collections import Counter
import random
import unittest
from unittest.mock import patch
from fastunknot.compressed_words import WordArena, CompressedLimit
from test_compressed_words import explicit_reduce


def singleton_oracle(words):
    return [sorted(g for g,n in Counter(map(abs,w)).items() if n==1) for w in words]


class SparseSubstitutionTests(unittest.TestCase):
    def test_reordered_repeated_roots_and_new_sparse_labels(self):
        a=WordArena();words=[[1009,-41,1009],[],[19,-3,41]];roots=[a.from_word(w) for w in words]
        self.assertEqual(a.singletons(roots),singleton_oracle(words));before=a.stats['letter_mask_nodes']
        indices=[2,0,2,1];self.assertEqual(a.singletons([roots[i] for i in indices]),singleton_oracle([words[i] for i in indices]))
        self.assertEqual(a.stats['letter_mask_nodes'],before)
        new=a.from_word([1,100000000000000000000003,-3]);roots.append(new);words.append([1,100000000000000000000003,-3])
        self.assertEqual(a.singletons(roots),singleton_oracle(words))
        self.assertEqual(len(a._letter_bits),6)
        self.assertLess(max(a._letter_bits.values()).bit_length(),10)

    def test_random_signed_simultaneous_substitution_and_raw_cancellation(self):
        rng=random.Random(261008522)
        for _ in range(400):
            words=[[rng.choice((-7,-3,-1,1,3,7)) for _ in range(rng.randrange(24))] for _ in range(rng.randrange(1,9))]
            images={x:[rng.choice((-7,-3,-1,1,3,7)) for _ in range(rng.randrange(7))] for x in (-7,-3,-1,1,3,7) if rng.randrange(2)}
            expected=[explicit_reduce([y for x in w for y in images.get(x,[x])]) for w in words]
            for warm in (False,True):
                a=WordArena();roots=[a.from_word(w) for w in words];mapping={x:a.from_word(w) for x,w in images.items()}
                if warm:self.assertEqual(a.singletons(roots),singleton_oracle(words))
                answer=a.substitute(roots,mapping)
                self.assertEqual([a.expand(r) for r in answer],expected)
                self.assertEqual(a.singletons(answer),singleton_oracle(expected))
                # Images containing source letters are not recursively substituted.
                answer=a.substitute(answer,{1:a.from_word([1,3]),3:a.letter(-1)})
                twice=[explicit_reduce([y for x in w for y in {1:[1,3],3:[-1]}.get(x,[x])]) for w in expected]
                self.assertEqual([a.expand(r) for r in answer],twice)

    def test_unchanged_raw_frontier_is_reduced_and_absent_images_ignored(self):
        a=WordArena();roots=[a.from_word([1,2,-2,-1,3]),a.from_word([1,-1]),0]
        a.singletons(roots)
        for mapping in ({7:a.letter(8)},{-3:a.letter(9)},{'unused':0}):
            with patch.object(a,'_reachable',side_effect=AssertionError('full source traversal')):
                result=a.substitute(roots,mapping)
            self.assertEqual([a.expand(r) for r in result],[[3],[],[]])

    def test_warm_huge_substitution_visits_only_affected_ancestors(self):
        a=WordArena(max_nodes=30000,max_work=1000000)
        prefix=a.reduce(a.power(a.from_word([1,2]),1<<2048));root=a.concat(prefix,a.letter(3));image=a.letter(4)
        self.assertEqual(a.singletons([root,prefix]),[[3],[]]);start=a.stats['work'];before=a.stats.get('substitution_changed_nodes',0)
        with patch.object(a,'_reachable',side_effect=AssertionError('full source traversal')),patch.object(a,'expand',side_effect=AssertionError('expansion')):
            out=a.substitute([root,prefix,root],{3:image})
        self.assertLess(a.stats['work']-start,40);self.assertEqual(a.stats['substitution_changed_nodes']-before,2)
        self.assertEqual(out[1],prefix);self.assertEqual(out[0],out[2]);self.assertEqual(a.last[out[0]],4)
        self.assertEqual(a.lengths[out[0]],(2<<2048)+1)

    def test_cold_path_and_incomplete_root_metadata_use_general_substitution(self):
        a=WordArena();known=a.from_word([1,2]);other=a.from_word([3,4]);a.singletons([known])
        with patch.object(a,'_reachable',wraps=a._reachable) as full:
            result=a.substitute([known,other],{1:a.letter(5)})
        self.assertGreater(full.call_count,0);self.assertNotIn('supported_substitutions',a.stats)
        self.assertEqual([a.expand(r) for r in result],[[5,2],[3,4]])
        self.assertNotIn(other,a._letter_masks)

    def test_partial_mask_discovery_and_substitution_can_be_retried(self):
        class Cancelled(Exception):pass
        for operation in ('masks','substitute'):
            for limit in (1,15,60):
                a=WordArena();word=[1009,1,-1,3,-7,41]*40;root=a.from_word(word);image=a.from_word([7,-3])
                if operation=='substitute':a.singletons([root])
                calls=0
                def check():
                    nonlocal calls
                    calls+=1
                    if calls==limit:raise Cancelled()
                a.check=check
                try:a.singletons([root]) if operation=='masks' else a.substitute([root],{3:image})
                except Cancelled:pass
                a.check=lambda:None
                self.assertEqual(a.singletons([root]),singleton_oracle([word]))
                result=a.substitute([root],{3:image})
                self.assertEqual(a.expand(result[0]),explicit_reduce([y for x in word for y in ([7,-3] if x==3 else [x])]))
        a=WordArena();root=a.from_word([1,2,3]*20);a.left=1
        with self.assertRaises(CompressedLimit):a.singletons([root])
        a.left=1000000;self.assertEqual(a.singletons([root]),[[]])

    def test_growing_singleton_queries_visit_only_new_grammar(self):
        a=WordArena(max_nodes=10000);root=0
        for i in range(1500):
            root=a.concat(root,a.letter(1+i%2));self.assertEqual(a.singletons([root]),[[1]] if i==0 else [[1,2]] if i==1 else [[2]] if i==2 else [[]])
        self.assertLess(a.stats['letter_mask_nodes'],1510)
        self.assertLess(a.stats['work'],30000)
