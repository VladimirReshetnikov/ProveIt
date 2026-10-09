"""Bounded-run arithmetic, independent replay, fallback and source proofs."""
import itertools
import random
import unittest
from unittest.mock import patch

from fastunknot.compressed_words import WordArena, CompressedLimit
from fastunknot.syllable_normalize import bounded_cyclic_roots
from fastunknot.syllable_normalize_verify import replay_cyclic_roots
from fastunknot.group_certificate import verify_group_certificate
from test_primitive_projection import inflated_source


def literal(word):
    stack=[]
    for x in word:
        if stack and stack[-1]==-x:stack.pop()
        else:stack.append(x)
    while len(stack)>1 and stack[0]==-stack[-1]:stack=stack[1:-1]
    return stack


def raw_map(arena,roots,images):
    mapped={0:0}
    for node in arena._reachable(roots):
        rule=arena.rules[node]
        mapped[node]=images.get(rule[1],node) if rule[0]=='t' else arena.concat(mapped[rule[1]],mapped[rule[2]])
    return [mapped[r] for r in roots]


class SyllableNormalizeTests(unittest.TestCase):
    def test_uniform_metadata_skips_power_descendants_with_exact_signs(self):
        for fn in (bounded_cyclic_roots,replay_cyclic_roots):
            a=WordArena();n=1<<4096
            pos=a.power(a.letter(1),n);neg=a.power(a.letter(-1),n)
            middle=a.power(a.letter(-2),n+3)
            prefix=a.concat(pos,middle);root=a.concat(prefix,neg)
            allowed={pos,neg,middle,prefix,root};rules=a.rules
            class GuardedRules(list):
                def __getitem__(self,node):
                    if node not in allowed:raise AssertionError('uniform descendant visited')
                    return super().__getitem__(node)
            a.rules=GuardedRules(rules)
            with patch.object(a,'cyclic_reduce',side_effect=AssertionError),patch.object(a,'equal',side_effect=AssertionError):
                answer=fn(a,[root])
            self.assertEqual(a.lengths[answer[0]],n+3);self.assertEqual(a.uniform[answer[0]],-2)
            self.assertEqual(a.stats['run_normalization_nodes'],5)
            self.assertEqual(a.stats['run_normalization_uniform_hits'],3)

    def test_rejection_witness_skips_siblings_and_is_cached_per_cap(self):
        for fn in (bounded_cyclic_roots,replay_cyclic_roots):
            a=WordArena();bad=a.from_word([1,2,1,2,1])
            hidden=a.power(a.from_word([3,4]),1<<1024);root=a.concat(bad,hidden)
            cache={};rules=a.rules;allowed=set(a._reachable([bad]))|{root}
            class GuardedRules(list):
                def __getitem__(self,node):
                    if node not in allowed:raise AssertionError('irrelevant sibling visited')
                    return super().__getitem__(node)
            a.rules=GuardedRules(rules);before=len(a.rules)
            self.assertIsNone(fn(a,[root],cache=cache,min_length=0))
            self.assertEqual(len(a.rules),before)
            self.assertNotIn(hidden,cache[4]);self.assertIsNone(cache[4][root])
            a.rules=rules
            parent=a.concat(root,hidden);before=len(a.rules)
            self.assertIsNone(fn(a,[parent],cache=cache,min_length=0))
            self.assertEqual(len(a.rules),before);self.assertNotIn(hidden,cache[4])
            self.assertIsNone(fn(a,[bad],cache=cache,min_length=0))
            answer=fn(a,[bad],cache=cache,min_length=0,max_runs=5)
            self.assertEqual(a.expand(answer[0]),[1,2,1,2,1])

    def test_exhaustive_short_words_match_literal_and_general_reduction(self):
        for n in range(7):
            for word in itertools.product((1,-1,2,-2),repeat=n):
                a=WordArena();root=a.from_word(word)
                first=bounded_cyclic_roots(a,[root],min_length=0)
                second=replay_cyclic_roots(a,[root],min_length=0)
                self.assertEqual(first is None,second is None)
                if first is not None:
                    self.assertEqual(a.expand(first[0]),literal(word));self.assertEqual(a.expand(second[0]),literal(word))
                self.assertEqual(a.expand(a.cyclic_reduce(root)),literal(word))

    def test_random_parses_caches_limits_and_endpoint_signs(self):
        rng=random.Random(261008508)
        for _ in range(150):
            a=WordArena();word=[rng.choice((-3,-2,-1,1,2,3)) for _ in range(rng.randrange(1,50))]
            nodes=[a.letter(x) for x in word]
            while len(nodes)>1:
                i=rng.randrange(len(nodes)-1);nodes[i:i+2]=[a.concat(nodes[i],nodes[i+1])]
            root=nodes[0];left={};right={}
            for cap in (1,4,16,1):
                aa=bounded_cyclic_roots(a,[root,0,root],cache=left,max_runs=cap,min_length=0)
                bb=replay_cyclic_roots(a,[root,0,root],cache=right,max_runs=cap,min_length=0)
                self.assertEqual(aa is None,bb is None)
                if aa is not None:
                    self.assertEqual([a.expand(r) for r in aa],[literal(word),[],literal(word)])
                    self.assertEqual([a.expand(r) for r in bb],[literal(word),[],literal(word)])
        a=WordArena();r=a.from_word([1,1,2,1,1,1])
        self.assertEqual(a.expand(bounded_cyclic_roots(a,[r],min_length=0)[0]),[1,1,2,1,1,1])

    def test_huge_conjugates_without_general_word_operations(self):
        for bits in (128,4096):
            a=WordArena(max_work=20000000);n=1<<bits;m=n+3
            pos=a.power(a.letter(1),n);neg=a.power(a.letter(-1),n);middle=a.power(a.letter(-2),m)
            roots=[a.concat(a.concat(pos,middle),neg),a.concat(pos,neg)]
            for fn in (bounded_cyclic_roots,replay_cyclic_roots):
                with patch.object(a,'reduce',side_effect=AssertionError),patch.object(a,'cyclic_reduce',side_effect=AssertionError),patch.object(a,'expand',side_effect=AssertionError),patch.object(a,'equal',side_effect=AssertionError),patch.object(a,'slice',side_effect=AssertionError):
                    result=fn(a,roots)
                self.assertIsNotNone(result);self.assertEqual(a.lengths[result[0]],m)
                self.assertEqual(a.uniform[result[0]],-2);self.assertEqual(result[1],0)

    def test_unknown_intermediate_is_no_claim_and_allocates_no_words(self):
        a=WordArena();w=a.power(a.from_word([1,2]),1<<128);r=a.concat(w,a.inverse(w));short=a.power(a.letter(3),128);count=len(a.rules)
        for fn in (bounded_cyclic_roots,replay_cyclic_roots):
            self.assertIsNone(fn(a,[short,r]));self.assertEqual(len(a.rules),count)
            self.assertIsNone(fn(a,[r]));self.assertEqual(len(a.rules),count)
        self.assertEqual(a.cyclic_reduce(r),0)
        self.assertGreaterEqual(len(a.rules),count)

    def test_monomial_maps_preserve_bounded_run_normalization(self):
        a=WordArena(max_work=20000000);roots=[]
        for shift in range(5):
            runs=[a.power(a.letter((i+shift)%5+1 if i%2 else -((i+shift)%5+1)),1<<32) for i in range(4)]
            roots.append(a.concat(a.concat(runs[0],runs[1]),a.concat(runs[2],runs[3])))
        cache={};replay_cache={}
        for phase in range(3):
            images={}
            for g in range(1,6):
                for sign in (1,-1):images[g*sign]=a.power(a.letter(g*sign*(-1 if g%2 else 1)),1<<(phase+16))
            roots=raw_map(a,roots,images)
            with patch.object(a,'reduce',side_effect=AssertionError),patch.object(a,'cyclic_reduce',side_effect=AssertionError),patch.object(a,'expand',side_effect=AssertionError),patch.object(a,'equal',side_effect=AssertionError):
                normalized=bounded_cyclic_roots(a,roots,cache=cache)
                checked=replay_cyclic_roots(a,roots,cache=replay_cache)
            self.assertIsNotNone(normalized);self.assertIsNotNone(checked)
            self.assertTrue(all(a.equal(x,y) for x,y in zip(normalized,checked)))
            roots=normalized

    def test_source_replay_is_independent_and_resource_guards_propagate(self):
        d,c=inflated_source(1024);stats={}
        with patch('fastunknot.syllable_normalize.bounded_cyclic_roots',side_effect=AssertionError),patch('fastunknot.syllable_normalize._join',side_effect=AssertionError),patch('fastunknot.syllable_normalize._cyclic',side_effect=AssertionError):
            self.assertTrue(verify_group_certificate(d,c,compressed=True,max_work=20000000,stats=stats))
        self.assertEqual(stats['run_normalization_hits'],1)
        for fn in (bounded_cyclic_roots,replay_cyclic_roots):
            a=WordArena();r=a.power(a.letter(1),128)
            for bad in (True,0,-1):
                with self.assertRaises(ValueError):fn(a,[r],max_runs=bad)
            a.left=0
            with self.assertRaises(CompressedLimit):fn(a,[r])
            def cancel():raise ValueError('external stop')
            a.check=cancel
            with self.assertRaisesRegex(ValueError,'external'):fn(a,[r])
