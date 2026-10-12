"""Exact reachability maintenance and phase-aware trial allowances."""
from collections import Counter
import random
import unittest
from unittest.mock import patch

from fastunknot import Diagram
from fastunknot.compressed_words import WordArena
from fastunknot.compressed_search import compressed_certificate
from fastunknot.elimination_batch import plan_batch
from fastunknot.group_certificate import GroupLimit, group_decide, verify_group_certificate


def literal_plan(words,alive):
    counts=Counter(abs(x) for w in words for x in w);candidates=[];supports=[]
    for slot,word in enumerate(words):
        local=Counter(abs(x) for x in word);supports.append(set(local))
        if set(local)<=alive:
            candidates.extend(((len(word)-2)*counts[g],len(word),slot,g) for g,n in local.items() if n==1)
    graph={};used=set();answer=[]
    for _,_,slot,g in sorted(candidates):
        if g in graph or slot in used or len(graph)>=len(alive)-1:continue
        dependencies=supports[slot]-{g};stack=list(dependencies);seen=set()
        while stack:
            v=stack.pop()
            if v in seen:continue
            seen.add(v);stack.extend(graph.get(v,()))
        if g in seen:continue
        graph[g]=dependencies;used.add(slot);answer.append(dict(relation=slot,generator=g))
    return answer


class EliminationReachTests(unittest.TestCase):
    def test_cached_reach_matches_fresh_dfs_with_reordered_roots_and_live_sets(self):
        rng=random.Random(261008517);labels=[1,3,19,41,103,1009]
        for _ in range(350):
            words=[[rng.choice((-1,1))*rng.choice(labels) for _ in range(rng.randrange(14))] for _ in range(rng.randrange(1,12))]
            a=WordArena();roots=[a.from_word(w) for w in words];cache={}
            self.assertEqual(plan_batch(a,roots,set(labels),cache),literal_plan(words,set(labels)))
            indices=list(range(len(words)));rng.shuffle(indices);indices+=indices[:2]
            alive={g for g in labels if rng.randrange(3)}
            self.assertEqual(plan_batch(a,[roots[i] for i in indices],alive,cache),literal_plan([words[i] for i in indices],alive))

    def test_late_definitions_update_ancestors_before_rejecting_a_cycle(self):
        words=[[g,-g-1] for g in range(1,40)]+[[40,-1]]
        # The unused survivor prevents the rank cap from hiding the last cycle.
        a=WordArena();roots=[a.from_word(w) for w in words];alive=set(range(1,42))
        result=plan_batch(a,roots,alive)
        self.assertEqual(result,literal_plan(words,alive));self.assertEqual(len(result),39)
        self.assertGreater(a.stats['elimination_reach_updates'],100)
        self.assertGreater(a.stats['elimination_cycle_queries'],len(result))

    def test_post_recovery_cap_preserves_total_cap_and_large_source_replay(self):
        d=Diagram.from_braid(257,list(range(1,257)))
        stats={};c=compressed_certificate(d,elimination_batch=True,post_recovery_work=50000,max_work=2000000,stats=stats)
        self.assertGreater(stats['recovery_work'],50000)
        self.assertLess(stats['work']-stats['recovery_work'],50000)
        self.assertTrue(verify_group_certificate(d,c,compressed=True,max_work=2000000))
        for options in ({'max_work':50000,'post_recovery_work':50000},{'max_work':2000000,'post_recovery_work':0}):
            with self.assertRaises(GroupLimit):compressed_certificate(d,elimination_batch=True,**options)
        for bad in (True,-1,'bad'):
            with self.assertRaises(ValueError):compressed_certificate(d,post_recovery_work=bad)
        result=group_decide(d,elimination_batch=True,max_work=2000000,seconds=None)
        self.assertEqual(result['status'],'UNKNOT');self.assertNotIn('elimination_fallback',result['search_stats'])
        self.assertEqual(result['certificate'],c)

    def test_accounted_search_failure_deducts_actual_work_and_recovery_failure_reserves_quota(self):
        d=Diagram.from_braid(5,[1,2,3,4])
        for recovered in (False,True):
            calls=[]
            def producer(source,**options):
                calls.append(options.copy())
                if options.get('elimination_batch'):
                    options['stats']['work']=51001
                    if recovered:options['stats']['recovery_work']=1000
                    raise GroupLimit('test phase limit')
                return compressed_certificate(source,**options)
            with patch('fastunknot.compressed_search.compressed_certificate',side_effect=producer):
                result=group_decide(d,elimination_batch=True,max_work=2000000,seconds=None)
            self.assertEqual(calls[0]['max_work'],500000);self.assertEqual(calls[0]['post_recovery_work'],50000)
            charged=51001 if recovered else 500000
            self.assertEqual(calls[1]['max_work'],2000000-charged)
            self.assertEqual(result['search_stats']['elimination_probe']['charged_work'],charged)
            self.assertEqual(result['status'],'UNKNOT')
