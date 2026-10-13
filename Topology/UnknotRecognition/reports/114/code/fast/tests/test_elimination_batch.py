"""Nonmonomial acyclic elimination, source replay and strict failure contracts."""
from copy import deepcopy
import json
from pathlib import Path
import random
import subprocess
import sys
import unittest
from unittest.mock import patch

from fastunknot import Diagram, recognize
from fastunknot.compressed_search import compressed_certificate
from fastunknot.compressed_words import WordArena, CompressedLimit
from fastunknot.elimination_batch import plan_batch, apply_batch
from fastunknot.elimination_batch_verify import replay_compressed_batch, replay_literal_batch
from fastunknot.group_certificate import _Budget, GroupLimit, group_decide, verify_group_certificate


def inverse(word):return [-x for x in reversed(word)]


def tower(depth,bits):
    a=WordArena(max_nodes=1000000,max_work=20000000);roots=[];entries=[];previous=1
    for g in range(3,depth+3):
        base=a.from_word([previous,1,-previous,2]);w=a.power(base,1<<bits)
        roots.append(a.concat(a.letter(-g),w));entries.append(dict(relation=len(roots)-1,generator=g));previous=g
    roots.extend((a.letter(previous),0,a.letter(-previous)))
    return a,roots,set(range(1,depth+3)),dict(kind='elimination_batch',entries=entries)


class EliminationBatchTests(unittest.TestCase):
    def test_random_dags_match_literal_homomorphisms_and_both_replayers(self):
        rng=random.Random(261008514)
        for _ in range(100):
            rank=rng.randrange(3,8);words=[];entries=[];images={1:[1],-1:[-1]}
            for g in range(2,rank+1):
                definition=[rng.choice((-1,1))*rng.randrange(1,g) for _ in range(rng.randrange(5))]
                images[g]=sum((images[x] for x in definition),[]);images[-g]=inverse(images[g])
                word=([g]+inverse(definition)) if rng.randrange(2) else ([-g]+definition)
                k=rng.randrange(len(word));word=word[k:]+word[:k]
                entries.append(dict(relation=len(words),generator=g));words.append(word)
            extra=[rng.choice((-1,1))*rng.randrange(1,rank+1) for _ in range(12)]
            words.extend((extra,[],extra));expected=[[] for _ in entries]+[sum((images[x] for x in w),[]) for w in words[len(entries):]]
            rng.shuffle(entries);move=dict(kind='elimination_batch',entries=entries)
            a=WordArena();roots=[a.from_word(w) for w in words];alive=set(range(1,rank+1))
            apply_batch(a,roots,alive,entries)
            self.assertEqual([a.expand(r) for r in roots],expected);self.assertEqual(alive,{1})
            b=WordArena();rr=[b.from_word(w) for w in words];ll=set(range(1,rank+1))
            with patch('fastunknot.elimination_batch.plan_batch',side_effect=AssertionError),patch('fastunknot.elimination_batch.apply_batch',side_effect=AssertionError):
                self.assertTrue(replay_compressed_batch(b,rr,ll,move))
                literal=deepcopy(words);self.assertTrue(replay_literal_batch(literal,set(range(1,rank+1)),move,_Budget(lambda:None,1000000,1000000)))
            self.assertEqual([b.expand(r) for r in rr],expected);self.assertEqual(literal,expected)

    def test_deep_nonmonomial_images_stay_compressed_without_normalization(self):
        for depth,bits in ((8,128),(64,64)):
            a,roots,alive,move=tower(depth,bits);rr=list(roots);ll=set(alive)
            expected=1
            for _ in range(depth):expected=(2*expected+2)*(1<<bits)
            with patch.object(a,'reduce',side_effect=AssertionError),patch.object(a,'cyclic_reduce',side_effect=AssertionError),patch.object(a,'expand',side_effect=AssertionError),patch.object(a,'equal',side_effect=AssertionError):
                apply_batch(a,roots,alive,move['entries'])
                self.assertTrue(replay_compressed_batch(a,rr,ll,move))
            self.assertEqual(roots,rr);self.assertEqual(alive,{1,2});self.assertEqual(ll,alive)
            self.assertEqual(a.lengths[roots[-3]],expected);self.assertEqual(a.lengths[roots[-1]],expected)
            self.assertEqual(a.uniform[roots[-3]],0);self.assertLess(len(a.rules),100000)

    def test_cycles_duplicates_non_singletons_and_strict_types_are_rejected(self):
        words=[[1,-2],[2,-3],[3,-1],[4,4,1],[5,-1]];alive={1,2,3,4,5}
        valid=dict(kind='elimination_batch',entries=[dict(relation=0,generator=2),dict(relation=1,generator=3)])
        invalid=[dict(kind='elimination_batch',entries=[dict(relation=i,generator=i+1) for i in range(3)]),
            dict(kind='elimination_batch',entries=[]),dict(kind='elimination_batch',entries=[dict(relation=3,generator=4)])]
        for key,value in (('relation',True),('relation',-1),('relation',999),('generator',True),('generator',99),('extra',1)):
            bad=deepcopy(valid);bad['entries'][0][key]=value;invalid.append(bad)
        for mutation in ('child','slot','extra'):
            bad=deepcopy(valid)
            if mutation=='child':bad['entries'][1]['generator']=2
            elif mutation=='slot':bad['entries'][1]['relation']=0
            else:bad['extra']=True
            invalid.append(bad)
        for move in invalid:
            a=WordArena();roots=[a.from_word(w) for w in words];original=roots[:];ll=set(alive)
            self.assertFalse(replay_compressed_batch(a,roots,ll,move));self.assertEqual(roots,original);self.assertEqual(ll,alive)
            literal=deepcopy(words);ll=set(alive)
            self.assertFalse(replay_literal_batch(literal,ll,move,_Budget(lambda:None,1000000,1000000)))
            self.assertEqual(literal,words);self.assertEqual(ll,alive)
        for entries in (valid['entries'],list(reversed(valid['entries']))):
            a=WordArena();roots=[a.from_word(w) for w in words]
            self.assertTrue(replay_compressed_batch(a,roots,set(alive),dict(kind='elimination_batch',entries=entries)))

    def test_planner_avoids_cycles_and_rebuilds_slot_and_live_membership(self):
        a=WordArena();roots=[a.from_word(w) for w in ([1,-2],[2,-3],[3,-1],[4,1,-5])];cache={}
        first=plan_batch(a,roots,{1,2,3,4,5},cache)
        self.assertGreaterEqual(len(first),2)
        for rr,ll in ((list(roots),{1,2,3,4,5}),([roots[3],0,roots[0],roots[1],roots[2]],{1,2,3,4,5})):
            entries=plan_batch(a,rr,ll,cache);self.assertTrue(replay_compressed_batch(a,rr,ll,dict(kind='elimination_batch',entries=entries)))
        entries=plan_batch(a,[roots[0],roots[3]],{1,2,3},cache)
        self.assertTrue(all(e['relation']==0 for e in entries))

    def test_actual_source_version_eight_and_rebinding(self):
        for strands in (4,5,9,17):
            d=Diagram.from_braid(strands,list(range(1,strands)))
            old=compressed_certificate(d);self.assertEqual(old,compressed_certificate(d,elimination_batch=False))
            c=compressed_certificate(d,elimination_batch=True)
            self.assertEqual(c['version'],8);self.assertEqual(len(c['moves']),1)
            for compressed in (False,True):
                with patch('fastunknot.elimination_batch.plan_batch',side_effect=AssertionError),patch('fastunknot.elimination_batch.apply_batch',side_effect=AssertionError):
                    self.assertTrue(verify_group_certificate(d,c,compressed=compressed));self.assertTrue(verify_group_certificate(d,old,compressed=compressed))
                bad=deepcopy(c);bad['version']=7;self.assertFalse(verify_group_certificate(d,bad,compressed=compressed))
            other=Diagram.from_braid(2,[1,1,1]);bad=deepcopy(c);bad['input_pd']=[list(r) for r in other.pd]
            self.assertFalse(verify_group_certificate(other,bad,compressed=True))

    def test_literal_expansion_preflight_and_shared_resource_limits(self):
        words=[[-2]+[1]*20,[-3]+[2]*20,[3]]
        move=dict(kind='elimination_batch',entries=[dict(relation=0,generator=2),dict(relation=1,generator=3)])
        literal=deepcopy(words)
        with self.assertRaises(GroupLimit):replay_literal_batch(literal,{1,2,3},move,_Budget(lambda:None,100,1000000))
        self.assertEqual(literal,words)
        for fn in ('plan','apply','replay'):
            a=WordArena();roots=[a.from_word(w) for w in words];a.left=0
            with self.assertRaises(CompressedLimit):
                if fn=='plan':plan_batch(a,roots,{1,2,3})
                elif fn=='apply':apply_batch(a,roots,{1,2,3},move['entries'])
                else:replay_compressed_batch(a,roots,{1,2,3},move)

    def test_options_cli_cancellation_and_budget_outcomes(self):
        d=Diagram.from_braid(5,[1,2,3,4])
        for bad in (1,None,'yes'):
            with self.assertRaises(ValueError):compressed_certificate(d,elimination_batch=bad)
            with self.assertRaises(ValueError):group_decide(d,elimination_batch=bad)
            with self.assertRaises(ValueError):recognize(d,group_elimination_batch=bad)
        with self.assertRaises(ValueError):recognize(d,group_elimination_batch=True,group_adaptive=True)
        def cancel():raise ValueError('caller cancellation')
        with self.assertRaisesRegex(ValueError,'caller'):group_decide(d,elimination_batch=True,check=cancel)
        for options in ({'max_work':0},{'max_nodes':0},{'max_letters':0}):self.assertEqual(group_decide(d,elimination_batch=True,**options)['status'],'INCONCLUSIVE')
        result=group_decide(d,elimination_batch=True,seconds=None)
        self.assertEqual(result['status'],'UNKNOT');self.assertEqual(result['certificate']['version'],8)
        proc=subprocess.run([sys.executable,'-B','-m','fastunknot','recognize','-','--group-elimination-batch','--group-seconds','2'],input=json.dumps({'pd':d.pd}),text=True,capture_output=True,cwd=Path(__file__).resolve().parents[1])
        self.assertEqual(proc.returncode,0,proc.stderr);self.assertEqual(json.loads(proc.stdout)['status'],'UNKNOT')

    def test_host_restarts_original_source_with_remaining_work_after_probe(self):
        d=Diagram.from_braid(5,[1,2,3,4]);calls=[]
        def producer(source,**options):
            calls.append(options.copy())
            if options.get('elimination_batch'):
                options['stats']['work']=123
                raise GroupLimit('synthetic batch stall')
            return compressed_certificate(source,**options)
        with patch('fastunknot.compressed_search.compressed_certificate',side_effect=producer):
            result=group_decide(d,elimination_batch=True,seconds=None,max_work=200000)
        self.assertEqual(result['status'],'UNKNOT');self.assertTrue(result['search_stats']['elimination_fallback'])
        self.assertEqual(calls[0]['max_work'],50000);self.assertEqual(calls[1]['max_work'],150000)
        self.assertNotEqual(result['certificate']['version'],8)
        self.assertEqual(result['search_stats']['elimination_probe']['charged_work'],50000)
        for bad in (True,-1,'bad'):
            with self.assertRaises(ValueError):group_decide(d,elimination_batch=True,max_work=bad)
