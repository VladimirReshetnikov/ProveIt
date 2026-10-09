"""Acyclic overlap batches, independent replay and source-bound version seven."""
from copy import deepcopy
import json
from pathlib import Path
import random
import subprocess
import sys
import unittest
from unittest.mock import patch

from fastunknot import Diagram, recognize
from fastunknot.compressed_words import WordArena, CompressedLimit
from fastunknot.compressed_search import _search, compressed_certificate
from fastunknot.primitive_forest import plan_forest, apply_forest
from fastunknot.primitive_forest_verify import replay_compressed_forest, replay_literal_forest
from fastunknot.primitive_projection_verify import verify_compressed_rank_one
from fastunknot.group_certificate import _Budget, verify_group_certificate, group_decide, GroupLimit
from test_primitive_projection import balanced

ROOT=Path(__file__).resolve().parents[1]


def family(rank,bits,shape='star'):
    arena=WordArena(max_work=20000000);roots=[];alive=set(range(1,rank+1))
    for child in range(2,rank+1):
        parent=1 if shape=='star' else child-1
        w=arena.concat(arena.power(arena.letter(parent),1<<bits),arena.letter(child))
        roots.extend((arena.power(w,2),arena.power(w,3)))
    return arena,roots,alive


class PrimitiveForestTests(unittest.TestCase):
    def test_random_signed_trees_and_every_retained_relator(self):
        rng=random.Random(261008506)
        for _ in range(100):
            labels=rng.sample(range(1,50),6);words=[]
            for i,child in enumerate(labels[1:],1):
                parent=rng.choice(labels[:i]);power=rng.choice((-3,-2,-1,1,2,3));sign=rng.choice((-1,1))
                word=[parent*(-1 if power*sign>0 else 1)]*abs(power)+[child*sign]
                words.append(word*rng.randrange(1,4))
            rng.shuffle(words);words += [[rng.choice(labels)*rng.choice((-1,1)) for _ in range(12)] for _ in range(3)]
            a=WordArena();roots=[a.from_word(w) for w in words];alive=set(labels)
            edges=plan_forest(a,roots,alive);self.assertTrue(edges);move=dict(kind='primitive_forest',edges=edges)
            b=WordArena();rr=[b.from_word(w) for w in words];ll=set(alive)
            literal=deepcopy(words);la=set(alive)
            self.assertTrue(replay_compressed_forest(b,rr,ll,move))
            self.assertTrue(replay_literal_forest(literal,la,move,_Budget(lambda:None,1000000,5000000)))
            apply_forest(a,roots,alive,edges)
            self.assertEqual([a.expand(r) for r in roots],[b.expand(r) for r in rr])
            self.assertEqual([list(a.expand(r)) for r in roots],literal)
            self.assertEqual(alive,ll);self.assertEqual(alive,la);self.assertEqual(len(roots),len(words))

    def test_star_chain_and_balanced_capacity_without_normalization(self):
        fixtures=[family(64,128,'star'),family(64,128,'chain'),balanced(6,64)]
        for a,roots,alive in fixtures:
            initial_rank=len(alive);original_slots=len(roots);edges=plan_forest(a,roots,alive)
            self.assertEqual(len(edges),initial_rank-1)
            with patch.object(a,'reduce',side_effect=AssertionError),patch.object(a,'cyclic_reduce',side_effect=AssertionError),patch.object(a,'expand',side_effect=AssertionError),patch.object(a,'equal',side_effect=AssertionError):
                apply_forest(a,roots,alive,edges)
                self.assertTrue(verify_compressed_rank_one(a,roots,alive,dict(kind='rank_one_exponent_zero',generator=next(iter(alive)))))
            self.assertEqual(len(roots),original_slots);self.assertTrue(any(roots));self.assertEqual(a.stats['forest_rounds'],1)
        a,roots,alive=family(9,128,'chain');moves=[];terminal={}
        self.assertTrue(_search(a,roots,alive,moves,primitive_terminal=terminal,primitive_forest=True))
        self.assertEqual(len(moves),1);self.assertEqual(moves[0]['kind'],'primitive_forest')
        b,rr,ll=family(9,128,'chain')
        with patch.object(b,'reduce',side_effect=AssertionError),patch.object(b,'cyclic_reduce',side_effect=AssertionError),patch.object(b,'expand',side_effect=AssertionError),patch.object(b,'equal',side_effect=AssertionError):
            self.assertTrue(replay_compressed_forest(b,rr,ll,moves[0]));self.assertTrue(verify_compressed_rank_one(b,rr,ll,terminal))

    def test_cycle_duplicate_child_slot_and_nonunit_forgeries(self):
        words=[[1,-2],[2,-3],[3,-1],[4,5,4,5,5],[1,4]];a=WordArena();roots=[a.from_word(w) for w in words]
        from fastunknot.primitive_power import primitive_power_terminal
        def edge(slot,child):
            pair={abs(x) for x in words[slot]};p=primitive_power_terminal(a,[roots[slot]],pair)
            return dict(child=child,proof=dict(p,relation=slot))
        valid=dict(kind='primitive_forest',edges=[edge(0,2),edge(1,3)])
        mutations=[dict(kind='primitive_forest',edges=[edge(0,1),edge(1,2),edge(2,3)]),
            dict(kind='primitive_forest',edges=[edge(0,2),edge(1,2)]),
            dict(kind='primitive_forest',edges=[edge(0,2),edge(0,1)]),
            dict(kind='primitive_forest',edges=[edge(3,5)]),dict(kind='primitive_forest',edges=[])]
        for key,value in [('child',True),('child',999),('extra',1)]:
            bad=deepcopy(valid);bad['edges'][0][key]=value;mutations.append(bad)
        bad=deepcopy(valid);bad['extra']=True;mutations.append(bad)
        bad=deepcopy(valid);bad['edges'][0]['proof']['exponent']=999;mutations.append(bad)
        for bad in mutations:
            b=WordArena();rr=[b.from_word(w) for w in words];ll=set(range(1,6));original=rr[:]
            self.assertFalse(replay_compressed_forest(b,rr,ll,bad));self.assertEqual(rr,original);self.assertEqual(ll,set(range(1,6)))
            literal=deepcopy(words);self.assertFalse(replay_literal_forest(literal,set(ll),bad,_Budget(lambda:None,1000000,1000000)));self.assertEqual(literal,words)
        # Permutation of checked edges cannot change the simultaneous quotient.
        for edges in (valid['edges'],list(reversed(valid['edges']))):
            b=WordArena();rr=[b.from_word(w) for w in words];ll=set(range(1,6))
            self.assertTrue(replay_compressed_forest(b,rr,ll,dict(kind='primitive_forest',edges=edges)))
            self.assertEqual(ll,{1,4,5})

    def test_producer_skips_general_pairs_and_rejects_cycles(self):
        a=WordArena();roots=[a.from_word(w) for w in ([1,2,1,2,2],[2,3],[3,4],[4,2])]
        edges=plan_forest(a,roots,{1,2,3,4})
        self.assertEqual(len(edges),2);self.assertTrue(all(e['proof']['relation']!=0 for e in edges))
        self.assertTrue(replay_compressed_forest(a,roots,{1,2,3,4},dict(kind='primitive_forest',edges=edges)))

    def test_source_bound_version_seven_and_old_proof_compatibility(self):
        seen=False
        for strands in (5,9,17):
            d=Diagram.from_braid(strands,list(range(1,strands)))
            old=compressed_certificate(d,primitive_projection=True)
            self.assertEqual(old,compressed_certificate(d,primitive_projection=True,primitive_forest=False))
            new=compressed_certificate(d,primitive_forest=True)
            self.assertEqual(new['version'],7);seen=True
            with patch('fastunknot.primitive_forest.plan_forest',side_effect=AssertionError),patch('fastunknot.primitive_forest.apply_forest',side_effect=AssertionError):
                for compressed in (False,True):
                    self.assertTrue(verify_group_certificate(d,new,compressed=compressed));self.assertTrue(verify_group_certificate(d,old,compressed=compressed))
            bad=deepcopy(new);bad['version']=6
            for compressed in (False,True):self.assertFalse(verify_group_certificate(d,bad,compressed=compressed))
            other=Diagram.from_braid(2,[1,1,1]);bad=deepcopy(new);bad['input_pd']=[list(r) for r in other.pd]
            self.assertFalse(verify_group_certificate(other,bad,compressed=True))
        self.assertTrue(seen)

    def test_literal_allocation_limits_and_compressed_work_caps(self):
        words=[[1]*20+[2],[2]*20+[3],[3,-3]];a=WordArena();roots=[a.from_word(w) for w in words]
        move=dict(kind='primitive_forest',edges=plan_forest(a,roots,{1,2,3}))
        with self.assertRaises(GroupLimit):replay_literal_forest(deepcopy(words),{1,2,3},move,_Budget(lambda:None,100,100000))
        with self.assertRaises(GroupLimit):replay_literal_forest(deepcopy(words),{1,2,3},move,_Budget(lambda:None,100000,100))
        a.left=0
        with self.assertRaises(CompressedLimit):replay_compressed_forest(a,roots,{1,2,3},move)

    def test_api_cli_strict_options_and_cancellation(self):
        d=Diagram.from_braid(5,[1,2,3,4])
        for bad in (1,None,'yes'):
            with self.assertRaises(ValueError):compressed_certificate(d,primitive_forest=bad)
            with self.assertRaises(ValueError):group_decide(d,primitive_forest=bad)
            with self.assertRaises(ValueError):recognize(d,group_primitive_forest=bad)
        with self.assertRaises(ValueError):recognize(d,group_primitive_forest=True,group_adaptive=True)
        result=group_decide(d,primitive_forest=True,seconds=None)
        self.assertEqual(result['status'],'UNKNOT');self.assertEqual(result['certificate']['version'],7)
        def cancel():raise ValueError('caller cancellation')
        with self.assertRaisesRegex(ValueError,'caller'):group_decide(d,primitive_forest=True,check=cancel)
        for options in ({'max_work':0},{'max_nodes':0},{'max_letters':0}):self.assertEqual(group_decide(d,primitive_forest=True,**options)['status'],'INCONCLUSIVE')
        run=subprocess.run([sys.executable,'-B','-m','fastunknot','recognize','-','--group-primitive-forest','--group-seconds','2'],input=json.dumps({'pd':d.pd}),text=True,capture_output=True,cwd=ROOT)
        self.assertEqual(run.returncode,0,run.stderr);self.assertEqual(json.loads(run.stdout)['status'],'UNKNOT')
