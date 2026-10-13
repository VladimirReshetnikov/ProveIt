"""Whole-round source replay, raw grammar growth and explicit normalization."""
from copy import deepcopy
import json
import random
import subprocess
import sys
import unittest
from unittest.mock import patch
from pathlib import Path

from fastunknot import Diagram, recognize
from fastunknot.compressed_words import WordArena, CompressedLimit
from fastunknot.compressed_search import _search, compressed_certificate
from fastunknot.primitive_projection import plan_projection, apply_projection, rank_one_zero
from fastunknot.primitive_projection_verify import (
    replay_compressed_projection, replay_literal_projection,
    verify_compressed_rank_one, verify_literal_rank_one,
)
from fastunknot.group_certificate import _presentation, _Budget, verify_group_certificate, group_decide, GroupLimit
from fastunknot.whitehead_power import powered_images

ROOT=Path(__file__).resolve().parents[1]


def balanced(depth,bits):
    arena=WordArena(max_work=10000000);alive=set(range(1,2**depth+1));roots=[];current=sorted(alive)
    while len(current)>1:
        for a,b in zip(current[::2],current[1::2]):
            w=arena.concat(arena.power(arena.letter(a),1<<bits),arena.letter(b))
            roots.extend((arena.power(w,2),arena.power(w,3)))
        current=current[::2]
    return arena,roots,alive


def inflated_source(bits):
    d=Diagram.from_braid(5,[1,2,3,4]);alive,words=_presentation(d,_Budget(lambda:None,10000,100000))
    arena=WordArena(max_work=10000000);roots=[arena.from_word(w) for w in words];k=1<<bits
    roots=[arena.cyclic_reduce(x) for x in arena.substitute(roots,powered_images(arena,alive,1,{1,2},k))]
    moves=[dict(kind='whitehead_power',multiplier=1,subset=[1,2],exponent=k)];terminal={}
    assert _search(arena,roots,alive,moves,primitive_terminal=terminal,primitive_projection=True)
    return d,dict(version=6,method='wirtinger-cyclic-group',status='UNKNOT',input_pd=[list(r) for r in d.pd],moves=moves,terminal=terminal)


class PrimitiveProjectionTests(unittest.TestCase):
    def test_literal_and_compressed_simultaneous_projection_random_words(self):
        rng=random.Random(261008505)
        for _ in range(120):
            # Two disjoint signed primitive donors plus unrelated relators.
            words=[[1,2,1,2,2],[-3,4,-3,4,4]]
            words += [[rng.choice((-4,-3,-2,-1,1,2,3,4)) for _ in range(rng.randrange(20))] for _ in range(4)]
            a=WordArena();roots=[a.from_word(w) for w in words];alive={1,2,3,4}
            selected=plan_projection(a,roots,alive);self.assertEqual(len(selected),2)
            move=dict(kind='primitive_projection',pairs=selected)
            other=WordArena();other_roots=[other.from_word(w) for w in words];other_alive=set(alive)
            literal=deepcopy(words);literal_alive=set(alive)
            self.assertTrue(replay_compressed_projection(other,other_roots,other_alive,move))
            self.assertTrue(replay_literal_projection(literal,literal_alive,move,_Budget(lambda:None,100000,100000)))
            apply_projection(a,roots,alive,selected)
            self.assertEqual([a.expand(r) for r in roots],[other.expand(r) for r in other_roots])
            self.assertEqual([list(a.expand(r)) for r in roots],literal)
            self.assertEqual(alive,other_alive);self.assertEqual(alive,literal_alive)
            self.assertEqual(len(roots),len(words))

    def test_cached_supports_and_negative_profiles_preserve_original_slots(self):
        a=WordArena();bad=a.from_word([1,1,2,2,2]);good=a.from_word([3,4,3,4,4]);cache={}
        first=plan_projection(a,[0,bad,good,good],{1,2,3,4},cache)
        self.assertEqual([p['relation'] for p in first],[2]);nodes=a.stats['projection_metadata_nodes']
        with patch('fastunknot.primitive_projection.primitive_power_terminal',side_effect=AssertionError):
            second=plan_projection(a,[good,bad,0],{1,2,3,4},cache)
        self.assertEqual(second[0]['relation'],0);self.assertEqual(a.stats['projection_metadata_nodes'],nodes)
        self.assertEqual(first[0]['relation'],2)

    def test_raw_balanced_rounds_never_normalize_and_share_resource_limits(self):
        for depth,bits in ((1,128),(3,512),(6,64)):
            a,roots,alive=balanced(depth,bits);moves=[];terminal={}
            with patch.object(a,'reduce',side_effect=AssertionError),patch.object(a,'cyclic_reduce',side_effect=AssertionError),patch.object(a,'expand',side_effect=AssertionError),patch.object(a,'equal',side_effect=AssertionError):
                self.assertTrue(_search(a,roots,alive,moves,primitive_terminal=terminal,primitive_projection=True,rank_two_terminal=False))
                self.assertTrue(rank_one_zero(a,roots,alive))
                self.assertTrue(verify_compressed_rank_one(a,roots,alive,terminal))
            self.assertEqual(a.stats['projection_rounds'],depth)
            self.assertEqual(a.stats['projection_pairs'],2**depth-1)
            self.assertEqual(len(roots),2*(2**depth-1))
            self.assertTrue(any(roots))  # Raw zero-exponent circuits were retained.
            b,rr,ll=balanced(depth,bits)
            with patch.object(b,'reduce',side_effect=AssertionError),patch.object(b,'expand',side_effect=AssertionError):
                for move in moves:self.assertTrue(replay_compressed_projection(b,rr,ll,move))
                self.assertTrue(verify_compressed_rank_one(b,rr,ll,terminal))
        a,roots,alive=balanced(2,8);a.left=0
        with self.assertRaises(CompressedLimit):plan_projection(a,roots,alive)

    def test_whole_source_rounds_both_replayers_and_normalization_handoff(self):
        for strands in (4,5,9,17):
            d=Diagram.from_braid(strands,list(range(1,strands)))
            c=compressed_certificate(d,primitive_projection=True,primitive_power=False)
            self.assertEqual(c['version'],6);self.assertEqual(c['terminal']['kind'],'rank_one_exponent_zero')
            for compressed in (False,True):self.assertTrue(verify_group_certificate(d,c,compressed=compressed))
        for bits in (4,128):
            d,c=inflated_source(bits)
            self.assertTrue(any(m['kind']=='normalize_relators' for m in c['moves']))
            with patch('fastunknot.primitive_projection.plan_projection',side_effect=AssertionError),patch('fastunknot.primitive_projection.apply_projection',side_effect=AssertionError),patch('fastunknot.primitive_projection.rank_one_zero',side_effect=AssertionError):
                self.assertTrue(verify_group_certificate(d,c,compressed=True,max_work=10000000))
            if bits==4:self.assertTrue(verify_group_certificate(d,c,max_work=10000000))
            else:
                with self.assertRaises(GroupLimit):verify_group_certificate(d,c,max_work=10000)
            bad=deepcopy(c);bad['moves']=[m for m in bad['moves'] if m['kind']!='normalize_relators']
            self.assertFalse(verify_group_certificate(d,bad,compressed=True,max_work=10000000))

    def test_overlap_forgery_missing_donors_slots_and_source_rebinding(self):
        d=Diagram.from_braid(9,list(range(1,9)));c=compressed_certificate(d,primitive_projection=True,primitive_power=False)
        ix=next(i for i,m in enumerate(c['moves']) if m['kind']=='primitive_projection')
        mutations=[]
        bad=deepcopy(c);bad['moves'][ix]['pairs'].append(deepcopy(bad['moves'][ix]['pairs'][0]));mutations.append(bad)
        for key,value in [('relation',True),('relation',999),('generators',[1,1]),('primitive_vector',[1,0]),('exponent',2),('width',True)]:
            bad=deepcopy(c);bad['moves'][ix]['pairs'][0][key]=value;mutations.append(bad)
        bad=deepcopy(c);bad['moves'][ix]['pairs']=[];mutations.append(bad)
        bad=deepcopy(c);bad['moves'][ix]['drop_other_relators']=True;mutations.append(bad)
        bad=deepcopy(c);bad['version']=5;mutations.append(bad)
        bad=deepcopy(c);bad['terminal']['generator']=True;mutations.append(bad)
        bad=deepcopy(c);bad['terminal']['torsion_free']=True;mutations.append(bad)
        for bad in mutations:
            for compressed in (False,True):self.assertFalse(verify_group_certificate(d,bad,compressed=compressed))
        other=Diagram.from_braid(2,[1]*3);bad=deepcopy(c);bad['input_pd']=[list(r) for r in other.pd]
        self.assertFalse(verify_group_certificate(other,bad,compressed=True))

    def test_rank_one_endpoint_checks_every_original_relator(self):
        a=WordArena();roots=[0,a.from_word([1,-1]),a.from_word([1,1,-1])];terminal=dict(kind='rank_one_exponent_zero',generator=1)
        self.assertFalse(rank_one_zero(a,roots,{1}))
        self.assertFalse(verify_compressed_rank_one(a,roots,{1},terminal))
        self.assertFalse(verify_literal_rank_one([[],[1,-1],[1,1,-1]],{1},terminal,_Budget(lambda:None,10000,10000)))
        self.assertFalse(verify_compressed_rank_one(a,[a.letter(2)],{1},terminal))

    def test_api_cli_old_defaults_and_caller_cancellation(self):
        d=Diagram.from_braid(5,[1,2,3,4]);default=compressed_certificate(d)
        self.assertEqual(default,compressed_certificate(d,primitive_projection=False))
        for bad in (1,None,'yes'):
            with self.assertRaises(ValueError):compressed_certificate(d,primitive_projection=bad)
            with self.assertRaises(ValueError):group_decide(d,primitive_projection=bad)
            with self.assertRaises(ValueError):recognize(d,group_primitive_projection=bad)
        with self.assertRaises(ValueError):recognize(d,group_primitive_projection=True,group_adaptive=True)
        result=group_decide(d,primitive_projection=True,seconds=None)
        self.assertEqual(result['status'],'UNKNOT');self.assertEqual(result['certificate']['version'],6)
        def cancel():raise ValueError('external cancellation')
        with self.assertRaisesRegex(ValueError,'external'):group_decide(d,primitive_projection=True,check=cancel)
        for options in ({'max_work':0},{'max_nodes':0},{'max_letters':0}):
            self.assertEqual(group_decide(d,primitive_projection=True,**options)['status'],'INCONCLUSIVE')
        run=subprocess.run([sys.executable,'-B','-m','fastunknot','recognize','-','--group-primitive-projection','--group-seconds','2'],input=json.dumps({'pd':d.pd}),text=True,capture_output=True,cwd=ROOT)
        self.assertEqual(run.returncode,0,run.stderr);self.assertEqual(json.loads(run.stdout)['status'],'UNKNOT')
