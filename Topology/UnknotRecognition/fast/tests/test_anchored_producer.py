"""Exact greedy discovery, priority boundaries and source-bound independent replay."""
from copy import deepcopy
import random
import unittest
from unittest.mock import patch
from fastunknot import Diagram
from fastunknot.anchored_projection import _SourceSearch, produce_block
from fastunknot.compressed_words import WordArena, CompressedLimit
from fastunknot.compressed_search import compressed_certificate, _search
from fastunknot.primitive_projection import projection_candidates, plan_projection, apply_projection
from fastunknot.primitive_forest import plan_forest, apply_forest
from fastunknot.elimination_batch import plan_batch
from fastunknot.group_certificate import verify_group_certificate
from test_primitive_projection import balanced


def first_move(a,roots,alive,forest):
    prepared=projection_candidates(a,roots,alive);cache={}
    if forest and len(prepared[0])>=2:
        edges=plan_forest(a,roots,alive,cache,_prepared=prepared)
        if len(edges)>=2:return dict(kind='primitive_forest',edges=edges)
    pairs=plan_projection(a,roots,alive,cache,_prepared=prepared)
    return dict(kind='primitive_projection',pairs=pairs) if pairs else None


def apply(a,roots,alive,move):
    if move['kind']=='primitive_forest':apply_forest(a,roots,alive,move['edges'])
    else:apply_projection(a,roots,alive,move['pairs'])


class AnchoredProducerTests(unittest.TestCase):
    def test_greedy_plans_and_singleton_priority_match_chained_words(self):
        rng=random.Random(261009453)
        for trial in range(240):
            labels=rng.sample(range(1,40),rng.randrange(4,10));words=[]
            for i,child in enumerate(labels[1:],1):
                parent=rng.choice(labels[:i]);k=rng.choice((-3,-2,-1,1,2,3))
                word=[parent if k>0 else -parent]*abs(k)+[child]
                words.append(word*rng.randrange(1,4))
            words += [[rng.choice(labels)*rng.choice((-1,1)) for _ in range(rng.randrange(0,14))] for _ in range(4)]
            rng.shuffle(words);a=WordArena(max_work=20000000);roots=[a.from_word(w) for w in words];alive=set(labels)
            state=_SourceSearch(a,roots,alive)
            for step in range(10):
                self.assertEqual(state.elimination(),plan_batch(a,roots,alive,ordered=True))
                forest=(trial+step)%2==0;move=first_move(a,roots,alive,forest)
                self.assertEqual(state.plan(forest),move)
                if move is None:break
                state.apply(move);apply(a,roots,alive,move)
                self.assertEqual(state.alive,alive)
                self.assertEqual([a.expand(r) for r in state.export()],[a.expand(r) for r in roots])
                if len(alive)<=1:break

    def test_complete_large_block_discovery_without_word_or_checker_helpers(self):
        for depth,bits,forest in ((5,128,False),(5,128,True),(4,512,False)):
            a,roots,alive=balanced(depth,bits);first=first_move(a,roots,alive,forest);expected=[]
            while first is not None:
                expected.append(first);apply(a,roots,alive,first)
                if len(alive)<=2:break
                first=first_move(a,roots,alive,forest)
            b,rr,ll=balanced(depth,bits);first=first_move(b,rr,ll,forest);moves=[]
            with patch.object(b,'expand',side_effect=AssertionError),patch.object(b,'reduce',side_effect=AssertionError), \
                 patch.object(b,'inverse',side_effect=AssertionError),patch.object(b,'slice',side_effect=AssertionError), \
                 patch.object(b,'substitute',side_effect=AssertionError),patch.object(b,'equal',side_effect=AssertionError), \
                 patch('fastunknot.anchored_projection_verify._SourceReplay',side_effect=AssertionError):
                produce_block(b,rr,ll,moves,first,forest=forest)
            self.assertEqual(moves,expected);self.assertEqual(ll,alive)
            self.assertEqual([b.lengths[r] for r in rr],[a.lengths[r] for r in roots])
            self.assertLessEqual(len(b.rules),len(a.rules))

    def test_limits_do_not_publish_partial_state_or_trace(self):
        for limit in (0,20,300):
            a,roots,alive=balanced(4,64);first=first_move(a,roots,alive,False);before=roots[:];labels=set(alive);moves=[dict(kind='prefix')];a.left=limit
            with self.assertRaises(CompressedLimit):produce_block(a,roots,alive,moves,first)
            self.assertEqual(roots,before);self.assertEqual(alive,labels);self.assertEqual(moves,[dict(kind='prefix')])
        a,roots,alive=balanced(4,64);first=first_move(a,roots,alive,False);before=roots[:];labels=set(alive);moves=[];a.max_nodes=len(a.rules)-1
        with self.assertRaises(CompressedLimit):produce_block(a,roots,alive,moves,first)
        self.assertEqual(roots,before);self.assertEqual(alive,labels);self.assertFalse(moves)
        class Cancel:
            def __bool__(self):return False
            def __call__(self):raise RuntimeError('cancel producer')
        a,roots,alive=balanced(4,64);first=first_move(a,roots,alive,False);before=roots[:];a.check=Cancel();moves=[]
        with self.assertRaisesRegex(RuntimeError,'cancel producer'):produce_block(a,roots,alive,moves,first)
        self.assertEqual(roots,before);self.assertFalse(moves)

    def test_dispatch_uses_direct_unit_images_and_anchors_binary_growth(self):
        for bits in (0,64):
            a,roots,alive=balanced(5,bits);moves=[];terminal={}
            if bits==0:
                with patch('fastunknot.anchored_projection._SourceSearch',side_effect=AssertionError):
                    self.assertTrue(_search(a,roots,alive,moves,primitive_projection=True,
                                           primitive_terminal=terminal,rank_two_terminal=False))
                self.assertNotIn('anchored_search_blocks',a.stats)
            else:
                self.assertTrue(_search(a,roots,alive,moves,primitive_projection=True,
                                       primitive_terminal=terminal,rank_two_terminal=False))
                self.assertGreater(a.stats['anchored_search_rounds'],1)
            self.assertEqual(terminal['kind'],'rank_one_exponent_zero')

    def test_full_sources_and_independent_checkers(self):
        for n in (9,17,33):
            d=Diagram.from_braid(n,list(range(1,n)))
            for options in (dict(primitive_projection=True,primitive_power=False),dict(primitive_forest=True),
                            dict(primitive_projection=True,elimination_batch=True)):
                with patch('fastunknot.anchored_projection_verify._SourceReplay',side_effect=AssertionError):
                    cert=compressed_certificate(d,max_work=20000000,**options)
                self.assertIsNotNone(cert)
                with patch('fastunknot.anchored_projection._SourceSearch',side_effect=AssertionError):
                    for compressed in (False,True):self.assertTrue(verify_group_certificate(d,cert,compressed=compressed,max_work=20000000))
                other=Diagram.from_braid(2,[1,1,1]);bad=deepcopy(cert);bad['input_pd']=[list(row) for row in other.pd]
                self.assertFalse(verify_group_certificate(other,bad,compressed=True))
