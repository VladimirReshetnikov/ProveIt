"""Source-anchored monomial replay against literal and chained arithmetic."""
from copy import deepcopy
import random
import unittest
from unittest.mock import patch
from fastunknot import Diagram
from fastunknot.anchored_projection_verify import replay_compressed_monomial_block
from fastunknot.compressed_words import WordArena, CompressedLimit
from fastunknot.compressed_search import compressed_certificate
from fastunknot.primitive_projection import plan_projection, apply_projection
from fastunknot.primitive_forest import plan_forest, apply_forest
from fastunknot.primitive_projection_verify import replay_compressed_projection, replay_literal_projection, verify_compressed_rank_one
from fastunknot.primitive_forest_verify import replay_compressed_forest, replay_literal_forest
from fastunknot.group_certificate import _Budget, verify_group_certificate
from test_primitive_projection import balanced, inflated_source


def setup(words, **options):
    a=WordArena(**options)
    return a,[a.from_word(w) for w in words]


def schedule(words,labels):
    a,roots=setup(words);alive=set(labels);moves=[]
    while len(alive)>1:
        if len(moves)%2:
            edges=plan_forest(a,roots,alive)[:2]
            if not edges:break
            moves.append(dict(kind='primitive_forest',edges=edges));apply_forest(a,roots,alive,edges)
        else:
            pairs=plan_projection(a,roots,alive)[:1]
            if not pairs:break
            moves.append(dict(kind='primitive_projection',pairs=pairs));apply_projection(a,roots,alive,pairs)
    return moves


class AnchoredProjectionTests(unittest.TestCase):
    def test_mixed_signed_blocks_match_literal_and_chained_replay(self):
        rng=random.Random(261009449)
        for _ in range(120):
            labels=rng.sample(range(1,60),7);words=[]
            for i,child in enumerate(labels[1:],1):
                parent=rng.choice(labels[:i]);power=rng.choice((-3,-2,-1,1,2,3));sign=rng.choice((-1,1))
                word=[parent*(-1 if power*sign>0 else 1)]*abs(power)+[child*sign]
                words.append(word*rng.randrange(1,4))
            rng.shuffle(words)
            words += [[],[rng.choice(labels)*rng.choice((-1,1)) for _ in range(12)]]
            moves=schedule(words,labels);self.assertGreaterEqual(len(moves),2)
            literal=deepcopy(words);expected_alive=set(labels)
            old,rr=setup(words);old_alive=set(labels)
            for move in moves:
                forest=move['kind']=='primitive_forest'
                self.assertTrue((replay_literal_forest if forest else replay_literal_projection)(
                    literal,expected_alive,move,_Budget(lambda:None,1000000,20000000)))
                self.assertTrue((replay_compressed_forest if forest else replay_compressed_projection)(old,rr,old_alive,move))
            a,roots=setup(words);alive=set(labels)
            with patch('fastunknot.primitive_projection.plan_projection',side_effect=AssertionError), \
                 patch('fastunknot.primitive_forest.apply_forest',side_effect=AssertionError):
                self.assertTrue(replay_compressed_monomial_block(a,roots,alive,moves))
            self.assertEqual([a.expand(r) for r in roots],literal)
            self.assertEqual([old.expand(r) for r in rr],literal)
            self.assertEqual(alive,expected_alive);self.assertEqual(alive,old_alive)

    def test_binary_powers_nonunit_pairs_and_no_word_helpers(self):
        for depth,bits in ((3,128),(5,64)):
            a,roots,alive=balanced(depth,bits);moves=[]
            while len(alive)>1:
                pairs=plan_projection(a,roots,alive);self.assertTrue(pairs)
                moves.append(dict(kind='primitive_projection',pairs=pairs));apply_projection(a,roots,alive,pairs)
            b,rr,ll=balanced(depth,bits)
            with patch.object(b,'expand',side_effect=AssertionError),patch.object(b,'reduce',side_effect=AssertionError), \
                 patch.object(b,'equal',side_effect=AssertionError),patch.object(b,'inverse',side_effect=AssertionError), \
                 patch.object(b,'slice',side_effect=AssertionError),patch.object(b,'substitute',side_effect=AssertionError):
                self.assertTrue(replay_compressed_monomial_block(b,rr,ll,moves))
                self.assertTrue(verify_compressed_rank_one(b,rr,ll,dict(kind='rank_one_exponent_zero',generator=next(iter(ll)))))
            self.assertEqual([a.lengths[r] for r in roots],[b.lengths[r] for r in rr])
            limited,lr,la=balanced(depth,bits);original=lr[:];original_alive=set(la)
            limited.max_nodes=len(limited.rules)-1
            with self.assertRaises(CompressedLimit):
                replay_compressed_monomial_block(limited,lr,la,moves)
            self.assertEqual(lr,original);self.assertEqual(la,original_alive)
        # A nonunit primitive vector followed by a supported second projection.
        words=[[1,2,1,2,2], [3,4,3,4,4], [1,3], [2,-4]]
        moves=schedule(words,{1,2,3,4});self.assertGreaterEqual(len(moves),2)
        a,roots=setup(words);alive={1,2,3,4}
        self.assertTrue(replay_compressed_monomial_block(a,roots,alive,moves))
        expected=deepcopy(words);la={1,2,3,4}
        for move in moves:
            fn=replay_literal_forest if move['kind']=='primitive_forest' else replay_literal_projection
            self.assertTrue(fn(expected,la,move,_Budget(lambda:None,100000,1000000)))
        self.assertEqual([a.expand(r) for r in roots],expected)

    def test_malformed_later_move_and_resource_limits_are_atomic(self):
        words=[[1,-2],[2,-3],[3,-4],[4,-5],[1,-5]];labels=set(range(1,6));moves=schedule(words,labels)
        bads=[]
        for field,value in (('exponent',2),('width',True),('relation',True),('generators',[1,1]),('primitive_vector',[0,1])):
            bad=deepcopy(moves)
            proof=bad[1]['edges'][0]['proof'];proof[field]=value;bads.append(bad)
        bad=deepcopy(moves);bad[1]['edges'][0]['child']=True;bads.append(bad)
        bads += [moves[:1]+[moves[0]],moves[:1]+[None],moves[:1]+[dict(kind=[],edges=[])]]
        for bad in bads:
            a,roots=setup(words);original=roots[:];alive=set(labels);n=len(a.rules)
            self.assertFalse(replay_compressed_monomial_block(a,roots,alive,bad))
            self.assertEqual(roots,original);self.assertEqual(alive,labels);self.assertEqual(len(a.rules),n)
        for allowance in (0,20,100):
            a,roots=setup(words);original=roots[:];alive=set(labels);a.left=allowance
            with self.assertRaises(CompressedLimit):replay_compressed_monomial_block(a,roots,alive,moves)
            self.assertEqual(roots,original);self.assertEqual(alive,labels)
        class Cancel:
            def __bool__(self):return False
            def __call__(self):raise RuntimeError('cancel anchored')
        a,roots=setup(words);original=roots[:];a.check=Cancel();alive=set(labels)
        with self.assertRaisesRegex(RuntimeError,'cancel anchored'):
            replay_compressed_monomial_block(a,roots,alive,moves)
        self.assertEqual(roots,original);self.assertEqual(alive,labels)

    def test_complete_pd_source_schemas_and_normalization_boundaries(self):
        d=Diagram.from_braid(17,list(range(1,17)))
        cert=compressed_certificate(d,primitive_projection=True,primitive_power=False)
        stats={}
        with patch('fastunknot.primitive_projection.plan_projection',side_effect=AssertionError), \
             patch('fastunknot.primitive_projection.apply_projection',side_effect=AssertionError), \
             patch('fastunknot.primitive_projection_verify.replay_compressed_projection',wraps=replay_compressed_projection) as single:
            self.assertTrue(verify_group_certificate(d,cert,compressed=True,stats=stats))
        self.assertEqual(stats['anchored_replay_blocks'],7)
        self.assertEqual(single.call_count,1)
        self.assertTrue(verify_group_certificate(d,cert,compressed=False))
        mixed=deepcopy(cert);mixed['version']=7
        mixed['moves'][1]=dict(kind='primitive_forest',edges=[dict(child=p['generators'][1],proof=p)
                                                           for p in mixed['moves'][1]['pairs']])
        for compressed in (False,True):
            self.assertTrue(verify_group_certificate(d,mixed,compressed=compressed))
        mixed['version']=6
        self.assertFalse(verify_group_certificate(d,mixed,compressed=True))
        bad=deepcopy(cert);bad['version']=5
        self.assertFalse(verify_group_certificate(d,bad,compressed=True))
        bad=deepcopy(cert);bad['moves'].append(dict(kind=[]))
        self.assertFalse(verify_group_certificate(d,bad,compressed=True))
        other=Diagram.from_braid(2,[1,1,1]);bad=deepcopy(cert);bad['input_pd']=[list(r) for r in other.pd]
        self.assertFalse(verify_group_certificate(other,bad,compressed=True))
        for bits in (4,128):
            d,cert=inflated_source(bits)
            self.assertTrue(verify_group_certificate(d,cert,compressed=True,max_work=20000000))
            bad=deepcopy(cert);bad['moves']=[m for m in bad['moves'] if m['kind']!='normalize_relators']
            self.assertFalse(verify_group_certificate(d,bad,compressed=True,max_work=20000000))
