"""Exact greedy selection and independently checked persistent production."""
from copy import deepcopy
import random
import unittest
from unittest.mock import patch

from fastunknot import Diagram
from fastunknot.compressed_words import WordArena, CompressedLimit
from fastunknot.compressed_search import compressed_certificate
from fastunknot.elimination_batch import plan_batch, apply_batch
from fastunknot.elimination_batch_verify import replay_literal_batch
from fastunknot.persistent_elimination import _Block, produce_block
from fastunknot.persistent_elimination_verify import replay_compressed_block
from fastunknot.group_certificate import _Budget, verify_group_certificate
from test_persistent_elimination import doubling

PD=[[0,1,2,3],[4,2,5,6],[6,7,8,9],[1,10,11,5],[7,11,12,13],
    [8,13,14,15],[16,17,18,9],[12,19,4,18],[15,14,20,21],
    [21,20,17,16],[10,0,3,19]]


def expand(block, root):
    pending=[root];out=[]
    while pending:
        h=pending.pop()
        if not h:continue
        rule=block.rules[abs(h)];sign=1 if h>0 else -1
        if rule[0]=='t':
            if rule[1] in block.bindings:pending.append(sign*block.bindings[rule[1]])
            else:out.append(sign*rule[1])
        elif sign>0:pending.extend((rule[2],rule[1]))
        else:pending.extend((-rule[1],-rule[2]))
        if len(out)>100000:raise AssertionError('test literal allowance exceeded')
    return out


class PersistentProducerTests(unittest.TestCase):
    def test_random_greedy_rounds_match_old_words_counts_and_selection(self):
        rng=random.Random(261009436);rounds=0
        for _ in range(350):
            rank=rng.randrange(4,10)
            words=[[rng.choice((-1,1))*rng.randrange(1,rank+1) for _ in range(rng.randrange(8))]
                   for _ in range(rng.randrange(2,rank+3))]
            a=WordArena(max_work=10000000);roots=[a.from_word(w) for w in words];alive=set(range(1,rank+1))
            b=WordArena(max_work=10000000);rr=[b.from_word(w) for w in words];block=_Block(b,rr,alive)
            literal=deepcopy(words);ll=set(alive);cache={}
            while len(alive)>=3:
                old=plan_batch(a,roots,alive,cache,ordered=True);new=block.plan()
                self.assertEqual(new,old)
                lengths,_,_,counts=block.summarize()
                self.assertEqual([lengths[abs(r)] for r in block.roots],[a.lengths[r] for r in roots])
                self.assertEqual({g:n for g,n in counts.items() if n},{g:n for g,n in a.summarize(roots)[0].items() if n})
                if len(old)<2:break
                evidence=dict(kind='elimination_batch',entries=old)
                self.assertTrue(replay_literal_batch(literal,ll,evidence,_Budget(lambda:None,1000000,10000000)))
                apply_batch(a,roots,alive,old);block.apply(new);rounds+=1
                self.assertEqual([expand(block,r) for r in block.roots],literal)
                self.assertEqual([a.expand(r) for r in roots],literal);self.assertEqual(block.alive,alive)
            result=block.export();self.assertEqual([b.expand(r) for r in result],literal)
        self.assertGreater(rounds,250)

    def test_binary_counts_cache_invalidation_and_independent_replay(self):
        a=WordArena(max_nodes=300000,max_work=30000000);roots=[];previous=1;trace=[]
        for g in range(3,19):
            body=a.power(a.from_word([previous,1,-previous,2]),1<<128)
            roots.append(a.concat(a.letter(-g),body));previous=g
        roots.extend((a.letter(previous),a.letter(-previous)))
        original=roots[:];alive=set(range(1,19));block=_Block(a,roots,alive)
        for g in range(3,19):
            selected=[dict(relation=g-3,generator=g)]
            block.apply(selected);trace.append(dict(kind='elimination_batch',entries=selected))
            values=block.summarize();self.assertIs(values,block.summarize())
        expected=1
        for _ in range(16):expected=(2*expected+2)*(1<<128)
        self.assertEqual(values[0][abs(block.roots[-1])],expected)
        with patch.object(a,'inverse',side_effect=AssertionError),patch.object(a,'reduce',side_effect=AssertionError),patch.object(a,'equal',side_effect=AssertionError),patch.object(a,'expand',side_effect=AssertionError):
            exported=block.export()
            rr=original[:];ll=set(alive)
            self.assertTrue(replay_compressed_block(a,rr,ll,trace))
        self.assertEqual([a.lengths[r] for r in exported],[a.lengths[r] for r in rr])
        self.assertEqual(ll,block.alive)

    def test_block_stall_publication_and_resource_failures(self):
        words,_=doubling(8)
        def build():
            a=WordArena(max_work=10000000);r=[a.from_word(w) for w in words];alive=set(range(1,13))
            return a,r,alive,plan_batch(a,r,alive,ordered=True)
        a,roots,alive,first=build();moves=[]
        self.assertTrue(produce_block(a,roots,alive,moves,first))
        self.assertEqual(plan_batch(a,roots,alive,ordered=True),[])
        self.assertEqual(len(moves),1)
        for budget in (0,20,200):
            a,roots,alive,first=build();original=roots[:];moves=[];a.left=budget
            with self.assertRaises(CompressedLimit):produce_block(a,roots,alive,moves,first)
            self.assertEqual(roots,original);self.assertEqual(alive,set(range(1,13)));self.assertEqual(moves,[])
        a,roots,alive,first=build();original=roots[:];a.max_nodes=len(a.rules)+3
        with self.assertRaises(CompressedLimit):produce_block(a,roots,alive,[],first)
        self.assertEqual(roots,original);self.assertEqual(alive,set(range(1,13)))
        class Cancel:
            def __bool__(self):return False
            def __call__(self):raise RuntimeError('producer cancellation')
        a,roots,alive,first=build();a.check=Cancel()
        with self.assertRaisesRegex(RuntimeError,'producer cancellation'):produce_block(a,roots,alive,[],first)

    def test_terminal_batch_fast_path_and_native_multibatch_source(self):
        with patch('fastunknot.persistent_elimination.produce_block',side_effect=AssertionError):
            for n in (4,16,64):
                d=Diagram.from_braid(n+1,list(range(1,n+1)));stats={}
                c=compressed_certificate(d,elimination_batch=True,stats=stats)
                self.assertEqual(len(c['moves']),1);self.assertNotIn('persistent_search_blocks',stats)
                self.assertTrue(verify_group_certificate(d,c,compressed=True))
        d=Diagram.from_pd(PD);stats={}
        c=compressed_certificate(d,elimination_batch=True,relator_moves=True,stats=stats)
        self.assertEqual(stats['persistent_search_blocks'],1)
        self.assertEqual(stats['persistent_search_batches'],2)
        self.assertEqual([m['kind'] for m in c['moves']],['elimination_batch','elimination_batch','normalize_relators'])
        for compressed in (False,True):
            with patch('fastunknot.persistent_elimination.produce_block',side_effect=AssertionError):
                self.assertTrue(verify_group_certificate(d,c,compressed=compressed))


if __name__=='__main__':unittest.main()
