"""Rank witnesses preserve v8 compatibility and avoid per-pivot grammar scans."""
from copy import deepcopy
import unittest
from unittest.mock import patch
from fastunknot.compressed_words import WordArena, CompressedLimit
from fastunknot.elimination_batch import plan_batch
from fastunknot.elimination_batch_verify import replay_compressed_batch
from fastunknot.compressed_search import compressed_certificate
from fastunknot import Diagram
from fastunknot.group_certificate import verify_group_certificate


def state(words):
    a=WordArena();return a,[a.from_word(w) for w in words],{abs(x) for w in words for x in w}


def move(*pairs):
    return dict(kind='elimination_batch',entries=[dict(relation=i,generator=g) for i,g in pairs])


class OrderedBatchTests(unittest.TestCase):
    def test_noncommuting_arbitrary_labels_and_legacy_reverse_order(self):
        words=[[9,-5,8],[5,9,5,-2,-8],[2,8,-2,-9],[2,5,-9,-5,-2,8]]
        outputs=[]
        for evidence in (move((0,5),(1,2)),move((1,2),(0,5))):
            a,roots,alive=state(words)
            self.assertTrue(replay_compressed_batch(a,roots,alive,evidence))
            outputs.append([a.expand(r) for r in roots]);self.assertEqual(alive,{8,9})
            self.assertEqual(a.stats.get('elimination_ordered_replays',0),int(evidence['entries'][0]['generator']==5))
            self.assertEqual(a.stats.get('elimination_ordered_fallbacks',0),int(evidence['entries'][0]['generator']==2))
        self.assertEqual(*outputs)

    def test_ordered_replay_needs_no_occurrence_support_inverse_or_normalization(self):
        a,roots,alive=state([[1,-2],[1,2,-1,-3],[3,-1]])
        forbidden=('occurrence','singletons','summarize','inverse','reduce','cyclic_reduce','equal','expand')
        from contextlib import ExitStack
        with ExitStack() as stack:
            for name in forbidden:stack.enter_context(patch.object(a,name,side_effect=AssertionError(name)))
            stack.enter_context(patch('fastunknot.elimination_batch.plan_batch',side_effect=AssertionError))
            self.assertTrue(replay_compressed_batch(a,roots,alive,move((0,2),(1,3))))
        self.assertEqual([a.expand(r) for r in roots],[[],[],[1,1,-1,-1]])

    def test_shared_source_is_summarized_once_and_rank_counts_are_literal(self):
        a=WordArena(max_work=10000000);body=a.power(a.from_word([1,2]),1<<1024)
        roots=[a.concat(a.letter(-g),body) for g in range(3,67)]+[a.from_word([3,-66])]
        M=len(a._reachable(roots));N=len(a.rules)-1
        self.assertTrue(replay_compressed_batch(a,roots,set(range(1,67)),move(*[(g-3,g) for g in range(3,67)])))
        self.assertEqual(a.stats['elimination_ordered_nodes'],M)
        self.assertEqual(a.lengths[roots[-1]],4<<1024)
        self.assertLessEqual(len(a.rules)-1-N,5*M)
        for word in ([3,-3,3,1],[3,-3,1],[1,2]):
            b,rr,ll=state([word,[3,2,1]]);original=rr[:]
            self.assertFalse(replay_compressed_batch(b,rr,ll,move((0,3))))
            self.assertEqual(rr,original)

    def test_cycles_in_unreferenced_definitions_and_dead_source_letters_reject(self):
        for words,live,evidence in (([[1,-2],[2,-1],[3]],{1,2,3},move((0,1),(1,2))),
                                    ([[1,-2],[9]],{1,2,3},move((0,2)))):
            a=WordArena();roots=[a.from_word(w) for w in words];before=roots[:];alive=set(live)
            self.assertFalse(replay_compressed_batch(a,roots,alive,evidence))
            self.assertEqual(roots,before);self.assertEqual(alive,live)

    def test_ordering_preserves_planner_selection_and_new_source_proofs_use_it(self):
        words=[[g,-g-1] for g in range(1,40)]+[[40,-1]]
        a,roots,alive=state(words);alive.add(41)
        plain=plan_batch(a,roots,alive);ordered=plan_batch(a,roots,alive,ordered=True)
        self.assertCountEqual(plain,ordered)
        self.assertTrue(replay_compressed_batch(a,roots,alive,dict(kind='elimination_batch',entries=ordered)))
        self.assertEqual(a.stats['elimination_ordered_replays'],1)
        d=Diagram.from_braid(65,list(range(1,65)));c=compressed_certificate(d,elimination_batch=True)
        stats={};self.assertTrue(verify_group_certificate(d,c,compressed=True,stats=stats))
        self.assertEqual(stats['elimination_ordered_replays'],1)
        self.assertTrue(verify_group_certificate(d,c,compressed=False))
        bad=deepcopy(c);bad['moves'][0]['entries'].reverse()
        self.assertTrue(verify_group_certificate(d,bad,compressed=True))

    def test_interrupted_summary_context_and_compile_leave_state_unpublished(self):
        words=[[1,-3,2],[3,1,-4,2],[4,-1]];evidence=move((0,3),(1,4))
        for allowance in (0,15,30,50,75):
            a,roots,alive=state(words);original=roots[:];live=alive.copy();a.left=allowance
            try:result=replay_compressed_batch(a,roots,alive,evidence)
            except CompressedLimit:
                self.assertEqual(roots,original);self.assertEqual(alive,live)
            else:self.assertTrue(result)
        a,roots,alive=state(words)
        def cancel():raise RuntimeError('cancel ordered replay')
        a.check=cancel
        with self.assertRaisesRegex(RuntimeError,'cancel ordered'):replay_compressed_batch(a,roots,alive,evidence)
