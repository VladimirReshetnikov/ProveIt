"""Whole raw blocks, checked against literal substitution and source replay."""
from copy import deepcopy
import math
import random
import unittest
from unittest.mock import patch

from fastunknot import Diagram
from fastunknot.compressed_search import compressed_certificate
from fastunknot.compressed_words import WordArena, CompressedLimit
from fastunknot.elimination_batch_verify import replay_compressed_batch, replay_literal_batch
from fastunknot.group_certificate import _Budget, verify_group_certificate
from fastunknot.persistent_elimination_verify import replay_compressed_block, _ReplayCircuit


def move(entries):
    return dict(kind='elimination_batch', entries=[dict(relation=s, generator=g) for s, g in entries])


def setup(words, **options):
    arena = WordArena(**options)
    return arena, [arena.from_word(w) for w in words]


def doubling(k):
    words = [[-3, 1, 4, 2]] + [[-3, i+4] for i in range(1, k)] + [[-3, k+4]]
    return words, [move([(i, i+3)]) for i in range(k)]


class PersistentEliminationTests(unittest.TestCase):
    def test_random_multibatch_words_match_literal_and_legacy_replay(self):
        rng = random.Random(261009063)
        for _ in range(180):
            rank = rng.randrange(4, 10)
            words, entries = [], []
            for g in range(3, rank+1):
                body = [rng.choice((-1, 1))*rng.randrange(1, g) for _ in range(rng.randrange(4))]
                word = [-g]+body if rng.randrange(2) else [g]+[-x for x in reversed(body)]
                cut = rng.randrange(len(word));words.append(word[cut:]+word[:cut])
                entries.append((len(words)-1, g))
            words += [[], [rng.choice((-1, 1))*rng.randrange(1, rank+1) for _ in range(9)]]
            rng.shuffle(entries);moves=[]
            while entries:
                count=rng.randrange(1, min(3, len(entries))+1)
                moves.append(move(entries[:count]));del entries[:count]
            expected=deepcopy(words);remaining=set(range(1, rank+1))
            old, rr=setup(words);old_alive=set(remaining)
            for evidence in moves:
                self.assertTrue(replay_literal_batch(expected, remaining, evidence, _Budget(lambda:None, 1000000, 10000000)))
                self.assertTrue(replay_compressed_batch(old, rr, old_alive, evidence))
            arena, roots=setup(words);alive=set(range(1, rank+1))
            with patch('fastunknot.elimination_batch.plan_batch', side_effect=AssertionError), patch('fastunknot.elimination_batch.apply_batch', side_effect=AssertionError):
                self.assertTrue(replay_compressed_block(arena, roots, alive, moves))
            self.assertEqual([arena.expand(r) for r in roots], expected)
            self.assertEqual([old.expand(r) for r in rr], expected)
            self.assertEqual(alive, remaining);self.assertEqual(alive, {1, 2})

    def test_binary_powers_and_forward_bindings_without_word_helpers(self):
        arena=WordArena(max_nodes=200000, max_work=20000000)
        roots=[];moves=[];previous=1;expected=1
        for g in range(3, 19):
            image=arena.power(arena.from_word([previous, 1, -previous, 2]), 1 << 256)
            roots.append(arena.concat(arena.letter(-g), image))
            moves.append(move([(g-3, g)]));previous=g
            expected=(2*expected+2)*(1 << 256)
        roots.extend((arena.letter(previous), arena.letter(-previous)))
        with patch.object(arena, 'expand', side_effect=AssertionError), patch.object(arena, 'equal', side_effect=AssertionError), patch.object(arena, 'reduce', side_effect=AssertionError), patch.object(arena, 'inverse', side_effect=AssertionError), patch.object(arena, 'slice', side_effect=AssertionError), patch.object(arena, 'substitute', side_effect=AssertionError):
            self.assertTrue(replay_compressed_block(arena, roots, set(range(1, 19)), moves))
        self.assertEqual(arena.lengths[roots[-1]], expected)
        self.assertEqual(arena.lengths[roots[-2]], expected)
        self.assertEqual(arena.uniform[roots[-1]], 0)

    def test_whole_block_depth_size_bound_and_exponential_raw_length(self):
        k=128;words,moves=doubling(k)
        arena, roots=setup(words, max_nodes=200000, max_work=20000000)
        circuit=_ReplayCircuit(arena, roots);s0=circuit.initial_nodes;d0=circuit.initial_depth
        alive=set(range(1, k+5))
        for i, evidence in enumerate(moves, 1):
            self.assertTrue(circuit.batch(alive, evidence))
            bound=d0+6*i*math.log2(d0+i+2)
            self.assertLessEqual(max(circuit.depth), bound)
        bound=s0+k*(k+1)*(d0+1)//2+2*k*(k-1)*(k+1)*math.log2(d0+k+2)
        self.assertLessEqual(len(circuit.rules)-1, bound)
        before=len(arena.rules)
        output=circuit.export()
        self.assertEqual(arena.lengths[output[-1]], (1 << k)+2)
        self.assertLessEqual(len(arena.rules)-before, 2*(len(circuit.rules)-1))
        self.assertEqual(len(circuit.bindings), k)

    def test_bad_later_batch_is_atomic_and_rejects_cycles_and_types(self):
        words=[[-3, 1], [4, -5], [5, -4], [6, 6], [7, -1], [7]]
        first=move([(0, 3)]);good=move([(4, 7)])
        invalid=[move([(1, 4), (2, 5)]), move([(3, 6)]), move([(0, 3)]), move([]),
                 move([(4, 7), (4, 5)]), move([(4, 7), (5, 7)])]
        for key,value in (('relation', True), ('relation', -1), ('relation', 100), ('generator', True), ('generator', 99), ('extra', 1)):
            bad=deepcopy(good);bad['entries'][0][key]=value;invalid.append(bad)
        bad=deepcopy(good);bad['extra']=True;invalid.append(bad)
        for bad in invalid:
            arena,roots=setup(words);original=list(roots);alive=set(range(1,8))
            self.assertFalse(replay_compressed_block(arena, roots, alive, [first,bad]))
            self.assertEqual(roots,original);self.assertEqual(alive,set(range(1,8)))

    def test_empty_images_repeated_children_and_signed_export(self):
        words=[[3], [-4, 3, 3], [4, -4, 1, 3]]
        arena,roots=setup(words);alive={1,3,4}
        self.assertTrue(replay_compressed_block(arena, roots, alive, [move([(0,3)]), move([(1,4)])]))
        self.assertEqual([arena.expand(r) for r in roots], [[],[],[1]])
        self.assertEqual(alive,{1})
        arena=WordArena();child=arena.letter(3);roots=[arena.concat(child,child),arena.letter(1)]
        self.assertFalse(replay_compressed_block(arena,roots,{1,3},[move([(0,3)])]))

    def test_shared_work_nodes_and_cancellation_preserve_public_state(self):
        words,moves=doubling(8)
        for limit in (0,10,100,300,1000):
            arena,roots=setup(words);original=roots[:];alive=set(range(1,13));arena.left=limit
            try:result=replay_compressed_block(arena,roots,alive,moves)
            except CompressedLimit:
                self.assertEqual(roots,original);self.assertEqual(alive,set(range(1,13)))
            else:self.assertTrue(result)
        arena,roots=setup(words);original=roots[:];alive=set(range(1,13));arena.max_nodes=len(arena.rules)+5
        with self.assertRaises(CompressedLimit):replay_compressed_block(arena,roots,alive,moves)
        self.assertEqual(roots,original);self.assertEqual(alive,set(range(1,13)))
        class Cancel:
            def __bool__(self):return False
            def __call__(self):raise RuntimeError('cancel persistent')
        arena,roots=setup(words);arena.check=Cancel()
        with self.assertRaisesRegex(RuntimeError,'cancel persistent'):replay_compressed_block(arena,roots,set(range(1,13)),moves)

    def test_actual_source_replay_boundaries_legacy_order_and_source_binding(self):
        diagram=Diagram.from_braid(17,list(range(1,17)))
        original=compressed_certificate(diagram,elimination_batch=True)
        entries=original['moves'][0]['entries']
        for backwards in (False,True):
            cert=deepcopy(original)
            chosen=list(reversed(entries)) if backwards else entries
            cert['moves']=[dict(kind='elimination_batch',entries=[e]) for e in chosen]
            stats={}
            self.assertTrue(verify_group_certificate(diagram,cert,compressed=True,stats=stats))
            self.assertTrue(verify_group_certificate(diagram,cert,compressed=False))
            self.assertEqual(stats['persistent_blocks'],1)
            split=deepcopy(cert);split['moves'].insert(3,dict(kind='normalize_relators'))
            stats={};self.assertTrue(verify_group_certificate(diagram,split,compressed=True,stats=stats))
            self.assertEqual(stats['persistent_blocks'],2)
            bad=deepcopy(cert);bad['moves'][-1]['entries'][0]['generator']=True
            self.assertFalse(verify_group_certificate(diagram,bad,compressed=True))
            other=Diagram.from_braid(2,[1,1,1]);bad=deepcopy(cert);bad['input_pd']=[list(r) for r in other.pd]
            self.assertFalse(verify_group_certificate(other,bad,compressed=True))


if __name__=='__main__':unittest.main()
