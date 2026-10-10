"""Arithmetic rank-two terminals with independent algebra and source replay."""
from copy import deepcopy
import importlib.util
from itertools import product
from pathlib import Path
import random
import unittest
from unittest.mock import patch

from fastunknot import Diagram
from fastunknot.compressed_words import WordArena, CompressedLimit
from fastunknot.compressed_search import compressed_certificate, _search
from fastunknot.primitive_power import primitive_power_terminal
from fastunknot.primitive_power_verify import verify_compressed_terminal, verify_literal_terminal
from fastunknot.group_certificate import _Budget, verify_group_certificate, GroupLimit

ROOT=Path(__file__).resolve().parents[1]
spec=importlib.util.spec_from_file_location('primitive_literal_oracle',ROOT.parent/'reports/45/code/oracle.py')
oracle=importlib.util.module_from_spec(spec);spec.loader.exec_module(oracle)


class PrimitivePowerTests(unittest.TestCase):
    def test_exhaustive_cyclic_words_against_literal_root_and_whitehead(self):
        for n in range(1,8):
            for word in product((1,-1,2,-2),repeat=n):
                if any(word[i]==-word[(i+1)%n] for i in range(n)):continue
                arena=WordArena();root=arena.from_word(word)
                proof=primitive_power_terminal(arena,[root],{1,2})
                expected,exponent=oracle.whitehead_primitive_power(word)
                self.assertEqual(proof is not None,expected,word)
                if proof:
                    self.assertEqual(proof['exponent'],exponent)
                    self.assertTrue(verify_compressed_terminal(arena,[root],{1,2},proof))
                    self.assertTrue(verify_literal_terminal([word],{1,2},proof,_Budget(lambda:None,10000,10000)))

    def test_random_parses_large_labels_and_all_relator_slots(self):
        rng=random.Random(261008504)
        labels=(2**80+1,2**80+3)
        for _ in range(300):
            word=oracle.cyclic_reduce(rng.choice((1,-1,2,-2)) for _ in range(rng.randrange(1,80)))
            renamed=[labels[abs(x)-1]*(1 if x>0 else -1) for x in word]
            arena=WordArena();nodes=[arena.letter(x) for x in renamed]
            while len(nodes)>1:
                i=rng.randrange(len(nodes)-1);nodes[i:i+2]=[arena.concat(nodes[i],nodes[i+1])]
            root=nodes[0] if nodes else 0
            roots=[0,root,root]
            proof=primitive_power_terminal(arena,roots,set(labels))
            self.assertEqual(proof is not None,oracle.whitehead_primitive_power(word)[0])
            if proof:
                self.assertEqual(proof['relation'],1)
                self.assertTrue(verify_compressed_terminal(arena,roots,set(labels),proof))
        arena=WordArena();a=arena.letter(1);b=arena.letter(2)
        self.assertIsNone(primitive_power_terminal(arena,[a,b],{1,2}))
        root=arena.power(arena.concat(a,b),3)
        commutator=arena.from_word([1,2,-1,-2])
        roots=[commutator,0,root]
        proof=primitive_power_terminal(arena,roots,{1,2})
        self.assertEqual(proof['relation'],2)
        self.assertEqual(roots,[commutator,0,root])
        self.assertTrue(verify_compressed_terminal(arena,roots,{1,2},proof))

    def test_exponential_nonuniform_kernel_and_independent_replay(self):
        arena=WordArena(max_work=10000000)
        a,b=arena.letter(1),arena.letter(2)
        for _ in range(512):a,b=arena.concat(a,b),a
        root=arena.power(a,(1<<5000)+1)
        before=len(arena.rules)
        with patch.object(arena,'expand',side_effect=AssertionError),patch.object(arena,'equal',side_effect=AssertionError),patch.object(arena,'lcp',side_effect=AssertionError):
            proof=primitive_power_terminal(arena,[root],{1,2})
            self.assertEqual(proof['exponent'],(1<<5000)+1)
            with patch('fastunknot.primitive_power.primitive_power_terminal',side_effect=AssertionError),patch.object(arena,'_reachable',side_effect=AssertionError):
                self.assertTrue(verify_compressed_terminal(arena,[root],{1,2},proof))
        self.assertEqual(len(arena.rules),before)
        self.assertGreater(arena.lengths[root].bit_length(),5000)

    def test_certificate_mutations_noncoherent_roots_and_unknown_symbols(self):
        arena=WordArena();root=arena.from_word([1,2,1,2,2]);roots=[root]
        proof=primitive_power_terminal(arena,roots,{1,2});self.assertIsNotNone(proof)
        changes=[('relation',True),('relation',-1),('generators',[1,True]),('generators',[2,1]),
                 ('primitive_vector',[True,3]),('primitive_vector',[2,4]),('primitive_vector',[2**10000,3]),
                 ('exponent',True),('exponent',2),('width',False),('width',5),('kind','primitive')]
        for key,value in changes:
            bad=deepcopy(proof);bad[key]=value
            self.assertFalse(verify_compressed_terminal(arena,roots,{1,2},bad),(key,value))
        bad=deepcopy(proof);bad['torsion_free']=True
        self.assertFalse(verify_compressed_terminal(arena,roots,{1,2},bad))
        self.assertIsNone(primitive_power_terminal(arena,[arena.from_word([1,2,-1])],{1,2}))
        self.assertIsNone(primitive_power_terminal(arena,[0],{1,2}))
        with self.assertRaises(ValueError):primitive_power_terminal(arena,[arena.letter(3)],{1,2})

    def test_new_terminal_requires_full_reconstructed_knot_source(self):
        d=Diagram.from_braid(3,[1,2]);c=compressed_certificate(d)
        self.assertEqual(c['version'],5);self.assertNotIn('remaining_generator',c)
        old=compressed_certificate(d,primitive_power=False)
        self.assertLess(old['version'],5)
        for compressed in (False,True):
            self.assertTrue(verify_group_certificate(d,c,compressed=compressed))
            self.assertTrue(verify_group_certificate(d,old,compressed=compressed))
            for other in (Diagram.from_braid(2,[1]*3),Diagram.from_braid(2,[1,1,-1])):
                bad=deepcopy(c);bad['input_pd']=[list(r) for r in other.pd]
                self.assertFalse(verify_group_certificate(other,bad,compressed=compressed))
            for key,value in [('version',4),('version',True),('moves',[{'kind':'discard','relation':0}]),('terminal',None)]:
                bad=deepcopy(c);bad[key]=value
                self.assertFalse(verify_group_certificate(d,bad,compressed=compressed))
            bad=deepcopy(c);bad['remaining_generator']=1
            self.assertFalse(verify_group_certificate(d,bad,compressed=compressed))

    def test_compressed_source_replay_with_huge_powered_prefix(self):
        d=Diagram.from_braid(3,[1,2])
        for bits in (8,128,1024):
            k=1<<bits
            c=dict(version=5,method='wirtinger-cyclic-group',status='UNKNOT',input_pd=[list(r) for r in d.pd],
                moves=[dict(kind='whitehead_power',multiplier=1,subset=[1,2],exponent=k)],
                terminal=dict(kind='rank_two_primitive_power',relation=0,generators=[1,2],
                              primitive_vector=[1-k,-1],exponent=1,width=k-1))
            with patch('fastunknot.primitive_power.primitive_power_terminal',side_effect=AssertionError),patch.object(WordArena,'expand',side_effect=AssertionError):
                self.assertTrue(verify_group_certificate(d,c,compressed=True,max_work=10000000))
            if bits==8:self.assertTrue(verify_group_certificate(d,c,max_work=10000000))
            else:
                with self.assertRaises(GroupLimit):verify_group_certificate(d,c,max_work=10000)

    def test_internal_algebraic_success_is_explicit_and_old_contract_retained(self):
        for enabled in (False,True):
            arena=WordArena();base=arena.from_word([1,2,1,2,2]);roots=[arena.power(base,2),arena.power(base,3)]
            alive,moves,terminal={1,2},[],{} if enabled else None
            self.assertTrue(_search(arena,roots,alive,moves,relator_moves=True,primitive_terminal=terminal))
            if enabled:
                self.assertEqual(alive,{1,2});self.assertEqual(moves,[])
                self.assertEqual(terminal['exponent'],2)
                self.assertTrue(verify_compressed_terminal(arena,roots,alive,terminal))
            else:self.assertEqual(len(alive),1);self.assertFalse(any(roots))

    def test_shared_work_limit_cancellation_and_strict_option(self):
        arena=WordArena();root=arena.from_word([1,2,1,2,2]);proof=primitive_power_terminal(arena,[root],{1,2})
        arena.left=0
        with self.assertRaises(CompressedLimit):primitive_power_terminal(arena,[root],{1,2})
        with self.assertRaises(CompressedLimit):verify_compressed_terminal(arena,[root],{1,2},proof)
        def cancel():raise ValueError('caller cancellation')
        arena.check=cancel
        with self.assertRaisesRegex(ValueError,'caller'):verify_compressed_terminal(arena,[root],{1,2},proof)
        with self.assertRaisesRegex(ValueError,'caller'):primitive_power_terminal(arena,[root],{1,2})
        d=Diagram.from_braid(3,[1,2])
        for bad in (1,None,'yes'):
            with self.assertRaises(ValueError):compressed_certificate(d,primitive_power=bad)
