"""Power-row source authentication, binary capacity and knot-prefix replay."""
from copy import deepcopy
import random
import unittest
from unittest.mock import patch

from fastunknot import Diagram
from fastunknot.compressed_words import WordArena, CompressedLimit
from fastunknot.compressed_search import _search
from fastunknot.group_certificate import _Budget, _presentation, verify_group_certificate
from fastunknot.power_pair import plan_power_pairs, apply_power_pairs
from fastunknot.power_pair_verify import replay_compressed_power_pairs, replay_literal_power_pairs
from fastunknot.primitive_projection import plan_projection
from fastunknot.whitehead_power import powered_images


def family(pairs,bits):
    arena=WordArena(max_nodes=1000000,max_work=100000000);roots=[];M=1<<bits
    for i in range(pairs):
        x,y=2*i+2,2*i+3
        for a,b in ((M,M+1),(M+1,M+2)):
            roots.append(arena.concat(arena.power(arena.letter(x),a),arena.power(arena.letter(-y),b)))
    return arena,roots,set(range(1,2*pairs+2))


def source_certificate():
    diagram=Diagram.from_braid(4,[1,2,3]);alive,words=_presentation(diagram,_Budget(lambda:None,10000,100000))
    arena=WordArena();roots=[arena.from_word(w) for w in words];moves=[]
    for multiplier,subset in ((1,[1,2]),(-1,[-1,-3])):
        moves.append(dict(kind='whitehead',multiplier=multiplier,subset=subset))
        images=powered_images(arena,alive,multiplier,set(subset),1)
        roots=[arena.cyclic_reduce(r) for r in arena.substitute(roots,images)]
    pairs=plan_power_pairs(arena,roots,alive)
    return diagram,dict(version=9,method='wirtinger-cyclic-group',status='UNKNOT',input_pd=[list(r) for r in diagram.pd],
        moves=moves+[dict(kind='power_pair_delete',pairs=pairs)],terminal=dict(kind='rank_one_exponent_zero',generator=1))


class PowerPairTests(unittest.TestCase):
    def test_random_signed_rotations_and_exact_retained_words(self):
        rng=random.Random(261009438)
        for _ in range(400):
            u,v,w,z=[rng.choice([-4,-3,-2,-1,1,2,3,4]) for _ in range(4)]
            words=[]
            for a,b in ((u,v),(w,z)):
                word=[2 if a>0 else -2]*abs(a)+[3 if b>0 else -3]*abs(b)
                cut=rng.randrange(len(word));words.append(word[cut:]+word[:cut])
            words += [[1,2,-1,3,-2],[]]
            arena=WordArena();roots=[arena.from_word(w) for w in words];alive={1,2,3}
            pairs=plan_power_pairs(arena,roots,alive)
            self.assertEqual(bool(pairs),u*z!=v*w)
            if not pairs:continue
            move=dict(kind='power_pair_delete',pairs=pairs);literal=deepcopy(words);ll=set(alive)
            self.assertTrue(replay_literal_power_pairs(literal,ll,move,_Budget(lambda:None,1000000,1000000)))
            rr=roots[:];aa=set(alive)
            self.assertTrue(replay_compressed_power_pairs(arena,rr,aa,move))
            apply_power_pairs(arena,roots,alive,pairs)
            expected=[[x for x in word if abs(x) not in (2,3)] for word in words]
            self.assertEqual(literal,expected);self.assertEqual([arena.expand(r) for r in roots],expected)
            self.assertEqual([arena.expand(r) for r in rr],expected);self.assertEqual(alive,aa);self.assertEqual(alive,ll)

    def test_large_binary_family_closes_after_projection_stalls(self):
        absent=WordArena();absent_roots=[absent.from_word(w) for w in ([2,2],[3,3])]
        with patch('fastunknot.power_pair.plan_power_pairs',side_effect=AssertionError):
            self.assertFalse(_search(absent,absent_roots,{1,2,3},[],primitive_projection=True,primitive_terminal={}))
        arena,roots,alive=family(8,1024)
        self.assertEqual(plan_projection(arena,roots,alive),[])
        original=roots[:];old_alive=set(alive);moves=[];terminal={}
        with patch.object(arena,'expand',side_effect=AssertionError),patch.object(arena,'reduce',side_effect=AssertionError),patch.object(arena,'equal',side_effect=AssertionError):
            self.assertTrue(_search(arena,roots,alive,moves,primitive_projection=True,primitive_terminal=terminal))
            self.assertEqual([m['kind'] for m in moves],['power_pair_delete'])
            self.assertTrue(replay_compressed_power_pairs(arena,original,old_alive,moves[0]))
        self.assertEqual(alive,{1});self.assertEqual(old_alive,{1});self.assertFalse(any(roots));self.assertFalse(any(original))

    def test_reject_shape_and_schema_forgeries_without_publication(self):
        valid=dict(kind='power_pair_delete',pairs=[dict(generators=[2,3],relations=[0,1])])
        for words in ([[2,3,2,3],[2,2,2,3,3,3,3]],[[2,2,-2,3],[2,3,3]],[[2,1,3,-1],[2,2,3,3,3]],[[2,3],[2,2,3,3]]):
            arena=WordArena();roots=[arena.from_word(w) for w in words];old=roots[:];alive={1,2,3}
            self.assertFalse(replay_compressed_power_pairs(arena,roots,alive,valid));self.assertEqual(roots,old);self.assertEqual(alive,{1,2,3})
            literal=deepcopy(words)
            self.assertFalse(replay_literal_power_pairs(literal,alive,valid,_Budget(lambda:None,10000,10000)));self.assertEqual(literal,words)
        mutations=[]
        for key,value in [('generators',[True,3]),('generators',[3,2]),('generators',[2,4]),('relations',[False,1]),('relations',[0,0]),('relations',[0,3])]:
            move=deepcopy(valid);move['pairs'][0][key]=value;mutations.append(move)
        mutations += [dict(valid,extra=1),dict(valid,pairs=[]),dict(valid,pairs=valid['pairs']*2)]
        for move in mutations:
            arena=WordArena();roots=[arena.from_word(w) for w in ([2,3],[2,3,3])]
            self.assertFalse(replay_compressed_power_pairs(arena,roots,{1,2,3},move))

    def test_source_prefix_replay_version_gate_and_no_producer_trust(self):
        diagram,certificate=source_certificate()
        for compressed in (False,True):
            with patch('fastunknot.power_pair.plan_power_pairs',side_effect=AssertionError),patch('fastunknot.power_pair.apply_power_pairs',side_effect=AssertionError):
                self.assertTrue(verify_group_certificate(diagram,certificate,compressed=compressed))
            for version in (6,7,8):
                wrong=deepcopy(certificate);wrong['version']=version
                self.assertFalse(verify_group_certificate(diagram,wrong,compressed=compressed))
            wrong=deepcopy(certificate);wrong['moves']=wrong['moves'][2:]
            self.assertFalse(verify_group_certificate(diagram,wrong,compressed=compressed))

    def test_resource_exhaustion_and_cancellation_are_atomic(self):
        for work in (0,10,100):
            arena,roots,alive=family(3,16);pairs=plan_power_pairs(arena,roots,alive)
            move=dict(kind='power_pair_delete',pairs=pairs);old=roots[:];initial=set(alive);arena.left=work
            with self.assertRaises(CompressedLimit):replay_compressed_power_pairs(arena,roots,alive,move)
            self.assertEqual(roots,old);self.assertEqual(alive,initial)
        arena,roots,alive=family(1,16)
        class Cancel:
            def __bool__(self):return False
            def __call__(self):raise RuntimeError('cancel power pairs')
        arena.check=Cancel()
        with self.assertRaisesRegex(RuntimeError,'cancel power pairs'):plan_power_pairs(arena,roots,alive)


if __name__=='__main__':unittest.main()
