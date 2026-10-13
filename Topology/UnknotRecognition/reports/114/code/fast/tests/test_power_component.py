"""Global power cycles, independent word authentication and source provenance."""
from copy import deepcopy
from fractions import Fraction
import random
import unittest
from unittest.mock import patch
from fastunknot import Diagram
from fastunknot.compressed_words import WordArena,CompressedLimit
from fastunknot.compressed_search import _search
from fastunknot.group_certificate import _Budget,_presentation,verify_group_certificate
from fastunknot.power_pair import power_rows,plan_power_pairs
from fastunknot.power_component import plan_power_components,apply_power_components
from fastunknot.power_component_verify import replay_compressed_power_components,replay_literal_power_components
from fastunknot.primitive_projection import plan_projection
from fastunknot.whitehead_power import powered_images


def family(rank,bits,arena_type=WordArena):
    assert rank>=3 and bits>=rank-1
    a=arena_type(max_nodes=1000000,max_work=100000000);roots=[];P=1+(1<<bits)
    labels=list(range(2,rank+2));last=(P**rank-1)//(1<<(rank-1))
    for i,g in enumerate(labels):
        h=labels[(i+1)%rank];b=last if i==rank-1 else 2
        roots.append(a.concat(a.power(a.letter(g),P),a.power(a.letter(-h),b)))
    return a,roots,set([1]+labels)


def source_certificate(strands=5):
    d=Diagram.from_braid(strands,list(range(1,strands)));alive,words=_presentation(d,_Budget(lambda:None,100000,1000000))
    a=WordArena();roots=[a.from_word(w) for w in words];moves=[]
    for g in sorted(alive-{1}):
        p,q=g-2,3-g;ops=[]
        if q:ops.append((1 if q>0 else -1,{1 if q>0 else -1,g},abs(q)))
        if p:ops.append((-1,{-1,-g},p))
        for mult,subset,k in ops:
            move=dict(kind='whitehead',multiplier=mult,subset=sorted(subset))
            if k>1:move.update(kind='whitehead_power',exponent=k)
            moves.append(move)
            roots=[a.cyclic_reduce(r) for r in a.substitute(roots,powered_images(a,alive,mult,subset,k))]
    components=plan_power_components(a,alive,power_rows(a,roots,alive))
    return d,dict(version=10,method='wirtinger-cyclic-group',status='UNKNOT',input_pd=[list(r) for r in d.pd],
                  moves=moves+[dict(kind='power_component_delete',components=components)],
                  terminal=dict(kind='rank_one_exponent_zero',generator=1))


def rank(rows,n):
    matrix=[[Fraction(v) for v in row] for row in rows];pivot=0
    for column in range(n):
        found=next((i for i in range(pivot,len(matrix)) if matrix[i][column]),None)
        if found is None:continue
        matrix[pivot],matrix[found]=matrix[found],matrix[pivot];div=matrix[pivot][column]
        matrix[pivot]=[x/div for x in matrix[pivot]]
        for i in range(pivot+1,len(matrix)):
            k=matrix[i][column]
            matrix[i]=[x-k*y for x,y in zip(matrix[i],matrix[pivot])]
        pivot+=1
    return pivot


class PowerComponentTests(unittest.TestCase):
    def test_random_graphs_against_independent_rational_rank_and_literal_words(self):
        rng=random.Random(261009457)
        for trial in range(400):
            n=rng.randrange(3,9);labels=list(range(2,n+2));words=[];matrix=[]
            edges=[(g,rng.choice(labels[:i])) for i,g in enumerate(labels) if i]
            edges += [tuple(rng.sample(labels,2)) for _ in range(rng.randrange(4))]
            for g,h in edges:
                u,v=[rng.choice((-3,-2,-1,1,2,3)) for _ in range(2)]
                word=[g if u>0 else -g]*abs(u)+[h if v>0 else -h]*abs(v)
                cut=rng.randrange(len(word));words.append(word[cut:]+word[:cut])
                row=[0]*n;row[g-2]=u;row[h-2]=v;matrix.append(row)
            if trial%5==0:
                g=rng.choice(labels);words.append([g]*2);row=[0]*n;row[g-2]=2;matrix.append(row)
            words += [[],[1,labels[0],-1,labels[-1],1]]
            a=WordArena();roots=[a.from_word(w) for w in words];alive=set([1]+labels)
            components=plan_power_components(a,alive,power_rows(a,roots,alive))
            self.assertEqual(bool(components),rank(matrix,n)==n)
            if not components:continue
            move=dict(kind='power_component_delete',components=components)
            literal=deepcopy(words);ll=set(alive);rr=roots[:];aa=set(alive)
            self.assertTrue(replay_literal_power_components(literal,ll,move,_Budget(lambda:None,1000000,1000000)))
            self.assertTrue(replay_compressed_power_components(a,rr,aa,move))
            apply_power_components(a,roots,alive,components)
            expected=[[x for x in w if abs(x)==1] for w in words]
            self.assertEqual(literal,expected);self.assertEqual(ll,{1});self.assertEqual(aa,ll);self.assertEqual(alive,ll)
            self.assertEqual([a.expand(r) for r in roots],expected);self.assertEqual([a.expand(r) for r in rr],expected)

    def test_binary_cycle_strictly_extends_local_detectors(self):
        for n,bits in ((3,64),(16,128),(32,128)):
            a,roots,alive=family(n,bits)
            self.assertFalse(plan_projection(a,roots,alive));self.assertFalse(plan_power_pairs(a,roots,alive))
            original=roots[:];labels=set(alive);moves=[];terminal={}
            with patch.object(a,'expand',side_effect=AssertionError),patch.object(a,'reduce',side_effect=AssertionError), \
                 patch.object(a,'equal',side_effect=AssertionError),patch.object(a,'cyclic_reduce',side_effect=AssertionError):
                self.assertTrue(_search(a,roots,alive,moves,primitive_projection=True,primitive_terminal=terminal))
                self.assertEqual([m['kind'] for m in moves],['power_component_delete'])
                with patch('fastunknot.power_component.plan_power_components',side_effect=AssertionError), \
                     patch('fastunknot.power_component.apply_power_components',side_effect=AssertionError):
                    self.assertTrue(replay_compressed_power_components(a,original,labels,moves[0]))
            self.assertEqual(alive,{1});self.assertEqual(labels,{1});self.assertFalse(any(original))
            self.assertEqual(terminal,dict(kind='rank_one_exponent_zero',generator=1))

    def test_signed_cycle_pure_seed_and_rejection_of_shapes_and_bad_graphs(self):
        valid=dict(kind='power_component_delete',components=[dict(generators=[2,3,4],relations=[0,1,2])])
        for words,expected in [([[2,2,3,3],[3,3,4,4],[4,4,2,2]],True),
                               ([[2,2,-3,-3],[3,3,-4,-4],[4,4,-2,-2]],False),
                               ([[2,2],[2,3],[3,4]],True),
                               ([[2,2],[3,3],[3,4]],False),
                               ([[2,3,2,3],[3,4],[4,2]],False),
                               ([[2,1,3,-1],[3,4],[4,2]],False),
                               ([[2,-2,3],[3,4],[4,2]],False)]:
            a=WordArena();roots=[a.from_word(w) for w in words];before=roots[:];alive={1,2,3,4}
            self.assertEqual(replay_compressed_power_components(a,roots,alive,valid),expected)
            literal=deepcopy(words);ll={1,2,3,4}
            self.assertEqual(replay_literal_power_components(literal,ll,valid,_Budget(lambda:None,100000,100000)),expected)
            if not expected:self.assertEqual(roots,before);self.assertEqual(alive,{1,2,3,4});self.assertEqual(literal,words)
        for key,value in [('generators',[True,3,4]),('generators',[2,2,4]),('generators',[2,3,5]),('relations',[False,1,2]),('relations',[0,0,2]),('relations',[0,1,9])]:
            bad=deepcopy(valid);bad['components'][0][key]=value;a,roots,alive=family(3,3)
            self.assertFalse(replay_compressed_power_components(a,roots,alive,bad))
        for bad in (dict(valid,extra=1),dict(valid,components=[]),dict(valid,components=valid['components']*2)):
            a,roots,alive=family(3,3);self.assertFalse(replay_compressed_power_components(a,roots,alive,bad))
        a,roots,alive=family(3,3);alive.remove(1)
        self.assertFalse(replay_compressed_power_components(a,roots,alive,valid))

    def test_source_prefix_schema_and_foreign_pd(self):
        for n in (5,9):
            d,cert=source_certificate(n)
            for compressed in (False,True):
                with patch('fastunknot.power_component.plan_power_components',side_effect=AssertionError), \
                     patch('fastunknot.power_component.apply_power_components',side_effect=AssertionError):
                    self.assertTrue(verify_group_certificate(d,cert,compressed=compressed,max_work=20000000))
                bad=deepcopy(cert);bad['version']=9;self.assertFalse(verify_group_certificate(d,bad,compressed=compressed))
                bad=deepcopy(cert);bad['moves']=bad['moves'][-1:];self.assertFalse(verify_group_certificate(d,bad,compressed=compressed))
                other=Diagram.from_braid(2,[1,1,1]);bad=deepcopy(cert);bad['input_pd']=[list(r) for r in other.pd]
                self.assertFalse(verify_group_certificate(other,bad,compressed=compressed))

    def test_resource_limits_and_cancellation_leave_public_state(self):
        for work in (0,10,100):
            a,roots,alive=family(6,16);components=plan_power_components(a,alive,power_rows(a,roots,alive));move=dict(kind='power_component_delete',components=components)
            before=roots[:];labels=set(alive);a.left=work
            with self.assertRaises(CompressedLimit):replay_compressed_power_components(a,roots,alive,move)
            self.assertEqual(roots,before);self.assertEqual(alive,labels)
        a,roots,alive=family(3,4);roots.append(a.from_word([1,2,3,1]))
        components=plan_power_components(a,alive,power_rows(a,roots,alive))
        move=dict(kind='power_component_delete',components=components);before=roots[:];labels=set(alive)
        a.max_nodes=len(a.rules)-1
        with self.assertRaises(CompressedLimit):replay_compressed_power_components(a,roots,alive,move)
        self.assertEqual(roots,before);self.assertEqual(alive,labels)
        class Cancel:
            def __bool__(self):return False
            def __call__(self):raise RuntimeError('cancel component')
        a,roots,alive=family(3,4);rows=power_rows(a,roots,alive);a.check=Cancel()
        with self.assertRaisesRegex(RuntimeError,'cancel component'):plan_power_components(a,alive,rows)
