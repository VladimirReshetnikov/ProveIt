"""Original-position replay, topology oracles and linear descent work bounds."""
import copy
import itertools
import random
import unittest
from unittest.mock import patch

from fastunknot.braid_descent import linear_descent
from fastunknot.braid_reduction import singleton_reduce, verify_singleton_reduction
from fastunknot.braid import braid_certificate
from fastunknot.diagram import Diagram
from fastunknot.scan import khovanov_rank


def slow(strands, word):
    word=list(word)
    while True:
        stack=[]
        for g in word:
            if stack and stack[-1]==-g:stack.pop()
            else:stack.append(g)
        while len(stack)>1 and stack[0]==-stack[-1]:
            stack=stack[1:-1]
        word=stack
        if strands<=3:break
        candidates=[i for i,g in enumerate(word) if abs(g)==strands-1]
        left=False
        if len(candidates)!=1:
            candidates=[i for i,g in enumerate(word) if abs(g)==1]
            left=True
        if len(candidates)!=1:break
        i=candidates[0];word=word[i+1:]+word[:i]
        if left:word=[g-1 if g>0 else g+1 for g in word]
        strands-=1
    return strands,tuple(word)


def cyclic(word):
    return min((word[i:]+word[:i] for i in range(len(word))),default=())


class LinearDescentTests(unittest.TestCase):
    def audit(self,strands,word):
        n,final,cert=linear_descent(strands,tuple(word),lambda:None)
        self.assertEqual(verify_singleton_reduction(strands,word,cert),(n,final))
        old,expected=slow(strands,word)
        self.assertEqual((n,cyclic(final)),(old,cyclic(expected)))
        self.assertLessEqual(cert['queue_pops'],2*len(word))
        self.assertLessEqual(len(cert['steps']),len(word))
        # A deliberately slow, list-based original-position oracle checks the
        # local witness independently of either linked-list implementation.
        positions=list(range(len(word)));lo=0;hi=strands
        for step in cert['steps']:
            if step['op']=='cancel':
                a,z=step['first'],step['second'];i=positions.index(a)
                self.assertEqual(positions[(i+1)%len(positions)],z)
                self.assertEqual(word[a],-word[z])
                positions.remove(a);positions.remove(z)
            else:
                p=step['position'];i=positions.index(p)
                endpoint=hi-1 if step['side']=='right' else lo+1
                self.assertEqual(sum(abs(word[j])==endpoint for j in positions),1)
                self.assertEqual(abs(word[p]),endpoint)
                positions=positions[i+1:]+positions[:i]
                if step['side']=='right':hi-=1
                else:lo+=1
        # Removing a head/wrapped cancellation in the list preserves the same
        # next surviving head as the producer's local linked-list operation.
        self.assertEqual(positions,cert['final_positions'])
        self.assertEqual(tuple((1 if word[p]>0 else -1)*(abs(word[p])-lo)
                               for p in positions),final)
        return cert

    def test_exhaustive_small_words_and_cyclic_cancellations(self):
        for strands in (2,3,4):
            for length in range(strands-1,6):
                for word in itertools.product(range(1,strands),repeat=length):
                    # All sign patterns on smaller ranks; a deterministic mixed
                    # pattern plus its mirror on rank four keeps this bounded.
                    patterns=itertools.product((-1,1),repeat=length) if strands<4 else (
                        tuple(1 if i%2 else -1 for i in range(length)),(1,)*length)
                    for signs in patterns:
                        self.audit(strands,tuple(x*y for x,y in zip(word,signs)))

    def test_random_conjugated_mixed_stabilizations(self):
        rng=random.Random(261008111)
        for case in range(120):
            word=[1,-2];strands=3
            for _ in range(rng.randrange(1,100)):
                sign=rng.choice((-1,1))
                if rng.randrange(2):word.append(sign*strands)
                else:word=[g+1 if g>0 else g-1 for g in word]+[sign]
                strands+=1
            conj=[rng.choice((-1,1))*rng.randrange(1,strands) for _ in range(25)]
            word=conj+word+[-g for g in reversed(conj)]
            self.audit(strands,word)

    def test_large_dispatch_both_signs_and_modes(self):
        for strands in (129,512,2048):
            word=[1,-2]+list(range(3,strands))
            for sign in (-1,1):
                source=[sign*g for g in word]
                n,w,cert=singleton_reduce(strands,source)
                self.assertEqual(n,3)
                self.assertEqual(cert['kind'],'singleton-markov-descent-v2')
                self.assertEqual(verify_singleton_reduction(strands,source,cert),(n,w))
                self.assertLessEqual(cert['queue_pops'],2*len(source))
                for backend in ('free-product','matrix'):
                    self.assertEqual(braid_certificate(strands,source,backend=backend,
                        use_braid_reduction=True)['status'],'UNKNOT')

    def test_small_rank_and_sparse_inputs_keep_legacy_path(self):
        with patch('fastunknot.braid_descent.linear_descent',side_effect=AssertionError):
            self.assertEqual(singleton_reduce(4,[1,-2,3]*100)[2]['kind'],
                             'singleton-markov-descent-v1')
            self.assertEqual(singleton_reduce(10**30,[])[0],10**30)

    def test_topology_on_small_stabilizations(self):
        for base in ([1,-2],[1,1,1,2],[1,-2]*2):
            for sign in (-1,1):
                for left in (False,True):
                    word=([g+1 if g>0 else g-1 for g in base]+[sign]
                          if left else list(base)+[sign*3])
                    n,w,cert=linear_descent(4,word,lambda:None)
                    self.assertEqual(khovanov_rank(Diagram.from_braid(4,word).pd)['reduced_rank'],
                                     khovanov_rank(Diagram.from_braid(n,w).pd)['reduced_rank'])

    def test_malformed_evidence_and_input_binding(self):
        source=[1,-2,3,4,5]
        _,_,cert=linear_descent(6,source,lambda:None)
        changes=[('input_strands',True),('final_strands',True),('final_word',[True]),
                 ('final_positions',[False]),('queue_pops',100),('steps',[None]),
                 ('steps',cert['steps']*4)]
        for key,value in changes:
            bad=copy.deepcopy(cert);bad[key]=value
            with self.assertRaises(ValueError):verify_singleton_reduction(6,source,bad)
        for key,value in (('position',False),('position',-1),('side','left'),('op','unknown')):
            bad=copy.deepcopy(cert);bad['steps'][0][key]=value
            with self.assertRaises(ValueError):verify_singleton_reduction(6,source,bad)
        bad=copy.deepcopy(cert);bad['steps'].insert(1,bad['steps'][0])
        with self.assertRaises(ValueError):verify_singleton_reduction(6,source,bad)
        with self.assertRaises(ValueError):verify_singleton_reduction(6,[1,-2,3,5,5],cert)
        # Mutation of the witness cannot authorize deleting a noninverse pair.
        _,_,cancel=linear_descent(4,[1,-1,2,3],lambda:None)
        with self.assertRaises(ValueError):verify_singleton_reduction(4,[1,1,2,3],cancel)

    def test_cancellation_callback_stops_producer_and_verifier(self):
        source=[1,-2]+list(range(3,1024))
        _,_,cert=singleton_reduce(1024,source)
        for function in (lambda cb:singleton_reduce(1024,source,cb),
                         lambda cb:verify_singleton_reduction(1024,source,cert,cb)):
            count=0
            def stop():
                nonlocal count
                count+=1
                if count==3:raise TimeoutError('audit stop')
            with self.assertRaises(TimeoutError):function(stop)
