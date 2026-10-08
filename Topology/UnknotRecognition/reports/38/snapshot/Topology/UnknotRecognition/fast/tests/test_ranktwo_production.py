import copy
import itertools
import json
from pathlib import Path
import random
import subprocess
import sys
import unittest
from unittest.mock import patch

from fastunknot import Diagram, recognize, khovanov_rank
from fastunknot.ranktwo import compress, verify, optimal_pass
from fastunknot.ranktwo.verify import local_equal
from ranktwo_oracles import brute_optimum, artin_action


def sleeve(m, base=1):
    b = (base, -(base+1))*m
    z = (base, base+1, base)*2
    return b+z+tuple(-v for v in b[::-1])+tuple(-v for v in z[::-1])


def sleeved(m):
    return sleeve(m)+sleeve(m,2)+(1,2,3)


class RankTwoProductionTests(unittest.TestCase):
    def test_optimum_and_independent_braid_action(self):
        rng = random.Random(2026100809)
        for _ in range(200):
            strands = rng.randrange(3, 7)
            word = tuple(rng.choice((-1,1))*rng.randrange(1,strands) for _ in range(rng.randrange(1,12)))
            for radius in (0,1):
                expected = brute_optimum(strands,word,radius)
                for dictionary in ('avl','hash'):
                    result = compress(strands,word,max_passes=1,radius=radius,dictionary=dictionary)
                    reduced,replay = verify(strands,word,result['certificate'])
                    self.assertEqual(len(word)-len(reduced),expected)
                    self.assertEqual(artin_action(strands,word),artin_action(strands,reduced))
                    self.assertLessEqual(replay['removed_nodes'],3*len(word)//2)
        self.assertFalse(local_equal((1,2,1)*2))  # quotient identity is a nontrivial central lift
        self.assertFalse(local_equal((1,),2))     # conjugate generators need not be equal

    def test_certificate_tampering_and_barrier(self):
        word=sleeved(4)
        result=compress(4,word,max_passes=1)
        self.assertEqual(result['word'],[1,2,3])
        for field,value in [('input_length',0),('input_sha256','bad'),('output_word',[1])]:
            broken=copy.deepcopy(result['certificate']);broken[field]=value
            with self.assertRaises(ValueError):verify(4,word,broken)
        broken=copy.deepcopy(result['certificate']);broken['steps'][0]['target']=3
        with self.assertRaises(ValueError):verify(4,word,broken)
        left=(1,2,3,1,2,1);right=(3,2,1,3,2,3)
        barrier=(left+tuple(-v for v in right[::-1]))*10+(1,2,3)
        self.assertEqual(compress(4,barrier,max_passes=1)['word'],list(barrier))
        self.assertEqual(artin_action(4,left),artin_action(4,right))

    def test_homology_profiles_and_restart_provenance(self):
        rng=random.Random(2026100810)
        count=0
        while count<60:
            strands=rng.randrange(2,5)
            word=[rng.choice((-1,1))*rng.randrange(1,strands) for _ in range(rng.randrange(1,10))]
            try:original=Diagram.from_braid(strands,word)
            except ValueError:continue
            i=rng.randrange(1,strands)
            word=word[:2]+[i,-i]+word[2:]
            original=Diagram.from_braid(strands,word)
            result=compress(strands,word,max_passes=1)
            short,_=verify(strands,word,result['certificate'])
            reduced=Diagram.from_braid(strands,short)
            profiles=[]
            for d in (original,reduced):
                raw=khovanov_rank(d.pd,check_d_squared=True)['by_degree']
                shift=d.signs().count(-1)
                profiles.append({h-shift:v for h,v in raw.items()})
            self.assertEqual(*profiles)
            count+=1
        d=Diagram.from_braid(4,sleeved(4))
        result=recognize(d,use_ranktwo=True,ranktwo_seconds=10)
        self.assertEqual(result.status,'UNKNOT')
        self.assertTrue(result.method.startswith('ranktwo-'))
        self.assertEqual(result.input_crossings,d.crossings)
        evidence=result.evidence['before_ranktwo']['ranktwo']
        reduced,_=verify(evidence['source_strands'],evidence['source_word'],evidence['certificate'])
        self.assertEqual(reduced,(1,2,3))
        self.assertIn('after_ranktwo',result.evidence)

    def test_local_global_budgets_and_cheap_decisions(self):
        d=Diagram.from_braid(4,sleeved(1))
        skipped=recognize(d,use_ranktwo=True,ranktwo_seconds=0)
        self.assertEqual(skipped.status,'UNKNOT')
        self.assertEqual(skipped.evidence['ranktwo']['status'],'skipped')
        self.assertEqual(recognize(d,use_ranktwo=True,seconds=0).status,'UNKNOWN')
        with patch('fastunknot.ranktwo.compress',side_effect=MemoryError):
            self.assertEqual(recognize(d,use_ranktwo=True).status,'UNKNOT')
        with patch('fastunknot.ranktwo.compress',side_effect=AssertionError('should not run')):
            self.assertEqual(recognize(Diagram.from_braid(2,[1]*3),use_ranktwo=True).status,'KNOTTED')
            self.assertEqual(recognize(Diagram.from_pd(d.pd),use_ranktwo=True).status,'UNKNOT')
        for options in (dict(use_ranktwo=1),dict(ranktwo_seconds=-1),dict(ranktwo_seconds=float('nan'))):
            with self.assertRaises(ValueError):recognize(d,**options)

    def test_restart_with_exact_backends_and_cli(self):
        d=Diagram.from_braid(4,sleeved(1))
        no_filters=dict(use_braid=False,use_seifert=False,use_reduction=False,use_descending=False,
                        use_alexander=False,use_jones=False,use_factorization=False)
        for backend in ('standard','shared','twist','barcode','fitting'):
            r=recognize(d,use_ranktwo=True,ranktwo_seconds=10,backend=backend,**no_filters)
            self.assertEqual(r.status,'UNKNOT')
            self.assertTrue(r.method.startswith('ranktwo-'))
        data=json.dumps(dict(braid=dict(strands=4,word=sleeved(1))))
        args=[sys.executable,'-B','-m','fastunknot','recognize','-','--ranktwo']
        result=subprocess.run(args,input=data,text=True,capture_output=True)
        self.assertEqual(result.returncode,0,result.stderr)
        self.assertTrue(json.loads(result.stdout)['method'].startswith('ranktwo-'))
        bad=subprocess.run(args+['--ranktwo-seconds','nan'],input=data,text=True,capture_output=True)
        self.assertEqual(bad.returncode,2)
