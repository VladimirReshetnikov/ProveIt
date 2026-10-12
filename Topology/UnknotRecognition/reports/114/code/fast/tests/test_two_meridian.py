"""PD provenance, independent cube/arithmetic checks and shared-budget replay."""
import copy
from fractions import Fraction as F
import itertools
import json
from pathlib import Path
import random
import subprocess
import sys
import unittest
from unittest.mock import patch

from fastunknot import Diagram, recognize
from fastunknot.geometry import ScanLimit
from fastunknot.group_certificate import _presentation, _Budget as GroupBudget
from fastunknot.two_meridian import (two_meridian_decide, verify_two_meridian_certificate,
    TwoMeridianLimit, _Budget, _model, _rules, _propagate, _multiply, _inverse, _phase)
from test_fastunknot import reference_reduced_rank, one_component

ROOT = Path(__file__).resolve().parents[1]
UNCAPPED = dict(seconds=None, max_work=None, max_attempts=None)
NO_FILTERS = dict(use_braid=False, use_rational=False, use_seifert=False,
    use_reduction=False, use_descending=False, use_alexander=False, use_jones=False,
    use_factorization=False, use_r3=False)


def load(name):
    return Diagram.from_json(json.loads((ROOT/'examples'/(name+'.json')).read_text()))


def budget():
    return _Budget(lambda: None, None, None)


def qmul(x, y):
    a,b,c,d = x; e,f,g,h = y
    return (a*e-b*f-c*g-d*h, a*f+b*e+c*h-d*g,
            a*g-b*h+c*e+d*f, a*h+b*g-c*f+d*e)


def qpow(x, k):
    if k < 0:
        x = (x[0], -x[1], -x[2], -x[3]); k = -k
    out = (F(1),F(0),F(0),F(0))
    while k:
        if k&1: out=qmul(out,x)
        x=qmul(x,x); k>>=1
    return out


class TwoMeridianTests(unittest.TestCase):
    def test_integer_normal_forms_against_rational_quaternions(self):
        rng = random.Random(26100883)
        A = (F(0),F(1),F(0),F(0))
        B = (F(0),F(-3,5),F(4,5),F(0))
        T = qmul(A,B)
        def evaluate(x):
            e,k,s=x
            q=qmul(qpow(T,k),qpow(A,s))
            return tuple((-1)**e*v for v in q)
        for _ in range(300):
            x=(rng.randrange(2),rng.randrange(-12,13),rng.randrange(2))
            y=(rng.randrange(2),rng.randrange(-12,13),rng.randrange(2))
            self.assertEqual(evaluate(_multiply(x,y,budget())),qmul(evaluate(x),evaluate(y)))
            self.assertEqual(qmul(evaluate(x),evaluate(_inverse(x))),(1,0,0,0))
        for _ in range(120):
            forms=[(rng.randrange(2),rng.randrange(-7,8),0) for _ in range(rng.randrange(1,5))]
            result=_phase(forms,budget())
            phases={F(j,d) for d in range(1,15) for j in range(1,d)}
            expected=any(all(((k*p-e)/2).denominator==1 for e,k,_ in forms) for p in phases)
            self.assertEqual(result['status']=='EXISTS',expected)
        self.assertEqual(_phase([(0,0,1)],budget())['status'],'NONE')
        self.assertEqual(_phase([(1,0,0)],budget())['status'],'NONE')

    def test_port_orientations_match_whole_wirtinger_presentation(self):
        rng=random.Random(26100887)
        for name in ('trefoil','figure_eight','hard_unknot_8','conway'):
            for d in (load(name),load(name).mirror()):
                rows=[row[2:]+row[:2] if rng.randrange(2) else row for row in d.pd]
                rng.shuffle(rows); d=Diagram.from_pd(rows)
                _,_,n,crossings=_model(d,budget())
                generators,words=_presentation(d,GroupBudget(lambda:None,100000,1000000))
                def cyclic_reduce(word):
                    stack=[]
                    for x in word:
                        if stack and stack[-1]==-x:stack.pop()
                        else:stack.append(x)
                    while len(stack)>1 and stack[0]==-stack[-1]:stack=stack[1:-1]
                    return stack
                actual=[]
                for o,u,v,sign in crossings:
                    o+=1;u+=1;v+=1
                    actual.append(cyclic_reduce([o,u,-o,-v] if sign==1 else [o,v,-o,-u]))
                self.assertEqual(actual,words)
                self.assertEqual(n,len(generators))

    def test_small_diagrams_against_independent_cube_and_seed_closure(self):
        rng=random.Random(26100889);tested=positive=negative=0
        while tested<80:
            strands=rng.randrange(2,5)
            word=[rng.choice((-1,1))*rng.randrange(1,strands) for _ in range(rng.randrange(1,9))]
            if not one_component(strands,word):continue
            d=Diagram.from_braid(strands,word)
            if tested%2:d=d.mirror()
            expected='UNKNOT' if reference_reduced_rank(d)==1 else 'KNOTTED'
            r=two_meridian_decide(d,**UNCAPPED)
            _,_,n,crossings=_model(d,budget());rules,incidence=_rules(n,crossings,budget())
            possible=False
            for count in (1,2):
                for seeds in itertools.combinations(range(n),count):
                    known=set(seeds)
                    while True:
                        old=set(known)
                        for o,u,v,_ in crossings:
                            if o in known and u in known:known.add(v)
                            if o in known and v in known:known.add(u)
                        if old==known:break
                    trace,reached=_propagate(n,rules,incidence,seeds,budget())
                    self.assertEqual(reached,len(known))
                    possible |= reached==n
            self.assertEqual(r['status']!='INCONCLUSIVE',possible)
            if possible:
                self.assertEqual(r['status'],expected)
                self.assertTrue(verify_two_meridian_certificate(d,r['certificate']))
                positive+=expected=='UNKNOT';negative+=expected=='KNOTTED'
            tested+=1
        self.assertGreater(positive,15);self.assertGreater(negative,10)

    def test_certificate_mutations_and_replay_without_search(self):
        d=load('hard_unknot_8');r=two_meridian_decide(d,**UNCAPPED);c=r['certificate']
        with patch('fastunknot.two_meridian._propagate',side_effect=AssertionError('search during replay')):
            self.assertTrue(verify_two_meridian_certificate(d,json.loads(json.dumps(c))))
        mutations=[]
        for key,value in [('version',True),('method','group'),('input_sha256','x'),
                          ('arc_count',1),('seeds',[0,0]),('status','KNOTTED'),('derivations',[])]:
            bad=copy.deepcopy(c);bad[key]=value;mutations.append(bad)
        bad=copy.deepcopy(c);bad['derivations'][0][2]*=-1;mutations.append(bad)
        bad=copy.deepcopy(c);bad['derivations'][0][0]=c['seeds'][0];mutations.append(bad)
        bad=copy.deepcopy(c);bad['relator_normal_forms'][0][1]+=1;mutations.append(bad)
        bad=copy.deepcopy(c);bad['phase']['gcd']=3;mutations.append(bad)
        for bad in mutations:self.assertFalse(verify_two_meridian_certificate(d,bad),bad)
        self.assertFalse(verify_two_meridian_certificate(load('trefoil'),c))
        for bad in (None,[],{},dict(seeds=None,derivations=[])):
            self.assertFalse(verify_two_meridian_certificate(d,bad))

    def test_shared_work_boundaries_and_global_cancellation(self):
        d=load('figure_eight');full=two_meridian_decide(d,**UNCAPPED)
        work=full['statistics']['work']
        self.assertEqual(two_meridian_decide(d,seconds=None,max_work=work)['certificate'],full['certificate'])
        for allowance in (0,work-1,work-full['statistics']['replay_work']):
            limited=two_meridian_decide(d,seconds=None,max_work=allowance)
            self.assertEqual(limited['status'],'INCONCLUSIVE')
            self.assertNotIn('certificate',limited)
            self.assertLessEqual(limited['statistics']['work'],allowance)
        for options in (dict(seconds=0),dict(max_attempts=0),dict(max_attempts=1)):
            limited=two_meridian_decide(d,**options)
            self.assertEqual(limited['status'],'INCONCLUSIVE')
        with self.assertRaises(TwoMeridianLimit):
            verify_two_meridian_certificate(d,full['certificate'],max_work=0)
        for target in (1,30,90):
            calls=0
            def cancel():
                nonlocal calls
                calls+=1
                if calls==target:raise ScanLimit('caller cancelled')
            with self.assertRaises(ScanLimit):two_meridian_decide(d,check=cancel,**UNCAPPED)
        def cancel():raise ScanLimit('caller cancelled')
        with self.assertRaises(ScanLimit):two_meridian_decide(d,max_work=0,check=cancel)

    def test_validation_empty_input_and_json_large_phase(self):
        for opts in (dict(seconds=True),dict(seconds=float('nan')),dict(max_work=-1),
                     dict(max_attempts=True),dict(max_work=1.5)):
            with self.assertRaises(ValueError):two_meridian_decide(Diagram.from_pd([]),**opts)
        empty=two_meridian_decide(Diagram.from_pd([]),**UNCAPPED)
        self.assertEqual(empty['status'],'UNKNOT')
        self.assertTrue(verify_two_meridian_certificate(Diagram.from_pd([]),empty['certificate']))
        with self.assertRaises(ValueError):two_meridian_decide(Diagram(((0,1,0,1),(2,3,2,3))),**UNCAPPED)
        from fastunknot.integer_codec import json_safe,certificate_equal
        result=_phase([(1,2**16000+1,0)],budget())
        self.assertTrue(certificate_equal(json.loads(json.dumps(json_safe(result))),result))

    def test_factor_certificate_is_bound_to_actual_factor(self):
        from fastunknot.interlace import visible_factors_interlacement
        d = Diagram.from_braid(3, [1, 1, 1, 2, 2, 2])
        factors, _ = visible_factors_interlacement(d)
        options = dict(NO_FILTERS, use_factorization=True)
        result = recognize(d, use_two_meridian=True, **options)
        self.assertEqual((result.status, result.method),
                         ('KNOTTED', 'connected-sum-factor:wirtinger-two-seed'))
        certificate = result.evidence['factors'][0]['two_meridian']['certificate']
        self.assertTrue(verify_two_meridian_certificate(factors[0], certificate))
        self.assertFalse(verify_two_meridian_certificate(d, certificate))

    def test_pipeline_fallback_options_and_cli(self):
        d=load('hard_unknot_8')
        r=recognize(d,use_two_meridian=True,**NO_FILTERS)
        self.assertEqual((r.status,r.method),('UNKNOT','wirtinger-two-seed'))
        for d in (load('conway'),load('hard_unknot_8')):
            r=recognize(d,use_two_meridian=True,two_meridian_max_work=0,**NO_FILTERS)
            self.assertEqual(r.evidence['two_meridian']['status'],'INCONCLUSIVE')
            self.assertNotEqual(r.method,'wirtinger-two-seed')
        for opts in (dict(use_two_meridian=1),dict(two_meridian_seconds=-1),
                     dict(two_meridian_max_work=True),dict(two_meridian_max_attempts=-1)):
            with self.assertRaises(ValueError):recognize(Diagram.from_pd([]),**opts)
        command=[sys.executable,'-B','-m','fastunknot','recognize','-',
            '--two-meridian','--no-braid','--no-rational','--no-seifert','--no-reduction',
            '--no-descending','--no-alexander','--no-jones','--no-factor','--no-r3']
        result=subprocess.run(command,input=json.dumps(load('trefoil').to_json()),text=True,capture_output=True,cwd=ROOT)
        self.assertEqual(result.returncode,0,result.stderr)
        decoded=json.loads(result.stdout)
        self.assertEqual((decoded['status'],decoded['method']),('KNOTTED','wirtinger-two-seed'))
        self.assertFalse(decoded['quasipolynomial_guarantee'])


if __name__=='__main__':unittest.main()
