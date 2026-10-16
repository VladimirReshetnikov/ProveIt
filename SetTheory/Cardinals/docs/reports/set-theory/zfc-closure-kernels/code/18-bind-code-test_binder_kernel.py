#!/usr/bin/env python3
"""Deterministic semantic and malformed-certificate tests for binder_kernel."""
import copy
import itertools
import json
from pathlib import Path
import random
import unittest

import binder_kernel as k


def line(rule, args, witnesses=()):
    return {'rule': rule, 'args': list(args), 'witnesses': list(witnesses)}


def random_formula(a, rng, fuel=4, depth=0):
    choices = ['mem', 'bot'] if fuel == 0 else ['mem', 'imp', 'all', 'imp']
    kind = rng.choice(choices)
    if kind == 'bot': return a.bot
    if kind == 'mem':
        def t():
            return k.B(rng.randrange(depth)) if depth and rng.randrange(2) else k.F(rng.randrange(5))
        return a.mem(t(), t())
    if kind == 'all': return a.all(random_formula(a, rng, fuel-1, depth+1))
    return a.imp(random_formula(a, rng, fuel-1, depth), random_formula(a, rng, fuel-1, depth))


def direct_psc(a, matrix, domain, relation, assignment):
    def sub(x,y): return all(not relation(z,x) or relation(z,y) for z in domain)
    def phi(x,y):
        return k.evaluate(a, matrix, domain, relation,
                          lambda i: x if i == 0 else y if i == 1 else assignment(i))
    local = all(any(all(not phi(x,y) or sub(y,b) for y in domain)
                    for b in domain) for x in domain)
    if not local: return True
    def hull(root,c):
        closed = all(not ((sub(x,root) or relation(x,c)) and phi(x,y)) or relation(y,c)
                     for x in domain for y in domain)
        support = all(not relation(y,c) or any(phi(x,y) for x in domain) for y in domain)
        return closed and support
    return all(any(hull(root,c) for c in domain) for root in domain)


class BinderTests(unittest.TestCase):
    counts = {'binding_semantics': 0, 'psc_semantics': 0, 'negative_checks': 0}

    def test_01_binding_semantics(self):
        rng = random.Random(20261016)
        for _ in range(1200):
            a = k.Arena(); p = random_formula(a, rng); name = rng.randrange(5)
            close = k.produce(a,p,k.Mode('close',name)); body = k.verify(a,close)
            opening = k.produce(a,body,k.Mode('open',name)); q = k.verify(a,opening)
            self.assertEqual(p,q)
            self.assertTrue(a.scoped(body,1))
            n = rng.choice((1,2,3)); domain=range(n); bits=rng.getrandbits(n*n)
            rel=lambda x,y: bool(bits & (1 << (x*n+y)))
            env=[rng.randrange(n) for _ in range(5)]
            for value in domain:
                rhs=k.evaluate(a,body,domain,rel,lambda i:env[i],(value,))
                lhs=k.evaluate(a,p,domain,rel,lambda i:value if i==name else env[i])
                self.assertEqual(lhs,rhs)
                self.counts['binding_semantics'] += 1
            opened_sem=k.evaluate(a,q,domain,rel,lambda i:env[i])
            self.assertEqual(opened_sem,k.evaluate(a,body,domain,rel,lambda i:env[i],(env[name],)))
            for mode in (k.Mode('plug',2,0,3),k.Mode('plug',1,0,4),k.Mode('plug',0,1,4)):
                c=k.produce(a,p,mode); out=k.verify(a,c); outer=tuple(rng.randrange(n) for _ in range(mode.width))
                self.assertTrue(a.scoped(out,mode.width))
                lhs=k.evaluate(a,p,domain,rel,lambda i:outer[mode.a] if i==0 else outer[mode.b] if i==1 else env[i])
                rhs=k.evaluate(a,out,domain,rel,lambda i:env[i],outer)
                self.assertEqual(lhs,rhs)
                self.counts['binding_semantics'] += 1

    def test_02_psc_semantics(self):
        rng=random.Random(103016)
        for _ in range(90):
            a=k.Arena(); matrix=random_formula(a,rng,3)
            ws=[k.produce(a,matrix,m) for m in (k.Mode('plug',2,0,3),k.Mode('plug',1,0,4),k.Mode('plug',0,1,4))]
            schema=k.psc(a,matrix,ws)
            for n in (1,2,3):
                graphs=range(1 << (n*n)) if n<3 else [rng.randrange(512) for _ in range(12)]
                for bits in graphs:
                    rel=lambda x,y: bool(bits & (1 << (x*n+y)))
                    env=[rng.randrange(n) for _ in range(5)]
                    want=direct_psc(a,matrix,range(n),rel,lambda i:env[i])
                    got=k.evaluate(a,schema,range(n),rel,lambda i:env[i])
                    self.assertEqual(got,want)
                    self.counts['psc_semantics'] += 1

    def test_03_complete_rule_interfaces(self):
        a=k.Arena(); p=a.mem(k.F(0),k.F(1)); aa=a.imp(p,p)
        s0=a.imp(p,a.imp(aa,p)); s1=a.imp(p,aa)
        s2=a.imp(s0,a.imp(s1,aa)); s3=a.imp(s1,aa)
        lines=[line('K',[p,aa]),line('K',[p,p]),line('S',[p,aa,p]),
               line('MP',[0,2]),line('MP',[1,3])]
        close=k.produce(a,aa,k.Mode('close',0)); allaa=a.all(close['output'])
        lines += [line('GEN',[4,0],[close])]
        opened=k.produce(a,close['output'],k.Mode('open',1))
        ui=a.imp(allaa,opened['output']); lines += [line('UI',[close['output'],1],[opened]),line('MP',[5,6])]
        # Nontrivial same-name instantiation: forall x (R(x,y)->R(x,y)) at y.
        self.assertEqual(a.nodes[opened['output']][1:],(a.mem(k.F(1),k.F(1)),)*2)
        vac=k.produce(a,aa,k.Mode('close',4)); closed=k.produce(a,p,k.Mode('close',4))
        lines += [line('UD',[aa,p,4],[vac,closed]),line('C',[aa,p])]
        modes=(k.Mode('plug',2,0,3),k.Mode('plug',1,0,4),k.Mode('plug',0,1,4))
        psc_ws=[k.produce(a,p,m) for m in modes]
        lines += [line('PSC',[p],psc_ws)]
        doc={'formulas':a.nodes,'lines':lines}
        _, conclusions=k.check_document(json.loads(json.dumps(doc)))
        self.assertEqual(len(conclusions),11)
        self.assertFalse(k.accepts_refutation(doc))
        self.example=doc
        # UI/UD are valid for every two-element relation and all four free assignments.
        checked_arena, conclusions=k.check_document(doc)
        for code in range(16):
            rel=lambda x,y: bool(code & (1 << (2*x+y)))
            for env in itertools.product(range(2),repeat=2):
                assign=lambda i: env[i] if i<2 else 0
                for idx in (0,1,2,3,4,5,6,7,8,9):
                    self.assertTrue(k.evaluate(checked_arena,conclusions[idx],range(2),rel,assign))

    def test_04_reject_tampering(self):
        a=k.Arena(); p=a.all(a.mem(k.B(0),k.F(0)))
        witness=k.produce(a,p,k.Mode('close',0))
        variants=[]
        w=copy.deepcopy(witness); w['rows'][-1][2]+=1; variants.append(w)
        w=copy.deepcopy(witness); w['rows'][-1][3]=[len(w['rows'])-1]; variants.append(w)
        w=copy.deepcopy(witness); w['output']=p; variants.append(w)
        w=copy.deepcopy(witness); w['mode'][1]=1; variants.append(w)
        w=copy.deepcopy(witness); w['rows'][0][3]=[0]; variants.append(w)
        for w in variants:
            with self.assertRaises(k.Invalid): k.verify(a,w)
            self.counts['negative_checks']+=1
        bad=a.mem(k.B(1),k.F(0))
        with self.assertRaises(k.Invalid): k.produce(a,bad,k.Mode('open',0))
        with self.assertRaises(k.Invalid): k.verify(a,witness,k.Mode('close',0),output=p)
        self.counts['negative_checks']+=2
        # All arbitrary wire-level junk must be a rejection, never a Bottom proof.
        junk=[None,{},[],True,{'formulas':[],'lines':[]},
              {'formulas':[['bot'],None],'lines':[]},
              {'formulas':[['bot']],'lines':[{'rule':[],'args':[],'witnesses':[]}]},
              {'formulas':[['bot']],'lines':[line('MP',[0,0])]},
              {'formulas':[['bot']],'lines':[line('GEN',[0,False],[{}])]}]
        for document in junk:
            self.assertFalse(k.accepts_refutation(document))
            self.counts['negative_checks']+=1
        # A free antecedent name cannot be hidden by an alleged fixed-point close.
        atom=a.mem(k.F(0),k.F(1)); cp=k.produce(a,atom,k.Mode('close',0))
        fake=copy.deepcopy(cp); fake['output']=atom
        doc={'formulas':a.nodes,'lines':[line('UD',[atom,atom,0],[fake,cp])]}
        self.assertFalse(k.accepts_refutation(doc)); self.counts['negative_checks']+=1

    def test_05_deep_certificate(self):
        a=k.Arena(); p=a.mem(k.F(0),k.F(1))
        for _ in range(6000): p=a.all(p)
        c=k.produce(a,p,k.Mode('close',0)); q=k.verify(a,c)
        back=k.produce(a,q,k.Mode('open',0)); self.assertEqual(k.verify(a,back),p)
        self.assertEqual(len(c['rows']),6001)
        self.assertTrue(a.scoped(q,1))


def make_example():
    a=k.Arena(); atom=a.mem(k.F(0),k.F(1)); aa=a.imp(atom,atom)
    s0=a.imp(atom,a.imp(aa,atom)); s1=a.imp(atom,aa)
    a.imp(s0,a.imp(s1,aa)); a.imp(s1,aa)
    close=k.produce(a,aa,k.Mode('close',0)); quantified=a.all(close['output'])
    opening=k.produce(a,close['output'],k.Mode('open',1)); a.imp(quantified,opening['output'])
    lines=[line('K',[atom,aa]),line('K',[atom,atom]),line('S',[atom,aa,atom]),
           line('MP',[0,2]),line('MP',[1,3]),line('GEN',[4,0],[close]),
           line('UI',[close['output'],1],[opening]),line('MP',[5,6])]
    return {'formulas':a.nodes,'lines':lines}


def run(output=None):
    suite=unittest.defaultTestLoader.loadTestsFromTestCase(BinderTests)
    result=unittest.TextTestRunner(verbosity=2).run(suite)
    evidence={'scope':'finite executable tests; no compiled TM or formal soundness claim',
              'success':result.wasSuccessful(),'tests':result.testsRun,
              **BinderTests.counts,'deep_binder_depth':6000,
              'example_proof_lines':8,'example_is_refutation':False}
    if output is not None:
        Path(output).write_text(json.dumps(evidence,indent=2)+'\n')
    if not result.wasSuccessful(): raise SystemExit(1)
    return evidence


if __name__=='__main__':
    import argparse
    parser=argparse.ArgumentParser(); parser.add_argument('--output'); parser.add_argument('--example')
    args=parser.parse_args(); print(json.dumps(run(args.output),indent=2))
    if args.example: Path(args.example).write_text(json.dumps(make_example(),indent=2)+'\n')
