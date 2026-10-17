#!/usr/bin/env python3
"""Independent finite controls for the reference checker and binary codec."""
import copy
import itertools
import json
import unittest
from pathlib import Path

import clause_codec as codec
import ground_resolution as gr


def literal(p, sign=True, *args):
    return {'positive':sign,'predicate':p,'args':list(args)}


def theory(clauses,functions=None,predicates=None):
    return {'functions':functions or {'o':0},'predicates':predicates or {'A':0,'B':0},
            'clauses':[{'name':f'a{i}','literals':c} for i,c in enumerate(clauses)]}


class ReferenceTests(unittest.TestCase):
    def test_all_512_propositional_clause_sets(self):
        # All non-tautological clauses on two propositions: each proposition
        # is absent, positive, or negative. The empty clause is included.
        possible=[]
        for a,b in itertools.product((0,1,-1),repeat=2):
            possible.append([literal(p,s==1) for p,s in [('A',a),('B',b)] if s])
        nref=0
        for mask in range(1<<len(possible)):
            cs=[c for i,c in enumerate(possible) if mask>>i&1]
            satisfiable=any(all(any(values[l['predicate']]==l['positive'] for l in c) for c in cs)
                for values in ({'A':a,'B':b} for a,b in itertools.product((False,True),repeat=2)))
            k=theory(cs)
            result=gr.refute(k,max_depth=0)
            self.assertEqual(result['status']=='refuted',not satisfiable)
            if not satisfiable:
                nref+=1
                self.assertTrue(gr.verify_certificate(k,result['certificate'])['verified'])
        self.assertEqual(nref,417)

    def test_function_instance(self):
        o=['o'];fo=['f',o]
        k=theory([[literal('P',True,o)],
                  [literal('P',False,'?x'),literal('P',True,['f','?x'])],
                  [literal('P',False,fo)]],{'o':0,'f':1},{'P':1})
        r=gr.refute(k,max_depth=0)
        self.assertEqual(r['status'],'refuted')
        self.assertTrue(gr.verify_certificate(k,r['certificate'])['verified'])

    def test_equality_quotient(self):
        a,b=['a'],['b']
        k=theory([[literal('eq',True,a,b)],[literal('P',True,a)],[literal('P',False,b)]],
                 {'a':0,'b':0},{'P':1,'eq':2})
        r=gr.refute(k,max_depth=0)
        self.assertEqual(r['status'],'refuted')
        self.assertTrue(any(n.get('axiom')=='$eq_predicate_P' for n in r['certificate']['nodes']))

    def test_invalid_certificates(self):
        k=theory([[literal('A')],[literal('A',False)]])
        cert=gr.refute(k,max_depth=0)['certificate']
        corruptions=[]
        c=copy.deepcopy(cert);c['nodes'][0]['clause']=[];corruptions.append(c)
        c=copy.deepcopy(cert);c['nodes'][-1]['parents']=[len(c['nodes']),0];corruptions.append(c)
        c=copy.deepcopy(cert);c['nodes'][-1]['pivot']['predicate']='B';corruptions.append(c)
        c=copy.deepcopy(cert);c['conclusion']=0;corruptions.append(c)
        c=copy.deepcopy(cert);c['nodes'][0]['axiom']='not_an_axiom';corruptions.append(c)
        for c in corruptions:
            with self.assertRaises(ValueError):
                gr.verify_certificate(k,c)

    def test_nonground_substitution_rejected(self):
        k=theory([[literal('P',True,'?x')]],{'o':0},{'P':1})
        bad={'format':'ground-resolution-v1','nodes':[{'kind':'instance','axiom':'a0',
            'substitution':{'?x':'?y'},'clause':[literal('P',True,['o'])]}],'conclusion':0}
        with self.assertRaises(ValueError):
            gr.verify_certificate(k,bad)

    def test_all_512_codec_round_trips(self):
        possible=[]
        for a,b in itertools.product((0,1,-1),repeat=2):
            possible.append([literal(p,s==1) for p,s in [('A',a),('B',b)] if s])
        for mask in range(1<<len(possible)):
            k=theory([c for i,c in enumerate(possible) if mask>>i&1])
            raw,m=codec.encode(k)
            d,n=codec.decode(raw)
            self.assertEqual(d,codec.canonical(k))
            self.assertEqual(n,m['meaningful_bits'])
            self.assertEqual(m['meaningful_bits'],m['header_bits']+m['clause_length_bits']+
                             m['literal_fields_bits']+m['term_fields_bits'])

    def test_variable_scope_and_arity_codec(self):
        k=theory([[literal('P',True,['g','?z',['f','?x'],'?z'],'?x')],
                  [literal('P',False,'?x','?z')]],{'o':0,'f':1,'g':3},{'P':2})
        raw,m=codec.encode(k);d,n=codec.decode(raw)
        self.assertEqual(d,codec.canonical(k))
        for bad in (raw[:-1],raw+b'\0',b'\0'+raw[1:]):
            with self.assertRaises(ValueError):
                codec.decode(bad)
        invalid=copy.deepcopy(k);invalid['clauses'][0]['literals'][0]['args'][0].append(['o'])
        with self.assertRaises(ValueError):
            codec.encode(invalid)

    def test_delivered_kernel_payloads(self):
        data=Path(__file__).resolve().parents[1]/'data'
        paths=list(data.glob('*clauses.json'))
        self.assertTrue(paths,'Kernel payloads are required for this delivery check')
        for path in paths:
            k=json.loads(path.read_text())
            fs,ps,axioms=gr.load_kernel(k)
            self.assertEqual(len(axioms),len(k['clauses'])+len(gr.equality_axioms(fs,ps)))
            raw,m=codec.encode(k);d,n=codec.decode(raw)
            self.assertEqual(d,codec.canonical(k))
            self.assertEqual(n,m['meaningful_bits'])
            stored=path.with_suffix('.bin')
            if stored.exists():
                self.assertEqual(stored.read_bytes(),raw)


if __name__=='__main__':
    unittest.main(verbosity=2)
