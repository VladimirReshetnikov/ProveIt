#!/usr/bin/env python3
"""Paid natural-domain parity atoms and one complete NAND example.
L inputs are already evaluated integers. All binary +,-,* gates are charged.
No claim of real-orthant nonnegativity, unrestricted optimality or universality.
"""
from __future__ import annotations
import argparse
import copy
import hashlib
import itertools
import json
from pathlib import Path
import random

PARENT_SHA = 'f33ba14f16009f4e825e00a91d1714696dadf34002ada3bf72fcbccc04a52cfc'
MODES = ('signed_existential', 'signed_canonical', 'natural')
VARIANTS = ('relation', 'accepted', 'projected', 'factored')


def need(ok, message):
    if not ok: raise ValueError(message)


def exact(a, b):
    if type(a) is not type(b): return False
    if type(a) is dict: return a.keys() == b.keys() and all(exact(a[k], b[k]) for k in a)
    if type(a) in (list, tuple): return len(a) == len(b) and all(exact(x, y) for x, y in zip(a, b))
    return a == b


def mode_check(mode):
    need(type(mode) is str and mode in MODES, 'unknown exact-string mode')


def integer(x):
    need(type(x) is int, 'exact integer required')
    return x


class _DAG:
    def __init__(self): self.gates = []
    def op(self, op, a, b):
        name = 'g' + str(len(self.gates))
        self.gates.append([name, op, a, b])
        return name
    def add(self,a,b): return self.op('add',a,b)
    def sub(self,a,b): return self.op('sub',a,b)
    def mul(self,a,b): return self.op('mul',a,b)
    def square(self,a): return self.mul(a,a)
    def total(self, terms):
        out = terms[0]
        for term in terms[1:]: out = self.add(out, term)
        return out


def _parts(g, mode, prefix, boolean=True):
    L, b = prefix+'L', prefix+'b'
    if mode == 'natural':
        q = prefix+'q'; witnesses = [q,b]
    else:
        qp,qm = prefix+'qp',prefix+'qm'
        q = g.sub(qp,qm); witnesses = [qp,qm,b]
    r = g.sub(g.sub(L,g.mul(2,q)),b)
    terms = [g.square(r)]
    bm = None
    if boolean:
        bm = g.sub(b,1); terms.append(g.mul(b,bm))
    if mode == 'signed_canonical': terms.append(g.mul(prefix+'qp',prefix+'qm'))
    return terms,bm,witnesses


def _finish(g, config, inputs, witnesses, output, truth=None):
    return {'format':'parity_truth_specialization_v1','config':config,
            'inputs':inputs,'witnesses':witnesses,'gates':g.gates,
            'output':output,'truth_output':truth,
            'ledger':{'M':sum(row[1]=='mul' for row in g.gates),
                      'A':sum(row[1]!='mul' for row in g.gates),
                      'total':len(g.gates),'witnesses':len(witnesses)},
            'domain':{'inputs':'natural' if config['mode']=='natural' else 'signed integer',
                      'witnesses':'natural'},
            'context_parent_sha256':PARENT_SHA}


def build_atom(mode='signed_existential', *, materialize_truth=False):
    mode_check(mode);need(type(materialize_truth) is bool,'exact bool required')
    g=_DAG();terms,bm,w=_parts(g,mode,'');out=g.total(terms)
    truth=g.sub(1,'b') if materialize_truth else None
    packet=_finish(g,{'kind':'atom','mode':mode,'materialize_truth':materialize_truth},['L'],w,out,truth)
    packet['truth_expression']='1-b'
    return packet


def build_nand(mode='signed_existential', *, variant='relation'):
    mode_check(mode);need(type(variant) is str and variant in VARIANTS,'unknown NAND variant')
    g=_DAG();boolean=variant!='factored'
    a,am,aw=_parts(g,mode,'a_',boolean);b,bm,bw=_parts(g,mode,'b_',boolean)
    terms=a+b;w=aw+bw
    if variant=='factored':
        c=g.sub(g.add('a_b','b_b'),1)
        terms.append(g.sub(g.square(c),g.mul('a_b','b_b')))
    else:
        product=g.mul(am,bm)
        if variant=='projected':terms.append(g.square(product))
        else:
            w=w+['z'];zminus=g.sub('z',1)
            terms.append(g.square(g.add(zminus,product)))
            if variant=='accepted':terms.append(g.square(zminus))
    return _finish(g,{'kind':'nand','mode':mode,'variant':variant},['a_L','b_L'],w,g.total(terms))


def checked(packet):
    need(type(packet) is dict and type(packet.get('config')) is dict,'canonical packet required')
    c=packet['config'];kind=c.get('kind')
    if type(kind) is str and kind=='atom':
        need(set(c)=={'kind','mode','materialize_truth'},'atom config fields')
        fresh=build_atom(c['mode'],materialize_truth=c['materialize_truth'])
    elif type(kind) is str and kind=='nand':
        need(set(c)=={'kind','mode','variant'},'NAND config fields')
        fresh=build_nand(c['mode'],variant=c['variant'])
    else: raise ValueError('unknown canonical packet kind')
    need(exact(packet,fresh),'packet differs from full canonical source')
    return fresh


def _eval(packet, values):
    env=dict(values)
    def value(x):return x if type(x) is int else env[x]
    for name,op,a,b in packet['gates']:
        a,b=value(a),value(b)
        env[name]=a+b if op=='add' else a-b if op=='sub' else a*b
    out={'penalty':env[packet['output']]}
    if packet['truth_output'] is not None:out['truth']=env[packet['truth_output']]
    return out


def evaluate(packet, values, *, integer_arithmetic_only=False):
    p=checked(packet);need(type(integer_arithmetic_only) is bool,'exact bool required')
    need(type(values) is dict and set(values)==set(p['inputs']+p['witnesses']),'exact assignment keys required')
    need(all(type(v) is int for v in values.values()),'exact integer coordinates required')
    if not integer_arithmetic_only:
        need(all(values[k]>=0 for k in p['witnesses']),'natural witnesses required')
        if p['config']['mode']=='natural':need(all(values[k]>=0 for k in p['inputs']),'natural inputs required')
    return _eval(p,values)


def canonical(mode,L,*,offset=0):
    mode_check(mode);integer(L);integer(offset);need(offset>=0,'nonnegative offset required')
    if mode=='natural':need(L>=0 and offset==0,'natural input and zero offset required')
    elif mode=='signed_canonical':need(offset==0,'canonical offset must be zero')
    q,b=divmod(L,2)
    if mode=='natural':return {'q':q,'b':b}
    return {'qp':max(q,0)+offset,'qm':max(-q,0)+offset,'b':b}


def restore_parent(packet,values):
    """On an atom zero, normalize private quotient splitting and restore d=2 parent.
    This existential relation map is not an off-zero polynomial identity.
    """
    p=checked(packet);need(p['config']['kind']=='atom','atom required')
    need(evaluate(p,values)['penalty']==0,'a natural-domain atom zero is required')
    q,b=divmod(values['L'],2)
    return {'L':values['L'],'qp':max(q,0),'qm':max(-q,0),'b':b,'s':0,'h':1-b}


def verify(parent):
    need(__debug__,'run without -O')
    parent=Path(parent);need(hashlib.sha256(parent.read_bytes()).hexdigest()==PARENT_SHA,'parent source pin mismatch')
    import sympy as sp
    counts={}
    def check(key,ok):
        need(bool(ok),key);counts[key]=counts.get(key,0)+1
    packets=[]
    def symbols(p):return {k:sp.Symbol(k) for k in p['inputs']+p['witnesses']}
    def manual_atom(x,mode,prefix='',boolean=True):
        q=x[prefix+'q'] if mode=='natural' else x[prefix+'qp']-x[prefix+'qm']
        b=x[prefix+'b'];r=x[prefix+'L']-2*q-b
        return r*r+(b*(b-1) if boolean else 0)+(x[prefix+'qp']*x[prefix+'qm'] if mode=='signed_canonical' else 0)
    for mode in MODES:
        for materialize in (False,True):
            p=build_atom(mode,materialize_truth=materialize);x=symbols(p)
            P=sp.expand(_eval(p,x)['penalty']);check('complete_symbolic_atom',sp.expand(P-manual_atom(x,mode))==0)
            check('exact_degree',sp.Poly(P,*x.values()).total_degree()==2)
            baseline={'signed_existential':(3,5),'signed_canonical':(4,6),'natural':(3,4)}[mode]
            check('full_charged_ledger',(p['ledger']['M'],p['ledger']['A'])==(baseline[0],baseline[1]+int(materialize)))
            if materialize:check('complete_truth_output',_eval(p,x)['truth']==1-x['b'])
            packets.append(p)
        forms={}
        for variant in VARIANTS:
            p=build_nand(mode,variant=variant);x=symbols(p);P=sp.expand(_eval(p,x)['penalty']);forms[variant]=(p,x,P)
            b1,b2=x['a_b'],x['b_b'];g=(b1-1)*(b2-1)
            if variant=='factored':target=manual_atom(x,mode,'a_',False)+manual_atom(x,mode,'b_',False)+(b1+b2-1)**2-b1*b2
            else:
                target=manual_atom(x,mode,'a_')+manual_atom(x,mode,'b_')
                target+=g*g if variant=='projected' else (x['z']-1+g)**2
                if variant=='accepted':target+=(x['z']-1)**2
            check('complete_symbolic_NAND',sp.expand(P-target)==0)
            check('exact_degree',sp.Poly(P,*x.values()).total_degree()==(2 if variant=='factored' else 4))
            m,a={'relation':(8,14),'accepted':(9,15),'projected':(8,12),'factored':(6,11)}[variant]
            dm,da={'signed_existential':(0,0),'signed_canonical':(2,2),'natural':(0,-2)}[mode]
            check('full_charged_ledger',(p['ledger']['M'],p['ledger']['A'])==(m+dm,a+da));packets.append(p)
        check('complete_acceptance_graph_identity',sp.expand(forms['accepted'][2].subs(sp.Symbol('z'),1)-forms['projected'][2])==0)
        x=forms['projected'][1];g=(x['a_b']-1)*(x['b_b']-1)
        check('complete_offzero_NAND_correction',sp.expand(forms['projected'][2]-forms['factored'][2]-(g*g-g))==0)
    # Parent d=2 graph: s=0,h=1-b. Its old quartic keeps squared penalties.
    L,qp,qm,b=sp.symbols('L qp qm b');r=L-2*(qp-qm)-b
    parent_rows=(qp*qm,r,0,b*(b-1),0)
    old=sum(v*v for v in parent_rows);new=r*r+b*(b-1)+qp*qm
    check('complete_parent_graph_correction',sp.expand(old-new-((qp*qm)**2-qp*qm+(b*(b-1))**2-b*(b-1)))==0)
    # Exhaust all bounded natural assignments, comparing independently derived fibers.
    for mode in MODES:
        p=build_atom(mode);Ls=range(0,15) if mode=='natural' else range(-14,15)
        for L in Ls:
            for W in itertools.product(range(8),repeat=len(p['witnesses'])):
                x=dict(zip(p['witnesses'],W));x['L']=L
                val=_eval(p,x)['penalty'];q= L//2
                expected=x['b']==L%2 and ((x['q']==q) if mode=='natural' else (x['qp']-x['qm']==q and (mode!='signed_canonical' or x['qp']*x['qm']==0)))
                check('exhaustive_atom_zero_fibers',(val==0)==expected and val>=0)
    # NAND Boolean block independently excludes all nonbits on N^2.
    for a,b in itertools.product(range(30),repeat=2):
        B=(a+b-1)**2-a*b
        check('exhaustive_NAND_boolean_block',B>=0 and (B==0)==((a,b) in ((0,1),(1,0),(1,1))))
    rng=random.Random(731198)
    for p in packets:
        xnames=p['inputs']+p['witnesses']
        # Every emitted register must be live in an exported output.
        dependencies={n:(a,b) for n,_,a,b in p['gates']};live=set()
        def visit(n):
            if n in dependencies and n not in live:
                live.add(n)
                for v in dependencies[n]:
                    if type(v) is str:visit(v)
        visit(p['output'])
        if p['truth_output'] is not None:visit(p['truth_output'])
        check('all_paid_gates_live',len(live)==len(p['gates']))
        for _ in range(24):
            x={k:rng.randrange(-10**20,10**20) for k in xnames};sx=symbols(p)
            poly=_eval(p,sx)['penalty']
            check('full_large_signed_evaluation',evaluate(p,x,integer_arithmetic_only=True)['penalty']==int(poly.subs({sx[k]:v for k,v in x.items()})))
        cp=copy.deepcopy(p);cp['gates'][0][2]=0.0
        try:checked(cp)
        except ValueError:check('guard_rejections',True)
        else:raise ValueError('float packet mutation accepted')
    for mode in MODES:
        for L in ((0,1,2,10**100+1) if mode=='natural' else (-10**100-1,-3,-2,-1,0,1,2,10**100+1)):
            p=build_atom(mode,materialize_truth=True);x={'L':L,**canonical(mode,L)}
            v=evaluate(p,x);check('large_canonical_truth',v=={'penalty':0,'truth':int(L%2==0)})
            old=restore_parent(p,x)
            check('parent_zero_restoration',old['qp']*old['qm']==0 and L-2*(old['qp']-old['qm'])-old['b']==0 and old['b']+old['h']==1)
            for name in p['witnesses']:
                y=dict(x);y[name]+=1
                check('single_coordinate_false_witness',evaluate(p,y)['penalty']>0)
            for bad in (True,1.0,-1):
                y=dict(x);y[p['witnesses'][0]]=bad
                try:evaluate(p,y)
                except ValueError:check('guard_rejections',True)
                else:raise ValueError('bad witness accepted')
    for mode in MODES:
        for L1,L2 in itertools.product((0,1,2,3,4,5),repeat=2):
            values={**{'a_'+k:v for k,v in canonical(mode,L1).items()},**{'b_'+k:v for k,v in canonical(mode,L2).items()},'a_L':L1,'b_L':L2}
            z=int(not(L1%2==0 and L2%2==0))
            for variant in VARIANTS:
                p=build_nand(mode,variant=variant);x={**values,**({'z':z} if variant in ('relation','accepted') else {})}
                expected=True if variant=='relation' else bool(z)
                check('complete_NAND_truth',(_eval(p,x)['penalty']==0)==expected)
    # Arbitrary complete NAND tuples: no legality oracle or canonical witness is used.
    for mode in MODES:
        for variant in VARIANTS:
            p=build_nand(mode,variant=variant)
            for _ in range(300):
                x={k:rng.randrange(5) for k in p['witnesses']}
                x.update({k:rng.randrange(0 if mode=='natural' else -9,10) for k in p['inputs']})
                expected=True
                for prefix in ('a_','b_'):
                    L=x[prefix+'L'];bit=x[prefix+'b'];q=x[prefix+'q'] if mode=='natural' else x[prefix+'qp']-x[prefix+'qm']
                    expected &= bit==L%2 and q==L//2
                    if mode=='signed_canonical':expected &= x[prefix+'qp']*x[prefix+'qm']==0
                z=int(not(x['a_L']%2==0 and x['b_L']%2==0))
                expected &= (x['z']==z if variant=='relation' else (x['z']==z==1 if variant=='accepted' else z==1))
                value=_eval(p,x)['penalty']
                check('arbitrary_complete_NAND_fibers',value>=0 and (value==0)==expected)
    # Exact rational/signed/private-port counterexamples are algebra, not supported inputs.
    half=sp.Rational(1,2)
    check('real_false_bit_counterexample',_eval(build_atom(),{'L':0,'qp':0,'qm':0,'b':half})['penalty']==0)
    check('natural_real_false_bit_counterexample',_eval(build_atom('natural'),{'L':1,'q':0,'b':half})['penalty']==0)
    check('signed_helpers_break_canonical',_eval(build_atom('signed_canonical'),{'L':3,'qp':1,'qm':-1,'b':0})['penalty']==0)
    check('real_negative_counterexample',_eval(build_atom(),{'L':0,'qp':0,'qm':0,'b':sp.Rational(1,4)})['penalty']==-sp.Rational(1,8))
    check('negative_input_natural_variant_missing',all(_eval(build_atom('natural'),{'L':-1,'q':q,'b':b})['penalty']>0 for q,b in itertools.product(range(8),repeat=2)))
    check('private_quotient_counterexample',_eval(build_atom(),{'L':0,'qp':1,'qm':1,'b':0})['penalty']==0 and _eval(build_atom('signed_canonical'),{'L':0,'qp':1,'qm':1,'b':0})['penalty']==1)
    check('strictly_positive_witness_counterexample',all(_eval(build_atom(),{'L':0,'qp':qp,'qm':qm,'b':b})['penalty']>0 for qp,qm,b in itertools.product(range(1,5),repeat=3)))
    # Packet/canonical builders have no public cached dictionary to poison.
    p=build_atom();p['gates'][0][1]='add';check('defensive_builds',checked(build_atom())==build_atom())
    for call in (lambda:build_atom(True),lambda:build_atom(materialize_truth=1),lambda:build_nand(variant=False),lambda:canonical('natural',-1),lambda:canonical('signed_canonical',2,offset=1),lambda:restore_parent(build_atom(),{'L':0,'qp':1,'qm':0,'b':0})):
        try:call()
        except ValueError:check('guard_rejections',True)
        else:raise ValueError('invalid public call accepted')
    return {'status':'PASS','source_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
            'parent_sha256':PARENT_SHA,'counts':counts,'packets':packets,
            'scope':'Fixed parity only, already evaluated inputs, natural witnesses. Signed existential variant has infinite fibers; signed canonical and natural variants have unique atom fibers. Truth materialization is charged when emitted. No whole-real-orthant or unrestricted-interface substitution, optimum, or global universal-operation claim.'}


def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--parent',required=True,type=Path);p.add_argument('--output',required=True,type=Path);p.add_argument('--expect',type=Path);a=p.parse_args()
    out=verify(a.parent)
    if a.expect:need(exact(out,json.loads(a.expect.read_text())),'receipt mismatch')
    a.output.write_text(json.dumps(out,sort_keys=True,indent=2)+'\n');print(json.dumps(out['counts'],sort_keys=True))
if __name__=='__main__':main()
