#!/usr/bin/env python3
"""Five-natural-witness congruence atoms with a literal charged circuit.

L is an already evaluated signed affine input. The modulus d>=1 is fixed.
No cost of evaluating L or the outer Boolean compiler is suppressed into21.
The21 count refers only to this five-residual sum of squares.
"""
from __future__ import annotations
import argparse, hashlib, itertools, json
from pathlib import Path
import random


def exact(a,b):
    if type(a) is not type(b):return False
    if isinstance(a,dict):return a.keys()==b.keys() and all(exact(a[k],b[k]) for k in a)
    if isinstance(a,(list,tuple)):return len(a)==len(b) and all(exact(x,y) for x,y in zip(a,b))
    return a==b


def integer(x):
    if type(x) is not int: raise ValueError('exact integer required')
    return x


def canonical(L,d):
    integer(L);integer(d)
    if d<1:raise ValueError('positive modulus required')
    q,r=divmod(L,d)
    return max(q,0),max(-q,0),int(r>0),max(r-1,0),d-1-r


def residuals(L,d,W):
    canonical(L,d)
    if len(W)!=5 or any(type(x) is not int or x<0 for x in W):raise ValueError('five natural witnesses required')
    qp,qm,b,s,h=W;r=b*(s+1)
    return qp*qm,L-d*(qp-qm)-r,r+h-(d-1),b*(b-1),(1-b)*s


def build(d,baseline=False):
    integer(d)
    if d<1:raise ValueError('positive modulus required')
    gates=[]
    def op(kind,a,b):
        name='g'+str(len(gates));gates.append([name,kind,a,b]);return name
    if baseline:
        r0=op('mul','qp','qm')
        q=op('sub','qp','qm');dq=op('mul',d,q)
        r1=op('sub',op('sub','L',dq),'a')
        r2=op('sub',op('add','a','h'),d-1)
        v=op('sub','b',1);r3=op('mul','b',v)
        w=op('add','b',v)
        r4=op('sub',op('sub','a',op('mul',w,'s')),'b')
    else:
        bs=op('mul','b','s');r=op('add',bs,'b')
        v=op('sub','b',1);r0=op('mul','qp','qm')
        q=op('sub','qp','qm');dq=op('mul',d,q)
        r1=op('sub',op('sub','L',dq),r)
        r2=op('sub',op('add',r,'h'),d-1)
        r3=op('mul','b',v);r4=op('sub',bs,'s')
    rows=[r0,r1,r2,r3,r4];squares=[op('mul',r,r) for r in rows];output=squares[0]
    for square in squares[1:]:output=op('add',output,square)
    return dict(inputs=['L','qp','qm','b','s','h']+(['a'] if baseline else []),gates=gates,rows=rows,output=output,
                multiplications=sum(g[1]=='mul' for g in gates),additions=sum(g[1]!='mul' for g in gates),fixed_modulus=d)


def evaluate(circuit,inputs):
    values=dict(inputs)
    def get(v):return v if type(v) is int else values[v]
    for name,kind,a,b in circuit['gates']:
        a,b=get(a),get(b)
        values[name]={'mul':lambda:a*b,'add':lambda:a+b,'sub':lambda:a-b}[kind]()
    return values[circuit['output']],tuple(values[x] for x in circuit['rows'])


def verify():
    import sympy as sp
    counts={}
    def check(key,ok):
        if not ok:raise AssertionError(key)
        counts[key]=counts.get(key,0)+1
    syms=sp.symbols('L qp qm b s h a');env=dict(zip(('L','qp','qm','b','s','h','a'),syms));L,qp,qm,b,s,h,a=syms
    for d in (1,2,7,10**50+3):
        c=build(d);old=build(d,True)
        value,rows=evaluate(c,env);before,oldrows=evaluate(old,env)
        target=[qp*qm,L-d*(qp-qm)-b*(s+1),b*(s+1)+h-d+1,b*(b-1),(b-1)*s]
        check('symbolic_complete_residuals',all(sp.expand(x-y)==0 for x,y in zip(rows,target)))
        check('symbolic_degree_four',sp.Poly(sp.expand(value),*syms).total_degree()==4)
        check('actual_charged_circuit',(c['multiplications'],c['additions'],len(c['gates']))==(9,12,21))
        check('baseline_charged_circuit',(old['multiplications'],old['additions'],len(old['gates']))==(9,13,22))
        baseline=[qp*qm,L-d*(qp-qm)-a,a+h-d+1,b*(b-1),a-(2*b-1)*s-b]
        check('baseline_actual_residuals',all(sp.expand(x-y)==0 for x,y in zip(oldrows,baseline)))
        # Restoration has a nonnegative value at every natural tuple. The last
        # residual reverses sign; the complete SOS is identical on the graph.
        check('restored_last_residual_exact_sign',sp.expand(oldrows[-1].subs(a,b*(s+1))+rows[-1])==0)
        check('complete_graph_SOS_identity',sp.expand(before.subs(a,b*(s+1))-value)==0)
    for d in range(1,9):
        for L in range(-20,21):
            solutions=[]
            for qp,qm in itertools.product(range(23),repeat=2):
                if qp*qm:continue
                for b,s in itertools.product(range(4),range(d+2)):
                    h=d-1-b*(s+1)
                    if h<0:continue
                    W=qp,qm,b,s,h
                    if not any(residuals(L,d,W)):solutions.append(W)
            check('complete_bounded_fiber',solutions==[canonical(L,d)])
    rng=random.Random(61719)
    for _ in range(1000):
        L=rng.randrange(-10**40,10**40);d=rng.randrange(1,10**15)
        W=canonical(L,d);check('large_signed_canonical',not any(residuals(L,d,W)) and 1-W[2]==int(L%d==0))
        inp=dict(zip(('qp','qm','b','s','h'),W));inp['L']=L
        check('actual_circuit_canonical',evaluate(build(d),inp)[0]==0)
        for j in range(5):
            mutated=list(W);mutated[j]+=1
            check('single_coordinate_false_witness',any(residuals(L,d,mutated)))
        signed={k:rng.randrange(-5,6) for k in ('L','qp','qm','b','s','h')}
        x=signed;direct=(x['qp']*x['qm'],x['L']-d*(x['qp']-x['qm'])-x['b']*(x['s']+1),x['b']*(x['s']+1)+x['h']-d+1,x['b']*(x['b']-1),(1-x['b'])*x['s'])
        check('off_zero_circuit_equality',evaluate(build(d),signed)[0]==sum(r*r for r in direct))
    for bad in ((True,2),(0,False),(0,0),(0,2.0)):
        try:canonical(*bad)
        except ValueError:check('invalid_inputs_rejected',True)
        else:raise AssertionError('invalid input accepted')
    return dict(status='PASS',source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),counts=counts,
                witness_count=5,residual_count=5,degree=4,atom_SOS_operations=21,
                schedule=build(7),baseline_schedule=build(7,True),
                compiler_witnesses='2I+5C+G',compiler_residuals='2I+5C+G+1',
                scope='Fixed quantifier-free Presburger predicates; L evaluation, Boolean gates and final accumulation paid separately. One fewer witness per congruence. Literal21 vs displayed22 is a schedule comparison, not a minimum or universal-operation improvement.')

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--output',type=Path);p.add_argument('--expect',type=Path);args=p.parse_args();out=verify()
    if args.expect and not exact(out,json.loads(args.expect.read_text())):raise AssertionError('saved receipt differs')
    if args.output:args.output.write_text(json.dumps(out,indent=2,sort_keys=True)+'\n')
    print(json.dumps(out['counts'],sort_keys=True))
