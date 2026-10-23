#!/usr/bin/env python3
"""Flatten the authored DAG, not any upstream code, into natural quadratics."""
import json
from pathlib import Path
from collections import defaultdict
from build_stack_step import build
ROOT=Path(__file__).resolve().parent

def add(a,b,scale=1):
    r=dict(a)
    for x,c in b.items():r[x]=r.get(x,0)+scale*c
    return {x:c for x,c in r.items() if c}
def scale(a,c):return {x:v*c for x,v in a.items() if v*c}
def constant(a):return all(x=='' for x in a)
def product(a,b):
    r=defaultdict(int)
    for x,c in a.items():
        for y,d in b.items():r[tuple(sorted(t for t in (x,y) if t))]+=c*d
    return {x:c for x,c in r.items() if c}
def linear(a):return {(x,) if x else ():c for x,c in a.items()}
def padd(a,b,sgn=1):
    r=dict(a)
    for m,c in b.items():r[m]=r.get(m,0)+sgn*c
    return {m:c for m,c in r.items() if c}
def pmul(a,b):
    r=defaultdict(int)
    for x,c in a.items():
        for y,d in b.items():r[tuple(sorted(x+y))]+=c*d
    return {m:c for m,c in r.items() if c}
def serial(p):return [{'monomial':list(m),'coefficient':c} for m,c in sorted(p.items())]

def flatten(coefficient_cap=None):
    dag=build();aff=[];nonnegative=[];res=[];wires=[]
    for i,node in enumerate(dag['nodes']):
        op,args=node['op'],node['args']
        if op=='var':a={args[0]:1};pos=True
        elif op=='const':a={'':args[0]};pos=args[0]>=0
        elif op=='add':
            a=add(aff[args[0]],aff[args[1]]);pos=all(nonnegative[j] for j in args)
        elif op=='sub':a=add(aff[args[0]],aff[args[1]],-1);pos=False
        else:
            l,r=(aff[j] for j in args)
            pos=args[0]==args[1] or all(nonnegative[j] for j in args)
            if constant(l):a=scale(r,l.get('',0))
            elif constant(r):a=scale(l,r.get('',0))
            else:
                assert pos,('negative nonlinear wire',i)
                name=f'q{len(wires)}'; a={name:1}
                res.append(padd({(name,):1},product(l,r),-1))
                wires.append({'name':name,'dag_node':i,
                    'nonnegative_reason':'square' if args[0]==args[1] else 'product_of_nonnegative',
                    'left':l,'right':r})
        if coefficient_cap is not None and op not in ('var','const') and pos and max(map(abs,a.values()),default=0)>coefficient_cap:
            name=f'q{len(wires)}'
            res.append(padd({(name,):1},linear(a),-1))
            wires.append({'name':name,'dag_node':i,'nonnegative_reason':'nonnegative_affine', 'affine':a})
            a={name:1}
        aff.append(a);nonnegative.append(pos)
    res.append(linear(aff[dag['output']]))
    quartic={}
    for p in res:quartic=padd(quartic,pmul(p,p))
    return {'schema':'sparse-natural-quadratic-system-v1',
      'meaning':'local transition source ONLY; not complete consistency equation',
      'exposed_state_coordinates':dag['state_inputs']+dag['state_outputs'],
      'base_witnesses':dag['existential_witnesses'],
      'wire_witnesses':wires,'witness_count':len(wires)+len(dag['existential_witnesses']),
      'quadratic_residuals':[serial(p) for p in res],
      'quartic_sum_of_squares':serial(quartic),
      'metrics':{'affine_coefficient_cap':coefficient_cap,'wire_count':len(wires),'residual_count':len(res),
        'quartic_monomials':len(quartic),'exact_degree':max(map(len,quartic)),
        'maximum_quartic_coefficient_magnitude':max(map(abs,quartic.values())),
        'maximum_residual_coefficient_magnitude':max(abs(c) for p in res for c in p.values()),
        'largest_constant_in_dag':4}}
if __name__=='__main__':
    for cap in (None,4,16,64):
        x=flatten(cap);(ROOT/f'stack_step_quartic{str(cap) if cap else ""}.json').write_text(json.dumps(x,indent=2)+'\n')
        print(json.dumps(x['metrics'],indent=2));print('Local witnesses:',x['witness_count'])
