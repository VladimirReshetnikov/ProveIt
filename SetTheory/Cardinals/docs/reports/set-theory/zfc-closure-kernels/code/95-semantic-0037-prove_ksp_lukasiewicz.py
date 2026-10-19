#!/usr/bin/env python3
"""Emit and independently replay a K/S/Peirce proof of the old L schema.

Only substitution instances of K, S and Peirce and modus ponens remain in
the exported DAG.  The proof generator uses the ordinary deduction theorem;
the certificate checker does not trust the generator or that theorem.
"""
from functools import cache
import json
from pathlib import Path

def C(a,b):return ('C',a,b)
def K(a,b):return C(a,C(b,a))
def S(a,b,c):return C(C(a,C(b,c)),C(C(a,b),C(a,c)))
def P(a,b):return C(C(C(a,b),a),a)
def pretty(x):
    return x if isinstance(x,str) else '('+pretty(x[1])+' -> '+pretty(x[2])+')'

nodes=[]
lookup={}

def add(rule,parameters=(),premises=(),conclusion=None):
    key=rule,tuple(parameters),tuple(premises),conclusion
    if key not in lookup:
        lookup[key]=len(nodes)
        nodes.append(dict(rule=rule,parameters=tuple(parameters),premises=tuple(premises),conclusion=conclusion))
    return lookup[key]

def ax(rule,*parameters):
    return add(rule,parameters,conclusion=dict(K=K,S=S,P=P)[rule](*parameters))

def assumption(f):return add('assumption',conclusion=f)

def mp(major,minor):
    f,g=nodes[major]['conclusion'],nodes[minor]['conclusion']
    assert isinstance(f,tuple) and f[0]=='C' and f[1]==g
    return add('MP',premises=(major,minor),conclusion=f[2])

@cache
def identity(a):
    return mp(mp(ax('S',a,C(a,a),a),ax('K',a,C(a,a))),ax('K',a,a))

@cache
def support(p):
    node=nodes[p]
    if node['rule']=='assumption':return frozenset((node['conclusion'],))
    return frozenset().union(*(support(q) for q in node['premises']))

@cache
def discharge(a,p):
    node=nodes[p]
    f=node['conclusion']
    if node['rule']=='assumption' and f==a:return identity(a)
    if a not in support(p):return mp(ax('K',f,a),p)
    if node['rule']=='MP':
        major,minor=node['premises']
        bb=nodes[minor]['conclusion']
        return mp(mp(ax('S',a,bb,f),discharge(a,major)),discharge(a,minor))
    return mp(ax('K',f,a),p)

def make_proof():
    a,b,c,u='a','b','c','u'
    h=C(C(c,u),a)
    k=C(a,c)
    g=C(c,u)
    cg=mp(assumption(k),mp(assumption(h),assumption(g)))
    g_to_c=discharge(g,cg)
    c_proof=mp(ax('P',c,u),g_to_c)
    b_to_c=mp(ax('K',c,b),c_proof)
    out=discharge(h,discharge(k,b_to_c))
    goal=C(h,C(k,C(b,c)))
    assert nodes[out]['conclusion']==goal
    active=set()
    def visit(i):
        if i in active:return
        active.add(i)
        for q in nodes[i]['premises']:visit(q)
    visit(out)
    order=sorted(active)
    remap={old:new for new,old in enumerate(order)}
    result=[]
    for old in order:
        node=nodes[old].copy()
        assert node['rule']!='assumption'
        node['premises']=[remap[x] for x in node['premises']]
        node['pretty']=pretty(node['conclusion'])
        result.append(node)
    return dict(theorem='((c -> u) -> a) -> ((a -> c) -> (b -> c))',
                final=remap[out],nodes=result)

def freeze(x):return tuple(freeze(a) for a in x) if isinstance(x,list) else x

def check(certificate):
    conclusions=[]
    counts={}
    for i,row in enumerate(certificate['nodes']):
        rule=row['rule']
        f=freeze(row['conclusion'])
        args=freeze(row['parameters'])
        premises=row['premises']
        if rule in ('K','S','P'):
            assert premises==[]
            assert f==dict(K=K,S=S,P=P)[rule](*args)
        elif rule=='MP':
            assert len(premises)==2 and all(0<=p<i for p in premises)
            major,minor=(conclusions[p] for p in premises)
            assert major==C(minor,f)
        else:raise AssertionError('Not a permitted proof rule: '+rule)
        conclusions.append(f)
        counts[rule]=counts.get(rule,0)+1
    a,b,c,u='a','b','c','u'
    assert conclusions[certificate['final']]==C(C(C(c,u),a),C(C(a,c),C(b,c)))
    return dict(status='PASS',proof_nodes=len(conclusions),rule_counts=counts,
                assumptions=0,arbitrary_formula_metavariables=['a','b','c','u'])

def main():
    base=Path(__file__).resolve().parent
    certificate=make_proof()
    path=base/'ksp_to_lukasiewicz.json'
    path.write_text(json.dumps(certificate,indent=2)+'\n')
    result=check(json.loads(path.read_text()))
    (base/'ksp_to_lukasiewicz_check.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))

if __name__=='__main__':main()
