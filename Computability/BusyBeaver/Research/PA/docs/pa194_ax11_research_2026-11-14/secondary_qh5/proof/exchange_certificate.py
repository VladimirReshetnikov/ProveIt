#!/usr/bin/env python3
"""Construct and check a parametric K,S,MP certificate for premise exchange.

K and S are inherited derived rules of the unchanged dominated implication
basis. This script checks only the finite exchange derivation; it is neither
an end-to-end PA proof checker nor a Turing-machine simulator.
"""
from dataclasses import dataclass
from functools import lru_cache
import json
import argparse
from pathlib import Path

def imp(a,b):
    return ('I',a,b)

@dataclass(frozen=True)
class Proof:
    rule: str
    formula: object
    data: tuple=()

def var(name,t):
    return Proof('hyp',t,(name,))

def K(a,b):
    return Proof('K',imp(a,imp(b,a)),(a,b))

def S(a,b,c):
    return Proof('S',imp(imp(a,imp(b,c)),imp(imp(a,b),imp(a,c))),(a,b,c))

def mp(major,minor):
    assert isinstance(major.formula,tuple) and major.formula[0]=='I'
    assert major.formula[1]==minor.formula
    return Proof('MP',major.formula[2],(major,minor))

@lru_cache(None)
def free(p):
    if p.rule=='hyp':return frozenset(p.data)
    if p.rule in ('K','S'):return frozenset()
    assert p.rule=='MP'
    return free(p.data[0])|free(p.data[1])

def identity(a):
    return mp(mp(S(a,imp(a,a),a),K(a,imp(a,a))),K(a,a))

@lru_cache(None)
def discharge(name,typ,p):
    if name not in free(p):return mp(K(p.formula,typ),p)
    if p.rule=='hyp':
        assert p.data==(name,) and p.formula==typ
        return identity(typ)
    assert p.rule=='MP'
    major,minor=p.data
    return mp(mp(S(typ,minor.formula,p.formula),
                 discharge(name,typ,major)),discharge(name,typ,minor))

P,Q,R='P','Q','R'
F=imp(P,imp(Q,R))
p=mp(mp(var('f',F),var('p',P)),var('q',Q))
p=discharge('p',P,p)
p=discharge('q',Q,p)
p=discharge('f',F,p)
expected=imp(F,imp(Q,imp(P,R)))
assert p.formula==expected and not free(p)

lines=[]
indices={}
def visit(p):
    if p in indices:return indices[p]
    if p.rule=='MP':
        major,minor=(visit(q) for q in p.data)
        data={'major':major,'minor':minor}
    else:
        assert p.rule in ('K','S')
        data={'parameters':p.data}
    idx=len(lines)
    lines.append(dict(rule=p.rule,formula=p.formula,**data))
    indices[p]=idx
    return idx
last=visit(p)

# Check the serialized certificate through a separate flat replay.
def freeze(x):
    return tuple(map(freeze,x)) if isinstance(x,(tuple,list)) else x
serialized=json.loads(json.dumps(lines))
for i,line in enumerate(serialized):
    f=freeze(line['formula'])
    if line['rule']=='K':
        a,b=map(freeze,line['parameters'])
        assert f==imp(a,imp(b,a))
    elif line['rule']=='S':
        a,b,c=map(freeze,line['parameters'])
        assert f==imp(imp(a,imp(b,c)),imp(imp(a,b),imp(a,c)))
    else:
        assert line['rule']=='MP'
        a,b=line['major'],line['minor']
        assert 0<=a<i and 0<=b<i
        assert freeze(serialized[a]['formula'])==imp(freeze(serialized[b]['formula']),f)
assert freeze(serialized[last]['formula'])==expected

result={'claim':'(P -> (Q -> R)) -> (Q -> (P -> R))',
        'proof_system':'K, S, modus ponens; no quantifier or falsity rule',
        'symbolic':True,'lines':serialized,'conclusion_line':last,
        'assumptions':[],
        'dependency':'K and S are derived from the unchanged restricted rho8 basis; see PA196/Logic/ImplicationBasis.lean'}
p=argparse.ArgumentParser(description=__doc__)
p.add_argument('--output',type=Path,default=Path(__file__).with_name('exchange_certificate.json'))
out=p.parse_args().output
out.write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({'ok':True,'lines':len(lines),'axioms_K':sum(x['rule']=='K' for x in lines),
                  'axioms_S':sum(x['rule']=='S' for x in lines),
                  'modus_ponens':sum(x['rule']=='MP' for x in lines),
                  'conclusion_line':last,'file':str(out)}))
