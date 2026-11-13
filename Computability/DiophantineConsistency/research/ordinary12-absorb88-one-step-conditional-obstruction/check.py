#!/usr/bin/env python3
"""Check one finite first-factor example of the conditional one-step map."""
import hashlib
import json
from pathlib import Path


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


path = Path(__file__).resolve().parent.parent / 'ordinary12-absorb88-probe' / 'graph-dag.json'
data = path.read_bytes()
require(hashlib.sha256(data).hexdigest() == '84a9a529636d6cadcf0f0c673c0728aa7b6fcbc0e2f2ac562a377553de831b25', 'graph drift')
graph = json.loads(data)


def evaluate(F, alpha, r):
    v = {i:i for i in range(5)}
    v.update({name:1 for name in graph['witnesses']+graph['fixed_numerals']})
    v.update(beta=3,K0=1,MC=0,MF=0,F=F,alpha=alpha,r=r)
    for name, op, x, y in graph['source']:
        left, right = v[x], v[y]
        if op == '+':
            v[name] = left+right
        elif op == '-':
            v[name] = left-right
        elif op == '*':
            v[name] = left*right
        else:
            raise RuntimeError(f'unknown operation: {op}')
    return v


tau = 32769
old = evaluate(1,1,32797)
new = evaluate(2,4,32713)
b,q,A = old['qm'],old['q'],old['K0']+old['w']
D = q*(q*A+1)
require((b,q,A,D)==(3,4,2,36), 'base registers')
require((A+1)%b==0, 'additional divisibility')
require(old['Bt']==12 and 0<old['Bt']<D, 'old transport')
require(old['Bt']%b==0 and D%b==0, 'transport divisibilities')
u=(D-old['Bt'])//b
require(u==8 and new['Bt']==-b*u, 'new transport')
require(tau*tau==1+old['ell']*(old['ell']+old['k']), 'first Pell norm')
require(new['r']==tau-(b*old['k']+1)*u and new['r']>0, 'new first-root witness')
require(old['A0']==new['A0']==0, 'first residuals')
require(old['G']==new['G']==10, 'preserved G')
require(old['A1']==new['A1'] and old['N']==new['N'], 'preserved other residuals')
require(new['F']<q and new['alpha']<=b*b, 'b-step guard is impossible')
require(old['A1']!=0 and old['N']!=0 and old['P12']>0 and new['P12']>0, 'not full graph zeros')
print(json.dumps({'status':'PASS', 'graph_sha256':hashlib.sha256(data).hexdigest(),
  'scope':'finite first-factor illustration only; neither tuple is a full graph zero',
  'old':{x:old[x] for x in ('F','alpha','r','G','Bt','A0')},
  'new':{x:new[x] for x in ('F','alpha','r','G','Bt','A0')},
  'b':b,'q':q,'A':A,'D':D,'u':u,
  'main_residual_unchanged_and_nonzero':True,
  'ordinary_residual_unchanged_and_nonzero':True},indent=2,sort_keys=True))
