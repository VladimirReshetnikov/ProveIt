#!/usr/bin/env python3
"""Exact symbolic homogeneous leaders for bounded correction obstruction."""
import hashlib
import json
from pathlib import Path

ROOT=Path(__file__).resolve().parents[2]
PATH=ROOT/'research/current2011-sheared72-46-candidate/polynomial.json'
if hashlib.sha256(PATH.read_bytes()).hexdigest()!='cfb30017781968c87e1fa7cba5d08a69b555a7c058ddb1e36b313c74b519e78f': raise RuntimeError('graph pin changed')
g=json.loads(PATH.read_bytes()); names=g['witnesses']+g['fixed_numerals']; weight=[1]*len(g['witnesses'])+[0]*len(g['fixed_numerals']); size=len(names)
zero=(0,)*size; KEEP=8; LIMIT=100000

def degree(m): return sum(a*b for a,b in zip(m,weight))
def trimmed(d,lost):
 d={m:c for m,c in d.items() if c}
 if not d:
  if lost>=0: raise RuntimeError('cancellation obscures exact leader')
  return {},-1
 top=max(map(degree,d)); floor=top-KEEP+1
 removed=[degree(m) for m in d if degree(m)<floor]
 lost=max([lost]+removed)
 d={m:c for m,c in d.items() if degree(m)>=floor}
 if lost>=top: raise RuntimeError('omitted terms could affect leader')
 if len(d)>LIMIT: raise RuntimeError('symbolic support guard')
 return d,lost
def literal(n): return ({zero:n} if n else {}),-1
def plus(a,b,sgn=1):
 d=dict(a[0])
 for m,c in b[0].items(): d[m]=d.get(m,0)+sgn*c
 return trimmed(d,max(a[1],b[1]))
def times(a,b):
 if not a[0] or not b[0]: return {},-1
 da=max(map(degree,a[0])); db=max(map(degree,b[0]))
 loss=max(a[1]+db if a[1]>=0 else -1,b[1]+da if b[1]>=0 else -1)
 d={}
 for x,c in a[0].items():
  for y,e in b[0].items():
   m=tuple(a+b for a,b in zip(x,y)); d[m]=d.get(m,0)+c*e
 if len(d)>LIMIT*4: raise RuntimeError('symbolic multiplication guard')
 return trimmed(d,loss)
def leader(a):
 if not a[0]: return {},-1
 top=max(map(degree,a[0])); return ({m:c for m,c in a[0].items() if degree(m)==top},-1)
def power(a,n):
 z=literal(1)
 for _ in range(n): z=times(z,a)
 return z
def product(*xs):
 z=literal(1)
 for x in xs: z=times(z,x)
 return z

env={}
for j,name in enumerate(names):
 m=[0]*size;m[j]=1;env[name]=({tuple(m):1},-1)
def get(x): return env[x] if isinstance(x,str) else literal(x)
max_support=1
for out,op,left,right in g['source']:
 if out in ('N02','Na2','strong2','rQW2','P2','sum1','sum2','sum3','polynomial'): continue
 a,b=get(left),get(right)
 env[out]=times(a,b) if op=='*' else plus(a,b,1 if op=='+' else -1)
 max_support=max(max_support,len(env[out][0]))

E=leader(env['E']); Y=leader(env['Y']); k=leader(env['k']); f=env['f']; T=env['T']; y=env['y']; i=env['i']; gamma=env['gamma']; W=leader(env['Nt'])
predP=product(literal(-1),power(E,2),power(k,2),power(Y,2))
predH=product(power(i,2),power(k,4),power(Y,4))
predQW=product(literal(8),gamma,power(E,2),k,Y,W)
predU=product(literal(-2),power(E,2),power(f,4),k,Y,T,y)
checks={}
for node,expected,deg in [('N0',predP,22),('strong_residual',predH,22),('rQW',predQW,20),('Na',predU,23)]:
 actual=leader(env[node]); checks[node]={'degree':max(map(degree,actual[0])),'terms':len(actual[0])}
 if actual[0]!=expected[0] or checks[node]['degree']!=deg: raise RuntimeError('leader mismatch: '+node)
print(json.dumps({'scope':'exact symbolic leaders with tracked discarded-degree ceilings; not a Lean proof',
 'graph_sha256':hashlib.sha256(PATH.read_bytes()).hexdigest(),'leaders':checks,
 'kept_degree_layers':KEEP,'max_retained_support':max_support},indent=2,sort_keys=True))
