#!/usr/bin/env python3
import hashlib,json,sys,subprocess
from collections import Counter
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site and not sys.flags.optimize
root=Path(__file__).resolve().parents[2];pkg=root/'research/current14-carrier65-unscaled-tail-search';p=root/'candidates/one-page-padding-staircase-carrier65-2011/polynomial.json';q=root/'research/current2011-unscaled66/polynomial.json';sha=lambda x:hashlib.sha256(x.read_bytes()).hexdigest()
assert sha(p)=='f1f7611842896806fa9e70ad102c6a0e7aa11747a650968f1c74cb169f0e253e' and sha(q)=='bf9e05905fe84f74edade75ba7d373bd6955aa035867af89a6026d9a21719e75' and sha(pkg/'search.py')=='9fbddeaacc13b615014046c2fbb47880d21bfb18cb9739326699eacb6d453b7c'
a,b=json.loads(p.read_text()),json.loads(q.read_text());assert a['source'][:51]==b['source'][:51] and len(a['source'])==65 and len(b['source'])==66
n=9;z=(0,)*n;one={z:1}
def var(i):return {tuple(int(j==i) for j in range(n)):1}
def add(x,y,sign=1):
 r=dict(x)
 for k,v in y.items():r[k]=r.get(k,0)+sign*v
 return {k:v for k,v in r.items() if v}
def mul(x,y):
 r={}
 for a,c in x.items():
  for b,d in y.items():
   k=tuple(u+v for u,v in zip(a,b));r[k]=r.get(k,0)+c*d
 return {k:v for k,v in r.items() if v}
n0,n1,nt,delta,i,c2,f2,v,y=map(var,range(n));env0={'N0':n0,'N1':n1,'Nt':nt,'Delta':delta,'i':i,'c2':c2,'Dc2':mul(delta,c2),'f2':f2,'V':v,'y':y,1:one}
def suffix(g):
 env=env0.copy()
 for name,op,l,r in g['source'][51:]:
  assert name not in env and l in env and r in env
  env[name]=mul(env[l],env[r]) if op=='*' else add(env[l],env[r],1 if op=='+' else -1)
 return env[g['output']]
old,new=suffix(a),suffix(b);assert old==mul(delta,new) and len(old)==len(new)==7
# Independently enumerate multiplication DAG states, not recursive tree-union sets.
atoms=frozenset(((1,0,0),(0,1,0),(0,0,1),(1,0,1)));targets={(1,2,2),(2,2,2)};limit=(2,2,2);states={atoms};found=None
for level in range(5):
 if any(targets<=state for state in states):found=level;break
 nxt=set()
 for state in states:
  for x in state:
   for y in state:
    w=tuple(i+j for i,j in zip(x,y))
    if w not in state and all(w[i]<=limit[i] for i in range(3)):nxt.add(state|{w})
 states=nxt
assert found==4
w=[(0,1,1),(0,2,1),(1,2,2),(2,2,2)];state=set(atoms)
for t in w:
 assert any(tuple(a[i]+b[i] for i in range(3))==t for a in state for b in state);state.add(t)
assert targets<=state
for g,num in ((a,65),(b,66)):
 deps={x[0]:(x[2],x[3]) for x in g['source']};seen=set();todo=[g['output']]
 while todo:
  x=todo.pop()
  if x in deps and x not in seen:seen.add(x);todo.extend(deps[x])
 assert len(seen)==num
r=json.loads((pkg/'result.json').read_text());assert r['minimum_new_multiplications']==4 and r['minimum_witness_exponent_vectors']==[list(x) for x in w] and r['strong_minimal_circuits']==20 and r['aux_minimal_circuits']==67 and r['candidate_unions']==1121
out=subprocess.run([sys.executable,'-I','-S','-B',str(pkg/'search.py')],capture_output=True,text=True,check=True,timeout=120);assert not out.stderr and json.loads(out.stdout)==r
print(json.dumps({'status':'PASS_INDEPENDENT_EXTERNAL_AUDIT','scope':'exact suffix identity with independent N0/N1/Nt and exhaustive multiplication-DAG minimum 4 under stated atoms; no global circuit lower bound or Lean'},indent=2))
