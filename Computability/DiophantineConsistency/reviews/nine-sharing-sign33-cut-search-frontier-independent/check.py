#!/usr/bin/env python3
import hashlib,json,subprocess,sys
from pathlib import Path
d=Path(__file__).resolve().parents[2];p=d/'research/nine-sharing-sign33-cut-search';sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest()
assert sha(p/'search.py')=='794b8151a4e887649dfba087770851cf7b8ce30686c3b983983e69fdf03b409f' and sha(p/'result.json')=='15ef358b93d3d193f17ba2fe9eb1d148b48f6bb142895724c9d9a5b01c973c8c'
res=json.loads((p/'result.json').read_text());replay=json.loads((Path(__file__).parent/'independent-replay.json').read_text());assert replay['best_witnesses']==33 and replay['iterations']==6000 and replay['distribution']!=res['distribution']
gp=d/'candidates/one-page-padding-staircase-carrier65-2011/polynomial.json';assert sha(gp)=='f1f7611842896806fa9e70ad102c6a0e7aa11747a650968f1c74cb169f0e253e';g=json.loads(gp.read_text());rows=g['source'][:60];cuts=res['best_cuts'];assert len(g['witnesses'])==14 and len(rows)==60 and len(cuts)==19 and res['best_witnesses']==33 and cuts['q2']==1 and 'qm' not in cuts and 'q' not in cuts
assert res['iterations']==6000 and res['random_seed']==20261106 and sum(map(int,res['distribution'].values()))==6000 and min(map(int,res['distribution']))==33
# Independent two-component degree propagation: None means a structurally
# absent component, not a mathematical zero or sign theorem.
def join(*values):
 vals=[v for v in values if v is not None];return max(vals) if vals else None
def prod(a,b):return a+b if a is not None and b is not None else None
env={k:(1,None) for k in g['witnesses']};env.update({k:(0,None) for k in g['fixed_numerals']});ob=[];bound=0;seen=[]
for n,op,l,r in rows:
 def get(x):return (0,None) if type(x) is int else env[x]
 ap,an=get(l);bp,bn=get(r)
 if op=='+':out=(join(ap,bp),join(an,bn))
 elif op=='-':out=(join(ap,bn),join(an,bp))
 elif op=='*':out=(join(prod(ap,bp),prod(an,bn)),join(prod(ap,bn),prod(an,bp)))
 else:raise AssertionError(op)
 degree=join(*out);assert degree is not None and degree<=2,(n,out);bound=max(bound,degree)
 if n in cuts:
  sign=cuts[n];assert sign in (-1,1)
  if (sign==1 and out[1] is not None) or (sign==-1 and out[0] is not None):ob.append([n,sign])
  env[n]=(1,None) if sign==1 else (None,1);seen.append(n)
 else:env[n]=out
assert len(seen)==len(cuts) and set(seen)==set(cuts) and bound==2 and ob==res['unproved_sign_obligations']==[['gap',1],['tau',1],['cTminusR',1],['V2minusY2',-1]]
assert [r[:2] for r in rows[:3]]==[['qm','*'],['q','+'],['q2','*']] and rows[0][2:]==['beta','J'] and rows[1][2:]==['qm',1] and rows[2][2:]==['q','q']
print(json.dumps({'status':'PASS_BEST_DEGREE_WITH_REPRODUCIBILITY_ISSUE','result_sha256':sha(p/'result.json'),'iterations':6000,'observed_best_witnesses':33,'best_cut_count':19,'unproved_sign_obligations':ob,'scope':'Retained and fresh replay differ due set-order hashing; independent structural degree of retained best only; no residual construction, sign proof, model theorem, global lower bound or Lean replay'},indent=2,sort_keys=True))
