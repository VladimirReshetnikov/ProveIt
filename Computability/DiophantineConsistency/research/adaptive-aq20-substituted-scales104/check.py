#!/usr/bin/env python3
"""Exact sparse-polynomial transfer, source and DAG certificate. No Lean."""
from pathlib import Path
from collections import Counter
import hashlib,json,re,sys
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
P=Path(__file__).resolve().parent;D=P.parents[1]
def pin(path,digest):
 b=path.read_bytes();assert hashlib.sha256(b).hexdigest()==digest,path;return b
pr=pin(D/'research/adaptive-aq22-two-quotients110/candidate.json','b82ef3f8e45cc260d8ffee26f3f8fa7ef2f207834829aee1a5ac357fcab0ffc1');p=json.loads(pr)
c=json.loads(pin(P/'candidate.json','e21601ed2d0a17aa72ad1bbe103122337ecf98455cf39d9e97a22883d1c9ab50'))
n=json.loads(pin(P/'natural-candidate.json','f24f0d1adefd50c3ebe93cc0f4d1289f84e47e3ce479e88e5c9db4fdaef1485f'))
mask=pin(D/'Lean/DiophantineConsistency/CurrentMaskData2011.lean','8e92c1f507bc250c31fb2671a921dfbef7a44ba643956f962cd64d9b50bd4582').decode()
kernel=pin(D/'Lean/DiophantineConsistency/CurrentKernelData2011.lean','529b2f89e4e93516a8a52343d98dc749c57f5a967d8ef522b92373bf3adf0a2c').decode()
positive=pin(D/'Lean/DiophantineConsistency/CurrentMasks2011.lean','403f35c26ffd2d94e4a29af8c826cfa0874ac8f2281bb673c1347989e7d48cea').decode()
assert 'def ports (K : ℤ) : Fin 4 → ℤ := ![beta, K, lowPort, highPort + beta]' in mask
assert 'def ports : Fin 4 → ℤ := CurrentMasks2011.ports (K : ℤ)' in kernel
assert 'theorem beta_pos_int : (0 : ℤ) < (beta : ℤ)' in positive
assert c['parent_sha256']==hashlib.sha256(pr).hexdigest() and len(c['witnesses'])==20 and c['operations']==len(c['source'])==104
assert n['positive_parent_sha256']==hashlib.sha256((P/'candidate.json').read_bytes()).hexdigest()
ren={x:'n_'+x for x in c['witnesses']};rep=lambda x:'shift_'+x if isinstance(x,str) and x in ren else x
assert n['witnesses']==list(ren.values())
assert n['source']==[['shift_'+x,'+',ren[x],1] for x in c['witnesses']]+[[x,o,rep(a),rep(b)] for x,o,a,b in c['source']]
assert n['operations']==len(n['source'])==124 and n['output']==c['output'] and n['fixed_numerals']==c['fixed_numerals']
def live(g):
 seen=set(g['witnesses']+g['fixed_numerals']);nodes={}
 for name,op,a,b in g['source']:
  assert name not in seen and op in '+-*' and all(isinstance(x,int) or x in seen for x in (a,b)),name
  nodes[name]=(a,b);seen.add(name)
 active={g['output']}; todo=[g['output']]
 while todo:
  for x in nodes.get(todo.pop(),()):
   if isinstance(x,str) and x not in active:active.add(x);todo.append(x)
 assert set(nodes)|set(g['witnesses'])|set(g['fixed_numerals'])<=active
 return dict(sorted(Counter(r[1] for r in g['source']).items()))
pc=live(c);nc=live(n)
def con(n):return {():n} if n else {}
def var(n):return {(n,):1}
def add(a,b,s=1):
 out=dict(a)
 for m,v in b.items():out[m]=out.get(m,0)+s*v
 return {m:v for m,v in out.items() if v}
def mul(a,b):
 out={}
 for x,v in a.items():
  for y,w in b.items():
   z=tuple(sorted(x+y));out[z]=out.get(z,0)+v*w
 return {m:v for m,v in out.items() if v}
def ev(g,targets,env):
 rows={r[0]:r for r in g['source']};need=set(targets);todo=list(targets)
 while todo:
  t=todo.pop()
  if t in rows and t not in env:
   for x in rows[t][2:]:
    if isinstance(x,str) and x not in need:need.add(x);todo.append(x)
 for name,op,a,b in g['source']:
  if name not in need or name in env:continue
  a=con(a) if isinstance(a,int) else env[a];b=con(b) if isinstance(b,int) else env[b]
  env[name]=mul(a,b) if op=='*' else add(a,b,1 if op=='+' else -1)
 return env
res=['A0','A1','auxResidual','g72','rankDifference','ellDifference','cSquareDifference','zDifference','dDifference','vDifference','deltaDifference']
base={x:var(x) for x in c['witnesses']+c['fixed_numerals']}
ce=ev(c,res+['M','U'],dict(base));pbase=dict(base);pbase['scaleVariable']=ce['M'];pbase['mainScaleVariable']=ce['U']
pe=ev(p,res+['scaleDifference','mainScaleDifference'],pbase)
assert pe['scaleDifference']=={} and pe['mainScaleDifference']=={}
assert all(pe[x]==ce[x] for x in res)
for g,terms in ((p,res+['scaleDifference','mainScaleDifference']),(c,res)):
 z=ev(g,[g['output']],{x:var(x) for x in terms})[g['output']]
 assert z=={(x,x):1 for x in terms}
w=set(c['witnesses']);degree=lambda poly:max((sum(x in w for x in mon) for mon in poly),default=-1)
degrees={r:degree(ce[r]) for r in res};assert max(degrees.values())==7
cert=[]
for r in res:
 for mon,coefficient in ce[r].items():
  wm=tuple(x for x in mon if x in w)
  if len(wm)!=max(degrees.values()):continue
  coeff={tuple(x for x in m if x not in w):v for m,v in ce[r].items() if tuple(x for x in m if x in w)==wm}
  if len(coeff)==1:
   term,val=next(iter(coeff.items()))
   if val and all(x=='beta' for x in term):cert.append((r,wm,val,len(term)))
assert cert
print(json.dumps({'scope':'exact all-port residual substitution; zero maps require beta positive; no Lean', 'positive':{'variables':20,'operations':104,'degree':2*max(degrees.values()),'counts':pc},'natural_shift':{'variables':20,'operations':124,'degree':2*max(degrees.values()),'counts':nc},'remaining_residuals_equal':True,'two_binding_residuals_zero':True,'sum_wiring_checked':True,'residual_degrees':degrees,'leading_witness_coefficient_beta_power':cert[0],'lean_elaboration':False},sort_keys=True,indent=2))
