#!/usr/bin/env python3
"""Exact sparse-polynomial transfer, source and DAG certificate. No Lean."""
from pathlib import Path
from collections import Counter
import hashlib,json,re,sys
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
P=Path(__file__).resolve().parent;D=P.parents[1]
def pin(path,digest):
 b=path.read_bytes();assert hashlib.sha256(b).hexdigest()==digest,path;return b
pr=pin(D/'research/adaptive-aq20-substituted-scales104/candidate.json','e21601ed2d0a17aa72ad1bbe103122337ecf98455cf39d9e97a22883d1c9ab50');p=json.loads(pr)
c=json.loads(pin(P/'candidate.json','624cc7848f1f36db2d35f5fdfc37111e36ab8e3e8c0ee71553c4fda6739de4fc'))
n=json.loads(pin(P/'natural-candidate.json','6c454d2bb25bc2226ffc0b23cebd5ea7aa271e3002f3c476ca16a568db7e6b59'))
assert c['parent_sha256']==hashlib.sha256(pr).hexdigest() and len(c['witnesses'])==17 and c['operations']==len(c['source'])==95
assert n['positive_parent_sha256']==hashlib.sha256((P/'candidate.json').read_bytes()).hexdigest()
ren={x:'n_'+x for x in c['witnesses']};rep=lambda x:'shift_'+x if isinstance(x,str) and x in ren else x
assert n['witnesses']==list(ren.values())
assert n['source']==[['shift_'+x,'+',ren[x],1] for x in c['witnesses']]+[[x,o,rep(a),rep(b)] for x,o,a,b in c['source']]
assert n['operations']==len(n['source'])==112 and n['output']==c['output'] and n['fixed_numerals']==c['fixed_numerals']
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
res=['A0','A1','auxResidual','g72','rankDifference','zDifference','dDifference','vDifference']
base={x:var(x) for x in c['witnesses']+c['fixed_numerals']}
ce=ev(c,res+['ell','c2','DeltaComputed'],dict(base));pbase=dict(base);pbase['ellVariable']=ce['ell'];pbase['cSquareVariable']=ce['c2'];pbase['deltaVariable']=ce['DeltaComputed']
removed=['ellDifference','cSquareDifference','deltaDifference'];pe=ev(p,res+removed,pbase)
assert all(pe[x]=={} for x in removed) and all(pe[x]==ce[x] for x in res)
for g,terms in ((p,res+removed),(c,res)):
 z=ev(g,[g['output']],{x:var(x) for x in terms})[g['output']]
 assert z=={(x,x):1 for x in terms}
w=set(c['witnesses']);degree=lambda poly:max((sum(x in w for x in mon) for mon in poly),default=-1)
degrees={r:degree(ce[r]) for r in res};assert max(degrees.values())==10
m=tuple(sorted(['Y']*4+['eta']*4+['i']*2))
assert ce['g72'].get(m)==1
assert not any(tuple(x for x in mon if x in w)==m and tuple(x for x in mon if x not in w) for mon in ce['g72'])
print(json.dumps({'scope':'exact all-port residual substitution; positivity arguments separately documented; no Lean', 'positive':{'variables':17,'operations':95,'degree':20,'counts':pc},'natural_shift':{'variables':17,'operations':112,'degree':20,'counts':nc},'remaining_8_residuals_equal':True,'three_binding_residuals_zero':True,'sum_wiring_checked':True,'residual_degrees':degrees,'leading_witness':'g72 has Y^4 eta^4 i² coefficient 1 for all ports','lean_elaboration':False},sort_keys=True,indent=2))
