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
c=json.loads(pin(P/'candidate.json','970b279d7e1a5d063c5e9b842fa92cb8a53827738bfa5af8ba42d93a36d97e7e'))
n=json.loads(pin(P/'natural-candidate.json','ef393ed2e2309e7c121c6fe90e91e5118cd2db9f39c9f13cb9372e9560508f01'))
assert c['parent_sha256']==hashlib.sha256(pr).hexdigest() and len(c['witnesses'])==20 and c['operations']==len(c['source'])==103
assert c['witnesses']==p['witnesses'] and c['fixed_numerals']==p['fixed_numerals'] and c['output']==p['output']
assert n['positive_parent_sha256']==hashlib.sha256((P/'candidate.json').read_bytes()).hexdigest()
ren={x:'n_'+x for x in c['witnesses']};rep=lambda x:'shift_'+x if isinstance(x,str) and x in ren else x
assert n['witnesses']==list(ren.values())
assert n['source']==[['shift_'+x,'+',ren[x],1] for x in c['witnesses']]+[[x,o,rep(a),rep(b)] for x,o,a,b in c['source']]
assert n['operations']==len(n['source'])==123 and n['output']==c['output'] and n['fixed_numerals']==c['fixed_numerals']
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
res=['A0', 'A1', 'auxResidual', 'g72', 'rankDifference', 'ellDifference', 'cSquareDifference', 'zDifference', 'dDifference', 'vDifference', 'deltaDifference']
base={x:var(x) for x in c['witnesses']+c['fixed_numerals']}
pe=ev(p,res,dict(base));ce=ev(c,res,dict(base));assert all(pe[x]==ce[x] for x in res)
for g in (p,c):
 z=ev(g,[g['output']],{x:var(x) for x in res})[g['output']]
 assert z=={(x,x):1 for x in res}
w=set(c['witnesses']);degree=lambda poly:max((sum(x in w for x in mon) for mon in poly),default=-1)
degrees={r:degree(ce[r]) for r in res};assert max(degrees.values())*2==14
print(json.dumps({'scope':'all-port exact polynomial identity, inherited degree certificate and proof boundaries; no Lean','positive':{'variables':20,'operations':103,'degree':14,'counts':pc},'natural_shift':{'variables':20,'operations':123,'degree':14,'counts':nc},'all_residuals_equal':True,'output_identical':True,'residual_degrees':degrees,'lean_elaboration':False},sort_keys=True,indent=2))
