#!/usr/bin/env python3
"""Exact sparse-polynomial transfer, source and DAG certificate. No Lean."""
from pathlib import Path
from collections import Counter
import hashlib,json,re,sys
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
P=Path(__file__).resolve().parent;D=P.parents[1]
def pin(path,digest):
 b=path.read_bytes();assert hashlib.sha256(b).hexdigest()==digest,path;return b
pr=pin(D/'research/adaptive-aq17-positive-bindings95/candidate.json','624cc7848f1f36db2d35f5fdfc37111e36ab8e3e8c0ee71553c4fda6739de4fc');p=json.loads(pr)
c=json.loads(pin(P/'candidate.json','7f9a6af2c44f1e9b6c763c9dd38cc4a3beb79d5dcd159539dc7275873e67c71a'))
n=json.loads(pin(P/'natural-candidate.json','30571052ff20a5fac63f6ab1cfb25292e5bdde42972433b21aaa9be5e9b030c2'))
assert c['parent_sha256']==hashlib.sha256(pr).hexdigest() and len(c['witnesses'])==17 and c['operations']==len(c['source'])==94
assert c['witnesses']==p['witnesses'] and c['fixed_numerals']==p['fixed_numerals'] and c['output']==p['output']
assert n['positive_parent_sha256']==hashlib.sha256((P/'candidate.json').read_bytes()).hexdigest()
ren={x:'n_'+x for x in c['witnesses']};rep=lambda x:'shift_'+x if isinstance(x,str) and x in ren else x
assert n['witnesses']==list(ren.values())
assert n['source']==[['shift_'+x,'+',ren[x],1] for x in c['witnesses']]+[[x,o,rep(a),rep(b)] for x,o,a,b in c['source']]
assert n['operations']==len(n['source'])==111 and n['output']==c['output'] and n['fixed_numerals']==c['fixed_numerals']
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
res=['A0', 'A1', 'auxResidual', 'g72', 'rankDifference', 'zDifference', 'dDifference', 'vDifference']
base={x:var(x) for x in c['witnesses']+c['fixed_numerals']}
pe=ev(p,res,dict(base));ce=ev(c,res,dict(base));assert all(pe[x]==ce[x] for x in res)
for g in (p,c):
 z=ev(g,[g['output']],{x:var(x) for x in res})[g['output']]
 assert z=={(x,x):1 for x in res}
w=set(c['witnesses']);degree=lambda poly:max((sum(x in w for x in mon) for mon in poly),default=-1)
degrees={r:degree(ce[r]) for r in res};assert max(degrees.values())*2==20
print(json.dumps({'scope':'all-port exact polynomial identity, inherited degree certificate and proof boundaries; no Lean','positive':{'variables':17,'operations':94,'degree':20,'counts':pc},'natural_shift':{'variables':17,'operations':111,'degree':20,'counts':nc},'all_residuals_equal':True,'output_identical':True,'residual_degrees':degrees,'lean_elaboration':False},sort_keys=True,indent=2))
