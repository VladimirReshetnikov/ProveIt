#!/usr/bin/env python3
"""Exact sparse-polynomial transfer, source and DAG certificate. No Lean."""
from pathlib import Path
from collections import Counter
import hashlib,json,re,sys
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
P=Path(__file__).resolve().parent;D=P.parents[1]
def pin(path,digest):
 b=path.read_bytes();assert hashlib.sha256(b).hexdigest()==digest,path;return b
pr=pin(D/'research/adaptive-aq17-factored-root94/candidate.json','7f9a6af2c44f1e9b6c763c9dd38cc4a3beb79d5dcd159539dc7275873e67c71a');p=json.loads(pr)
c=json.loads(pin(P/'candidate.json','ff131760c176ebd56a593aff49523daf384c03322e2ddaae07f65f8f63bb7bac'))
assert c['positive_parent_sha256']==hashlib.sha256(pr).hexdigest() and len(c['witnesses'])==17 and c['operations']==len(c['source'])==105
forced={'f','T','y','firstQuotient','mainQuotient','vValueVariable'};assert c['forced_unshifted']==sorted(forced)
ren={x:'n_'+x for x in p['witnesses']};shifted={x:'shift_'+x for x in p['witnesses'] if x not in forced}
rep=lambda x:shifted.get(x,ren.get(x,x)) if isinstance(x,str) else x
assert c['witnesses']==list(ren.values())
assert c['source']==[['shift_'+x,'+',ren[x],1] for x in p['witnesses'] if x not in forced]+[[x,o,rep(a),rep(b)] for x,o,a,b in p['source']]
assert c['output']==p['output'] and c['fixed_numerals']==p['fixed_numerals']
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
counts=live(c)
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
pbase={x:(var(ren[x]) if x in forced else add(var(ren[x]),con(1))) for x in p['witnesses']}
pbase.update({x:var(x) for x in p['fixed_numerals']})
pe=ev(p,res,pbase);ce=ev(c,res,dict(base));assert all(pe[x]==ce[x] for x in res)
for g in (p,c):
 z=ev(g,[g['output']],{x:var(x) for x in res})[g['output']]
 assert z=={(x,x):1 for x in res}
rows={r[0]:r for r in p['source']}
for r in [['g38','*','firstQuotient','firstQuotient'],['g40','*','ell','g30'],['g30','+','ell','k'],['g41','+','1','g40']]:
 r=[int(x) if isinstance(x,str) and x.isdigit() else x for x in r];assert rows[r[0]]==r
for r in [['E','*','X','Y'],['k','+','eta','zeta'],['kY','*','Y','k'],['c','+','eta','kY'],['c2','*','c','c'],['ell','*','E','kY'],['a','+','E','Y'],['g15','*',4,'a'],['H','+',3,'g15'],['g17','*','a','a'],['DeltaComputed','+','H','g17'],['y2','*','y','y']]:assert rows[r[0]]==r
for r in [['A0','-','g38','g41'],['g61','*','mainQuotient','mainQuotient'],['g63','*','DeltaComputed','c2'],['g64','+',1,'g63'],['A1','-','g61','g64'],['I','*','c2','i'],['g71','*','I','I'],['g72','-','g71','QComputed'],['g80','*','vValueVariable','vValueVariable'],['g81','-','y2','g80'],['g82','*','QComputed','g81'],['Fa','-','y2','g82'],['auxResidual','-','Fa',1],['f2','*','f','f'],['rho','-','f2',1],['QComputed','*','DeltaComputed','rho'],['g74','*','T','c'],['g75','-','g74','rankVariable'],['g76','*','f2','g75'],['VComputed','-','g76','c'],['vDifference','-','vValueVariable','VComputed']]:assert rows[r[0]]==r
w=set(c['witnesses']);degree=lambda poly:max((sum(x in w for x in mon) for mon in poly),default=-1)
degrees={r:degree(ce[r]) for r in res};assert max(degrees.values())==10
m=tuple(sorted(['n_Y']*4+['n_eta']*4+['n_i']*2))
assert ce['g72'].get(m)==1
assert not any(tuple(x for x in mon if x in w)==m and tuple(x for x in mon if x not in w) for mon in ce['g72'])
print(json.dumps({'scope':'exact mixed-shift graph, residuals and positivity-forcing wiring; zero equivalence uses the documented model argument; no Lean','natural':{'variables':17,'operations':105,'degree':20,'counts':counts},'unshifted':sorted(forced),'mixed_substitution_residual_identity':True,'sum_of_eight_squares_checked':True,'residual_degrees':degrees,'leading_witness':'g72 has n_Y^4 n_eta^4 n_i² coefficient 1 for all ports','lean_elaboration':False},sort_keys=True,indent=2))
