#!/usr/bin/env python3
"""Exact sparse-polynomial transfer, source and DAG certificate. No Lean."""
from pathlib import Path
from collections import Counter
import hashlib,json,re,sys
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
P=Path(__file__).resolve().parent;D=P.parents[1]
def pin(path,digest):
 b=path.read_bytes();assert hashlib.sha256(b).hexdigest()==digest,path;return b
pr=pin(D/'research/adaptive-square-sums22-degree10/candidate.json','1266b143c5512351739ea2c71fc8e0b8b0e5cecc599392f128c0803ff78ce106');p=json.loads(pr)
c=json.loads(pin(P/'candidate.json','b82ef3f8e45cc260d8ffee26f3f8fa7ef2f207834829aee1a5ac357fcab0ffc1'))
n=json.loads(pin(P/'natural-candidate.json','3a86d13d17522c1d662888dbc5149f61023e34c9d04bb7db4c241818ee9ee0a7'))
s=pin(D/'Lean/DiophantineConsistency/AdaptiveAQ22Literal.lean','7d417cd67cc0d6150e3c122e7c4cca4d5c924b54dafe36885f7b5d9b06cf7b6c').decode()
q=pin(D/'Lean/DiophantineConsistency/ArithmeticAdaptiveQuotients2011.lean','40070b23fceee62a689a1002f97f6f612057634b5bd8472949f0d2dcab136884').decode()
e=pin(D/'Lean/DiophantineConsistency/IPRAAQ22Native.lean','b90a9eb67b6fef945e6f1a3c9900e39e3a07a16dbe032089b3489660e00ce747').decode()
assert re.findall(r'let (\w+) : Expr \(Fin 22\) := \.var (\d+)',s)==[(v,str(i)) for i,v in enumerate(p['witnesses'])]
assert re.findall(r'let (\w+) : Expr \(Fin 22\) := \.constant \(p (\d+)\)',s)==[(v,str(i)) for i,v in enumerate(p['fixed_numerals'])]
def cv(x):return int(x) if x.isdigit() else x
assert [[n,o,cv(a),cv(b)] for n,a,o,b in re.findall(r'^  let (\w+) := (\w+) ([+*\-]) (\w+)$',s,re.M)]==p['source']
assert re.search(r'\n  '+p['output']+r'\s*\nend ',s)
assert 'theorem scaled_quotient (m z n : V) (hm : 0<m) (h : z*z=m*m*n)' in q
assert 'theorem literal_equivalence' in e and 'positiveShift' in e and 'mappedNativeRefutation embedding' in e
assert c['parent_sha256']==hashlib.sha256(pr).hexdigest() and len(c['witnesses'])==22 and c['operations']==len(c['source'])==110
assert n['positive_parent_sha256']==hashlib.sha256((P/'candidate.json').read_bytes()).hexdigest()
ren={x:'n_'+x for x in c['witnesses']};rep=lambda x:'shift_'+x if isinstance(x,str) and x in ren else x
assert n['witnesses']==list(ren.values())
assert n['source']==[['shift_'+x,'+',ren[x],1] for x in c['witnesses']]+[[x,o,rep(a),rep(b)] for x,o,a,b in c['source']]
assert n['operations']==len(n['source'])==132 and n['output']==c['output'] and n['fixed_numerals']==c['fixed_numerals']
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
res=['A0','A1','auxResidual','g72','scaleDifference','mainScaleDifference','rankDifference','ellDifference','cSquareDifference','zDifference','dDifference','vDifference','deltaDifference']
base={x:var(x) for x in c['witnesses']+c['fixed_numerals']}
pbase=dict(base);pbase['zValueVariable']=mul(var('scaleVariable'),var('firstQuotient'));pbase['dValueVariable']=mul(var('mainScaleVariable'),var('mainQuotient'))
pe=ev(p,res,pbase);ce=ev(c,res,dict(base))
assert pe['A0']==mul(mul(var('scaleVariable'),var('scaleVariable')),ce['A0'])
assert pe['A1']==mul(mul(var('mainScaleVariable'),var('mainScaleVariable')),ce['A1'])
assert all(pe[x]==ce[x] for x in res[2:])
for g in (p,c):
 z=ev(g,[g['output']],{x:var(x) for x in res})[g['output']]
 assert z=={(x,x):1 for x in res}
w=set(c['witnesses']);degree=lambda poly:max((sum(x in w for x in mon) for mon in poly),default=-1)
degrees={r:degree(ce[r]) for r in res};assert max(degrees.values())==5
cert=[]
for r in res:
 for mon,coefficient in ce[r].items():
  wm=tuple(x for x in mon if x in w)
  if len(wm)!=5:continue
  coeff={tuple(x for x in m if x not in w):v for m,v in ce[r].items() if tuple(x for x in m if x in w)==wm}
  if coeff=={():1} or coeff=={():-1}:cert.append((r,wm,coefficient))
assert cert
print(json.dumps({'scope':'exact all-port residual transfer and source/DAG evidence; zero maps use the documented IΣ₁ quotient argument; no Lean elaboration', 'positive':{'variables':22,'operations':110,'degree':10,'counts':pc},'natural_shift':{'variables':22,'operations':132,'degree':10,'counts':nc},'parent_literal_rows_match':True,'squared_norm_factors':['scaleVariable²','mainScaleVariable²'],'other_11_residuals_equal':True,'sum_of_13_squares_checked':True,'residual_degrees':degrees,'leading_witness':cert[0],'lean_elaboration':False},sort_keys=True,indent=2))
