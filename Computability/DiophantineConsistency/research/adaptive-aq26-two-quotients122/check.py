#!/usr/bin/env python3
"""Exact sparse-polynomial transfer, source and DAG certificate. No Lean."""
from pathlib import Path
from collections import Counter
import hashlib,json,re,sys
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
P=Path(__file__).resolve().parent;D=P.parents[1]
def pin(path,digest):
 b=path.read_bytes();assert hashlib.sha256(b).hexdigest()==digest,path;return b
pr=pin(D/'research/adaptive-square-sums26-degree8/candidate.json','d8e80e15d74271ba62877e841198a85729c0c4a74a5927927591b9ec2204b1a5');p=json.loads(pr)
c=json.loads(pin(P/'candidate.json','14c9cac4f3af45c15ec5e6df623c83fcab7581ba042aff34c6614dad890154ae'))
n=json.loads(pin(P/'natural-candidate.json','9909fc023d41d060b4edc6a89374f3b88d2f5e83f8b03d45eb5f6f86dc8141ee'))
s=pin(D/'Lean/DiophantineConsistency/AdaptiveAQ26Literal.lean','91af1d18ff4323623ce77828d08cbfc3d3da92c9fa1bee0e840ae0b74486a441').decode()
q=pin(D/'Lean/DiophantineConsistency/ArithmeticAdaptiveQuotients2011.lean','40070b23fceee62a689a1002f97f6f612057634b5bd8472949f0d2dcab136884').decode()
e=pin(D/'Lean/DiophantineConsistency/IPRAAQ26Native.lean','7be42c91618e357ea519fc21afa07fbfd646aa376571d85fd004584b711c37d1').decode()
assert re.findall(r'let (\w+) : Expr \(Fin 26\) := \.var (\d+)',s)==[(v,str(i)) for i,v in enumerate(p['witnesses'])]
assert re.findall(r'let (\w+) : Expr \(Fin 26\) := \.constant \(p (\d+)\)',s)==[(v,str(i)) for i,v in enumerate(p['fixed_numerals'])]
def cv(x):return int(x) if x.isdigit() else x
assert [[n,o,cv(a),cv(b)] for n,a,o,b in re.findall(r'^  let (\w+) := (\w+) ([+*\-]) (\w+)$',s,re.M)]==p['source']
assert re.search(r'\n  '+p['output']+r'\s*\nend ',s)
assert 'theorem scaled_quotient (m z n : V) (hm : 0<m) (h : z*z=m*m*n)' in q
assert 'theorem literal_equivalence' in e and 'positiveShift' in e and 'mappedNativeRefutation embedding' in e
assert c['parent_sha256']==hashlib.sha256(pr).hexdigest() and len(c['witnesses'])==26 and c['operations']==len(c['source'])==122
assert n['positive_parent_sha256']==hashlib.sha256((P/'candidate.json').read_bytes()).hexdigest()
ren={x:'n_'+x for x in c['witnesses']};rep=lambda x:'shift_'+x if isinstance(x,str) and x in ren else x
assert n['witnesses']==list(ren.values())
assert n['source']==[['shift_'+x,'+',ren[x],1] for x in c['witnesses']]+[[x,o,rep(a),rep(b)] for x,o,a,b in c['source']]
assert n['operations']==len(n['source'])==148 and n['output']==c['output'] and n['fixed_numerals']==c['fixed_numerals']
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
res=['A0','A1','auxResidual','g72','scaleDifference','mainScaleDifference','rankDifference','cDifference','ellDifference','cSquareDifference','zDifference','dDifference','vDifference','deltaDifference','qSquareDifference','product2Difference','qSignedDifference']
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
degrees={r:degree(ce[r]) for r in res};assert max(degrees.values())==4
m=tuple(sorted(['cSquareVariable','cSquareVariable','i','i']))
assert ce['g72'].get(m)==1
assert not any(tuple(x for x in mon if x in w)==m and tuple(x for x in mon if x not in w) for mon in ce['g72'])
print(json.dumps({'scope':'exact all-port residual transfer and source/DAG evidence; zero maps use the documented IΣ₁ quotient argument; no Lean elaboration', 'positive':{'variables':26,'operations':122,'degree':8,'counts':pc},'natural_shift':{'variables':26,'operations':148,'degree':8,'counts':nc},'parent_literal_rows_match':True,'squared_norm_factors':['scaleVariable²','mainScaleVariable²'],'other_15_residuals_equal':True,'sum_of_17_squares_checked':True,'residual_degrees':degrees,'leading_term_g72':'cSquareVariable² i² with coefficient 1','lean_elaboration':False},sort_keys=True,indent=2))
