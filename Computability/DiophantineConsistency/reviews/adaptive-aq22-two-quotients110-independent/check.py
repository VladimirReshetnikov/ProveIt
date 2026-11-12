#!/usr/bin/env python3
"""Independent full-output sparse-polynomial check and model lemma audit."""
from pathlib import Path
import collections,hashlib,json,re,sys
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
D=Path(__file__).resolve().parents[2]
def pin(p,h):
 b=(D/p).read_bytes();assert hashlib.sha256(b).hexdigest()==h,p;return b.decode()
p=json.loads(pin('research/adaptive-square-sums22-degree10/candidate.json','1266b143c5512351739ea2c71fc8e0b8b0e5cecc599392f128c0803ff78ce106'))
c=json.loads(pin('research/adaptive-aq22-two-quotients110/candidate.json','b82ef3f8e45cc260d8ffee26f3f8fa7ef2f207834829aee1a5ac357fcab0ffc1'))
n=json.loads(pin('research/adaptive-aq22-two-quotients110/natural-candidate.json','3a86d13d17522c1d662888dbc5149f61023e34c9d04bb7db4c241818ee9ee0a7'))
pin('research/adaptive-aq22-two-quotients110/receipt.json','38dd311675e3d7e19cf339032937129b2f0c317fbc77692e414b92a1908481f2')
q=pin('Lean/DiophantineConsistency/ArithmeticAdaptiveQuotients2011.lean','40070b23fceee62a689a1002f97f6f612057634b5bd8472949f0d2dcab136884')
s=pin('Lean/DiophantineConsistency/ArithmeticSquareDivisibility.lean','f775c2050a794b1ea026cdec0950e42528260fa1d75a03f1ef625f258670e660')
e=pin('Lean/DiophantineConsistency/IPRAAQ22Native.lean','b90a9eb67b6fef945e6f1a3c9900e39e3a07a16dbe032089b3489660e00ce747')
lit=pin('Lean/DiophantineConsistency/AdaptiveAQ22Literal.lean','7d417cd67cc0d6150e3c122e7c4cca4d5c924b54dafe36885f7b5d9b06cf7b6c')
assert re.findall(r'let (\w+) : Expr \(Fin 22\) := \.var (\d+)',lit)==[(v,str(i)) for i,v in enumerate(p['witnesses'])]
assert re.findall(r'let (\w+) : Expr \(Fin 22\) := \.constant \(p (\d+)\)',lit)==[(v,str(i)) for i,v in enumerate(p['fixed_numerals'])]
cv=lambda x:int(x) if x.isdigit() else x
assert [[n,o,cv(a),cv(b)] for n,a,o,b in re.findall(r'^  let (\w+) := (\w+) ([+*\-]) (\w+)$',lit,re.M)]==p['source']
policy=json.loads(pin('research/ipra-standard-aq22/historical/task-policy.json','0d80d3899a9b0d2356e16e4c7cc81ec72fe792ea1a1ee2e336f3e92373b4a6b1'))
pin('reviews/ipra-aq22-historical-pair-terminal/README.md','56545a77231c7e9b2a214e7db1d80bc4e8f38b6936a6087d64cc6da479c7eb90')
pin('reviews/ipra-aq22-historical-pair-independent-audit/README.md','f021cffa6272653613a7fcc7732ffffff5ffbccf68b8b83658a3272092664d1e')
assert policy['sources']['DiophantineConsistency.AdaptiveAQ22Literal']['sha256']==hashlib.sha256(lit.encode()).hexdigest()
assert policy['sources']['DiophantineConsistency.IPRAAQ22Native']['sha256']==hashlib.sha256(e.encode()).hexdigest()
assert '[V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]' in q and 'theorem scaled_quotient (m z n : V) (hm : 0<m) (h : z*z=m*m*n)' in q
assert '∃ t : V, z=m*t ∧ t*t=n' in q and 'dvd_of_square_dvd m z hm hd' in q
assert 'theorem dvd_of_square_dvd (m z : V) (hm : 0<m) (h : m*m ∣ z*z) : m∣z' in s
assert 'IPRAExpressionNative.nativeNoZero' in e and '∼mappedNativeRefutation embedding' in e
assert len(p['witnesses'])==len(c['witnesses'])==len(n['witnesses'])==22 and len(p['source'])==114 and len(c['source'])==110 and len(n['source'])==132
assert c['witnesses']==[{'zValueVariable':'firstQuotient','dValueVariable':'mainQuotient'}.get(x,x) for x in p['witnesses']]
ren={x:'n_'+x for x in c['witnesses']};rep=lambda x:'shift_'+x if isinstance(x,str) and x in ren else x
assert n['witnesses']==list(ren.values()) and n['source']==[['shift_'+x,'+',ren[x],1] for x in c['witnesses']]+[[x,op,rep(a),rep(b)] for x,op,a,b in c['source']]
assert n['fixed_numerals']==c['fixed_numerals'] and n['output']==c['output']
def atom(x):return {(x,):1}
def add(a,b,k=1):
 d=dict(a)
 for m,v in b.items():d[m]=d.get(m,0)+k*v
 return {m:v for m,v in d.items() if v}
def mul(a,b):
 d=collections.defaultdict(int)
 for ma,ca in a.items():
  for mb,cb in b.items():d[tuple(sorted(ma+mb))]+=ca*cb
 return {m:v for m,v in d.items() if v}
def run(g,subs):
 env={x:atom(x) for x in g['witnesses']+g['fixed_numerals']};env.update(subs)
 rows={}
 for name,op,a,b in g['source']:
  assert name not in env and op in '+-*'
  rows[name]=(a,b)
  a=env[a] if isinstance(a,str) else ({():a} if a else {})
  b=env[b] if isinstance(b,str) else ({():b} if b else {})
  env[name]=mul(a,b) if op=='*' else add(a,b,-1 if op=='-' else 1)
 active={g['output']};todo=[g['output']]
 while todo:
  for x in rows.get(todo.pop(),()):
   if isinstance(x,str) and x not in active:active.add(x);todo.append(x)
 assert set(rows)|set(g['witnesses'])|set(g['fixed_numerals'])<=active
 return env
sub={'zValueVariable':mul(atom('scaleVariable'),atom('firstQuotient')),'dValueVariable':mul(atom('mainScaleVariable'),atom('mainQuotient'))}
a=run(p,sub);b=run(c,{})
scale2=mul(atom('scaleVariable'),atom('scaleVariable'));main2=mul(atom('mainScaleVariable'),atom('mainScaleVariable'))
assert a['A0']==mul(scale2,b['A0']) and a['A1']==mul(main2,b['A1'])
assert add(a['zDifference'],b['zDifference'],-1)=={} and add(a['dDifference'],b['dDifference'],-1)=={}
# Independent full-output identity, not just residual checks.
correction=add(mul(add(mul(scale2,scale2),{():1},-1),mul(b['A0'],b['A0'])),mul(add(mul(main2,main2),{():1},-1),mul(b['A1'],b['A1'])))
assert add(a[p['output']],b[c['output']],-1)==correction and correction
# Reconstruct both outputs over formal residual atoms, independent of their values.
res=['A0','A1','auxResidual','g72','scaleDifference','mainScaleDifference','rankDifference','ellDifference','cSquareDifference','zDifference','dDifference','vDifference','deltaDifference',]
for graph in (p,c):
 env={x:atom(x) for x in res}
 for name,op,x,y in graph['source']:
  if name in env:continue
  if isinstance(x,str) and x not in env:continue
  if isinstance(y,str) and y not in env:continue
  x=env[x] if isinstance(x,str) else ({():x} if x else {})
  y=env[y] if isinstance(y,str) else ({():y} if y else {})
  env[name]=mul(x,y) if op=='*' else add(x,y,-1 if op=='-' else 1)
 assert env[graph['output']]=={(x,x):1 for x in res}
inputs=set(c['witnesses']);out=b[c['output']];degree=lambda m:sum(x in inputs for x in m)
assert max(map(degree,out))==10
target=tuple(sorted(['deltaVariable']*2+['f']*4+['y']*4));assert out.get(target,0)>0
assert not any(tuple(x for x in m if x in inputs)==target and any(x not in inputs for x in m) for m in out)
print(json.dumps({'scope':'external exact full-polynomial comparison and model-lemma source audit; no new Lean proof','positive_variables':22,'positive_operations':110,'natural_operations':132,'degree_every_integer_port_tuple':10,'full_child_terms':len(out),'degree_witness_coefficient':out[target],'squared_residuals':13,'normal_residual_scaling_checked':2,'root_residuals_equal_after_reconstruction':2,'full_output_identity_not_equality':True,'existing_model_scaled_quotient_source_checked':True},sort_keys=True,indent=2))
