#!/usr/bin/env python3
"""Independent full-output sparse-polynomial check and model lemma audit."""
from pathlib import Path
import collections,hashlib,json,re,sys
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
D=Path(__file__).resolve().parents[2]
def pin(p,h):
 b=(D/p).read_bytes();assert hashlib.sha256(b).hexdigest()==h,p;return b.decode()
p=json.loads(pin('research/adaptive-square-sums26-degree8/candidate.json','d8e80e15d74271ba62877e841198a85729c0c4a74a5927927591b9ec2204b1a5'))
c=json.loads(pin('research/adaptive-aq26-two-quotients122/candidate.json','14c9cac4f3af45c15ec5e6df623c83fcab7581ba042aff34c6614dad890154ae'))
n=json.loads(pin('research/adaptive-aq26-two-quotients122/natural-candidate.json','9909fc023d41d060b4edc6a89374f3b88d2f5e83f8b03d45eb5f6f86dc8141ee'))
pin('research/adaptive-aq26-two-quotients122/receipt.json','b153c9751dcae8e6037ee9c4b1b6d3e7df7f992d5be6119c735626619d5f4223')
q=pin('Lean/DiophantineConsistency/ArithmeticAdaptiveQuotients2011.lean','40070b23fceee62a689a1002f97f6f612057634b5bd8472949f0d2dcab136884')
s=pin('Lean/DiophantineConsistency/ArithmeticSquareDivisibility.lean','f775c2050a794b1ea026cdec0950e42528260fa1d75a03f1ef625f258670e660')
e=pin('Lean/DiophantineConsistency/IPRAAQ26Native.lean','7be42c91618e357ea519fc21afa07fbfd646aa376571d85fd004584b711c37d1')
lit=pin('Lean/DiophantineConsistency/AdaptiveAQ26Literal.lean','91af1d18ff4323623ce77828d08cbfc3d3da92c9fa1bee0e840ae0b74486a441')
assert re.findall(r'let (\w+) : Expr \(Fin 26\) := \.var (\d+)',lit)==[(v,str(i)) for i,v in enumerate(p['witnesses'])]
assert re.findall(r'let (\w+) : Expr \(Fin 26\) := \.constant \(p (\d+)\)',lit)==[(v,str(i)) for i,v in enumerate(p['fixed_numerals'])]
cv=lambda x:int(x) if x.isdigit() else x
assert [[n,o,cv(a),cv(b)] for n,a,o,b in re.findall(r'^  let (\w+) := (\w+) ([+*\-]) (\w+)$',lit,re.M)]==p['source']
assert '[V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]' in q and 'theorem scaled_quotient (m z n : V) (hm : 0<m) (h : z*z=m*m*n)' in q
assert '∃ t : V, z=m*t ∧ t*t=n' in q and 'dvd_of_square_dvd m z hm hd' in q
assert 'theorem dvd_of_square_dvd (m z : V) (hm : 0<m) (h : m*m ∣ z*z) : m∣z' in s
assert 'IPRAExpressionNative.nativeNoZero' in e and '∼mappedNativeRefutation embedding' in e
assert len(p['witnesses'])==len(c['witnesses'])==len(n['witnesses'])==26 and len(p['source'])==126 and len(c['source'])==122 and len(n['source'])==148
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
res=['A0','A1','auxResidual','g72','scaleDifference','mainScaleDifference','rankDifference','cDifference','ellDifference','cSquareDifference','zDifference','dDifference','vDifference','deltaDifference','qSquareDifference','product2Difference','qSignedDifference']
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
assert max(map(degree,out))==8
target=tuple(sorted(['cSquareVariable']*4+['i']*4));assert out.get(target,0)>0
assert not any(tuple(x for x in m if x in inputs)==target and any(x not in inputs for x in m) for m in out)
print(json.dumps({'scope':'external exact full-polynomial comparison and model-lemma source audit; no new Lean proof','positive_variables':26,'positive_operations':122,'natural_operations':148,'degree_every_integer_port_tuple':8,'full_child_terms':len(out),'degree_witness_coefficient':out[target],'squared_residuals':17,'normal_residual_scaling_checked':2,'root_residuals_equal_after_reconstruction':2,'full_output_identity_not_equality':True,'existing_model_scaled_quotient_source_checked':True},sort_keys=True,indent=2))
