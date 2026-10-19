#!/usr/bin/env python3
"""Independent proof-local replay; all checks remain active with python -O."""
import json
from pathlib import Path
ROOT=Path(__file__).resolve().parent
D=json.loads((ROOT/'equality_proofs.json').read_text())
def tup(x):return tuple(map(tup,x)) if isinstance(x,list) else x
F=('rel',0,0)
I=lambda a,b:('imp',a,b)
Q=lambda i,a:('all',i,a)
N=lambda a:I(a,F)
E=lambda i,a:N(Q(i,N(a)))
Eq=lambda a,b:('eq',a,b)
fs=list(map(tup,D['formulas']));ps=D['proof_nodes'];open_sets=[]
def req(b,msg):
 if not b:raise ValueError(msg)
for ix,p in enumerate(ps):
 r=p['rule'];f=fs[p['formula']];args=p['args'];deps=frozenset()
 if r=='K':req(f==I(f[1],I(f[2][1],f[1])),str(ix))
 elif r=='S':
  a=f[1][1];b=f[1][2][1];c=f[1][2][2]
  req(f==I(I(a,I(b,c)),I(I(a,b),I(a,c))),str(ix))
 elif r=='MP':
  l,h=args;req(l<ix and h<ix,'acyclic');req(fs[ps[l]['formula']]==I(fs[ps[h]['formula']],f),str(ix));deps=open_sets[l]|open_sets[h]
 elif r=='GEN':
  v=tup(args[0]);h=args[1];req(h<ix,'acyclic');req(not open_sets[h],'closed GEN');req(f==Q(v,fs[ps[h]['formula']]),str(ix))
 elif r=='rho1':
  v=f[1][1];e=f[1][2][1];req(e[0]=='eq' and e[1]==v and f==E(v,e),str(ix))
 elif r=='rho2':
  v=f[1][1];a=f[1][2][1];b=f[1][2][2];req(f==I(Q(v,I(a,b)),I(Q(v,a),Q(v,b))),str(ix))
 elif r=='rho6':
  v=f[1][1][1];a=f[2];req(f==I(E(v,Q(v,a)),a),str(ix))
 elif r=='rho7':
  c,a=f[1][1:];c2,b=f[2][1][1:];req(c==c2 and f==I(Eq(c,a),I(Eq(c,b),Eq(a,b))),str(ix))
 elif r=='V_eq':
  e=f[1];req(e[0]=='eq' and f==I(e,Q(('weq',e[1],e[2]),e)),str(ix))
 elif r=='HYP':deps=frozenset((f,))
 else:raise ValueError(r)
 open_sets.append(deps)
expected={'equality_reflexivity':Eq('x','x'),'equality_symmetry':I(Eq('x','y'),Eq('y','x')),'equality_transitivity':I(Eq('x','y'),I(Eq('y','z'),Eq('x','z')))}
report={}
for name,root in D['roots'].items():
 req(not open_sets[root],'open root');req(fs[ps[root]['formula']]==expected[name],'wrong root')
 seen=set()
 def walk(j):
  if j in seen:return
  seen.add(j);p=ps[j]
  if p['rule']=='MP':
   for c in p['args']:walk(c)
  if p['rule']=='GEN':walk(p['args'][1])
 walk(root);counts={}
 for j in seen:counts[ps[j]['rule']]=counts.get(ps[j]['rule'],0)+1
 report[name]=dict(proof_nodes=len(seen),rules=counts,formula=str(expected[name]))
report['total_nodes']=len(ps);report['total_formulas']=len(fs);report['valid']=True
(ROOT/'equality_results.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report,indent=2))
