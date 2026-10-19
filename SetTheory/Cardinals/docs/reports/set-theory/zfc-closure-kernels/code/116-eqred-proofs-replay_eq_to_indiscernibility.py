#!/usr/bin/env python3
"""Independent local-rule replay of projection certificates, safe under -O."""
from pathlib import Path
import json
H=Path(__file__).resolve().parent
raw=json.loads((H/'eq_to_indiscernibility_proofs.json').read_text())
def tup(x):return tuple(map(tup,x)) if isinstance(x,list) else x
fs=list(map(tup,raw['formulas']));nodes=raw['proof_nodes']
F=('rel',0,0)
I=lambda a,b:('imp',a,b)
Q=lambda i,a:('all',i,a)
N=lambda a:I(a,F)
Ex=lambda i,a:N(Q(i,N(a)))
And=lambda a,b:N(I(a,N(b)))
code=lambda a:('native_code',a)

def req(c,m):
 if not c:raise ValueError(m)
opens=[]
for ix,p in enumerate(nodes):
 r=p['rule'];f=fs[p['formula']];ar=p['args'];deps=frozenset()
 if r=='K':req(f==I(f[1],I(f[2][1],f[1])),f'{ix}: K')
 elif r=='S':
  a=f[1][1];b=f[1][2][1];c=f[1][2][2]
  req(f==I(I(a,I(b,c)),I(I(a,b),I(a,c))),f'{ix}: S')
 elif r=='MP':
  p1,p2=ar;req(p1<ix and p2<ix,'acyclic MP')
  req(fs[nodes[p1]['formula']]==I(fs[nodes[p2]['formula']],f),f'{ix}: MP')
  deps=opens[p1]|opens[p2]
 elif r=='GEN':
  i,p1=tup(ar[0]),ar[1];req(p1<ix,'acyclic GEN');req(not opens[p1],'closed GEN')
  req(f==Q(i,fs[nodes[p1]['formula']]),f'{ix}: GEN')
 elif r=='rho1':
  i=f[1][1];e=f[1][2][1]
  req(e[0]=='eq' and e[1]==i and f==Ex(i,e),f'{ix}: rho1')
 elif r=='rho2':
  i=f[1][1];a=f[1][2][1];b=f[1][2][2]
  req(f==I(Q(i,I(a,b)),I(Q(i,a),Q(i,b))),f'{ix}: rho2')
 elif r=='rho6':
  i=f[1][1][1];a=f[2]
  req(f==I(Ex(i,Q(i,a)),a),f'{ix}: rho6')
 elif r=='Sym':
  a,b=f[1][1:]
  req(f==I(('eq',a,b),('eq',b,a)),f'{ix}: symmetry')
 elif r=='rho3':
  a,b=f[1][1:];z=f[2][1][1]
  req(f==I(('eq',a,b),I(('rel',z,a),('rel',z,b))),f'{ix}: rho3')
 elif r=='rho5':
  a,b=f[1][1:];z=f[2][1][2]
  req(f==I(('eq',a,b),I(('rel',a,z),('rel',b,z))),f'{ix}: rho5')
 elif r=='V_eq':
  a,b=f[1][1:];e=('eq',a,b)
  req(f==I(e,Q(('weq',a,b),e)),f'{ix}: exact canonical Eq V')
 elif r=='PV':
  a=f[1];v=f[2][1]
  req(v[0]=='native_code' and v[1][0]=='imp' and v[1][1]==a and
      f==I(a,Q(code(I(a,v[1][2])),a)),f'{ix}: exact projection V')
 elif r=='HYP':deps=frozenset((f,))
 else:raise ValueError('unrecognized rule '+r)
 opens.append(deps)

a,b='a','b';e=('eq',a,b)
R=lambda x,y:('rel',x,y)
def E(z):
 inward=Q(z,And(I(R(z,a),R(z,b)),I(R(z,b),R(z,a))))
 outward=Q(z,And(I(R(a,z),R(b,z)),I(R(b,z),R(a,z))))
 return And(inward,outward)
expected={}
for kind,z in [('canonical',('weq',a,b)),('projection',code(I(e,('meta','B'))))]:
 expected[kind+'_Eq_to_E']=I(e,E(z))
 expected[kind+'_exists_E']=Ex(a,E(z))
report={}
for name,root in raw['roots'].items():
 req(not opens[root],name+': closed root');req(fs[nodes[root]['formula']]==expected[name],name+': expected root')
 seen=set()
 def walk(i):
  if i in seen:return
  seen.add(i);p=nodes[i]
  if p['rule']=='MP':
   for j in p['args']:walk(j)
  if p['rule']=='GEN':walk(p['args'][1])
 walk(root)
 counts={}
 for i in seen:counts[nodes[i]['rule']]=counts.get(nodes[i]['rule'],0)+1
 report[name]={'proof_nodes':len(seen),'rules':counts}
report.update(valid=True,total_nodes=len(nodes),total_formulas=len(fs),
 fixed_falsity='Rel(0,0)',primitive_axioms=['K','S','rho1','rho2','rho3','rho5','Sym','V_eq or PV'],
 native_binding='PV binder is wim(A_code,B_code), including wim(0,0)=0; no enc(dec(n)) premise',
 scope='Exact Eq-to-E and existential E bridge. No rho7, primitive equality reflexivity, old vacuity, DNE, CP/GIC, or alpha conversion.')
(H/'eq_to_indiscernibility_results.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(report,indent=2))
