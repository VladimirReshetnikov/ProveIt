#!/usr/bin/env python3
"""Standalone replay of serialized Hilbert proof nodes; safe under python -O."""
from pathlib import Path
import json
ROOT=Path(__file__).resolve().parent
raw=json.loads(ROOT.joinpath('hilbert_proofs.json').read_text())
def tup(x):return tuple(map(tup,x))if isinstance(x,list)else x
forms=list(map(tup,raw['formulas']));nodes=raw['proof_nodes']
F=('rel',0,0);p=('meta','p');i='i'
def imp(a,b):return ('imp',a,b)
def all_(v,a):return ('all',v,a)
def neg(a):return imp(a,F)
def j(a):return neg(neg(a))
def ex(v,a):return neg(all_(v,neg(a)))
def conj(a,b):return neg(imp(a,neg(b)))
def req(cond,msg):
 if not cond:raise ValueError(msg)
proved=[];open_hyp=[]
for n,row in enumerate(nodes):
 r=row['rule'];a=forms[row['formula']];ar=row['args'];h=frozenset()
 if r=='MP':
  x,y=ar;req(x<n and y<n,f'{n}: forward proof reference')
  req(proved[x]==imp(proved[y],a),f'{n}: bad MP');h=open_hyp[x]|open_hyp[y]
 elif r=='GEN':
  v,x=ar;req(x<n,f'{n}: forward GEN reference')
  req(not open_hyp[x],f'{n}: GEN of open derivation')
  req(a==all_(v,proved[x]),f'{n}: bad GEN')
 elif r=='K':
  x=a[1];y=a[2][1];req(a==imp(x,imp(y,x)),f'{n}: bad K')
 elif r=='S':
  x=a[1][1];y=a[1][2][1];z=a[1][2][2]
  req(a==imp(imp(x,imp(y,z)),imp(imp(x,y),imp(x,z))),f'{n}: bad S')
 elif r=='rho1':
  v=a[1][1];e=a[1][2][1]
  req(len(e)==3 and e[0]=='eq' and e[1]==v and a==ex(v,e),f'{n}: bad rho1')
 elif r=='rho2':
  v=a[1][1];x=a[1][2][1];y=a[1][2][2]
  req(a==imp(all_(v,imp(x,y)),imp(all_(v,x),all_(v,y))),f'{n}: bad rho2')
 elif r=='rho6':
  v=a[1][1][1];x=a[2]
  req(a==imp(ex(v,all_(v,x)),x),f'{n}: bad rho6')
 elif r=='weak_vacuity':req(a==imp(p,j(all_(i,p))),f'{n}: unexpected premise')
 elif r=='HYP':h=frozenset((a,))
 else:raise ValueError(f'{n}: unknown rule {r}')
 proved.append(a);open_hyp.append(h)
v=imp(p,all_(i,p));c=('meta','C');g=('meta','G');ve=('meta','ve')
x=('meta','a');y=('meta','b');u=('meta','u')
expected={
 'weak_from_double_vacuity':imp(j(v),imp(p,j(all_(i,p)))),
 'bundle_component_dn':imp(conj(conj(c,g),conj(v,ve)),j(v)),
 'atomic_dne':imp(j(p),p),
 'classical_rho8':imp(imp(imp(p,u),x),imp(imp(x,p),imp(y,p)))
}
for name,k in raw['roots'].items():
 req(not open_hyp[k],f'{name}: open root')
 req(proved[k]==expected[name],f'{name}: wrong conclusion')
report=dict(proof_nodes_replayed=len(nodes),formulas=len(forms),checked_roots=list(raw['roots']),fixed_falsity='Rel(0,0)',extra_axiom='p -> not not All(i,p)',status='All local rules and closed GEN applications checked. The extra premise remains explicit.')
ROOT.joinpath('hilbert_replay_results.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(report,indent=2))
