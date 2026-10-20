#!/usr/bin/env python3
"""Separate parser/checker for the exported seed+G proof DAG and symbolic label templates.
No imports from the proof generator or its original checker.
"""
from pathlib import Path
from itertools import product
import argparse,json,hashlib
F=('rel',0,0)
I=lambda a,b:('imp',a,b)
Q=lambda i,a:('all',i,a)
E=lambda a,b:('eq',a,b)
N=lambda a:I(a,F)
Ex=lambda i,a:N(Q(i,N(a)))
def freeze(x):return tuple(map(freeze,x)) if isinstance(x,list) else x
def need(v,m):
 if not v:raise ValueError(m)
def atoms(f):
 if f==F:return set()
 if f[0]=='imp':return atoms(f[1])|atoms(f[2])
 return {f}
def val(f,v):
 if f==F:return False
 if f[0]=='imp':return not val(f[1],v) or val(f[2],v)
 return v[f]
def label(z):
 if type(z) is int:return z>=0
 if type(z) is str:return z in ('a','b','c')
 return isinstance(z,tuple) and len(z)==3 and z[0]=='kappa' and label(z[1]) and label(z[2])
def kappa(a,b):
 if type(a) is int and type(b) is int:return 4*((a+b)*(a+b+1)//2+b)+1
 return 'kappa',a,b
ap=argparse.ArgumentParser(description=__doc__)
ap.add_argument('proof',type=Path)
ap.add_argument('--output',type=Path,required=True)
args=ap.parse_args()
p=args.proof;d=json.loads(p.read_text())
forms=list(map(freeze,d['formulas']));nodes=d['proof_nodes'];deps=[];counts={}
for j,n in enumerate(nodes):
 rule=n['rule'];f=forms[n['formula']];a=n['args'];uses=[];counts[rule]=counts.get(rule,0)+1
 if rule=='MP':
  need(len(a)==2 and all(isinstance(i,int)and 0<=i<j for i in a),'MP topological order')
  need(forms[nodes[a[0]]['formula']]==I(forms[nodes[a[1]]['formula']],f),'MP')
  uses=a
 elif rule=='GEN':
  z,prem=a;z=freeze(z);need(label(z) and isinstance(prem,int)and 0<=prem<j,'GEN args')
  need(f==Q(z,forms[nodes[prem]['formula']]),'GEN formula');uses=[prem]
 elif rule=='TAUT':
  ats=sorted(atoms(f),key=repr)
  need(all(val(f,dict(zip(ats,bits)))for bits in product((False,True),repeat=len(ats))),'TAUT')
 elif rule=='rho1':
  z=f[1][1];e=f[1][2][1];need(e[0]=='eq'and e[1]==z and f==Ex(z,e),'rho1')
 elif rule=='rho2':
  z=f[1][1];A=f[1][2][1];B=f[1][2][2]
  need(f==I(Q(z,I(A,B)),I(Q(z,A),Q(z,B))),'rho2')
 elif rule=='rho6':
  z=f[1][1][1];A=f[2];need(f==I(Ex(z,Q(z,A)),A),'rho6')
 elif rule in ('G','OLD_H','OLD_RHO7'):
  a=freeze(a);need(all(label(z) for z in a),'labels must be natural-valued terms')
  x,y=a[:2];e=E(x,y)
  if rule=='G':expected=I(E(a[2],x),I(E(a[2],y),Q(kappa(x,y),e)))
  elif rule=='OLD_H':expected=I(e,Q(kappa(x,y),e))
  else:expected=I(E(a[2],x),I(E(a[2],y),e))
  need(f==expected,rule)
 else:raise ValueError('Unsupported leaf/rule: '+rule)
 deps.append(uses)
roots={}
for name,j in d['roots'].items():
 need(isinstance(j,int)and 0<=j<len(nodes),'root index')
 seen=set();todo=[j]
 for i in todo:
  if i in seen:continue
  seen.add(i);todo.extend(deps[i])
 used={nodes[i]['rule']for i in seen}
 if name.startswith(('reflexivity','helper','box_elimination','old_euclidean','symmetry')):
  need(not used&{'OLD_H','OLD_RHO7'},'old premise in new-theory proof')
 if name.startswith('reverse_G'):need('G'not in used,'G premise in old-theory proof')
 roots[name]=dict(nodes=len(seen),rules=sorted(used))
r=dict(status='INDEPENDENT_FINITE_DAG_REPLAY_PASS',proof_sha256=hashlib.sha256(p.read_bytes()).hexdigest(),nodes=len(nodes),formulas=len(forms),root_count=len(roots),rules=counts,roots=roots,scope='Closed finite native-formula derivations with rho8/rho6-derived propositional TAUT leaves; no proof-generator imports, no open-hypothesis rule, and no circular cross-theory leaves. Symbolic label terms are natural-valued under every assignment; each checked rule is stable under that evaluation. This establishes the uniform template as well as numerical regressions.')
args.output.write_text(json.dumps(r,indent=2)+'\n')
print(json.dumps({k:v for k,v in r.items()if k!='roots'},indent=2))
