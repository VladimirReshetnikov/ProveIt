#!/usr/bin/env python3
"""Independent symbolic-label Hilbert proof checker; imports no generator.

Labels are natural-valued terms x,y,z,kappa(s,t), where kappa=4P+1.
Every rule is schematic in those labels. No comparison of distinct label
variables is made. Consequently acceptance covers every natural substitution,
not merely the displayed variable names or a finite set of instances.
"""
from pathlib import Path
from itertools import product
import argparse,json,hashlib,copy
F=('rel',0,0)
I=lambda a,b:('imp',a,b)
Q=lambda z,a:('all',z,a)
E=lambda a,b:('eq',a,b)
N=lambda a:I(a,F)
Ex=lambda z,a:N(Q(z,N(a)))
K=lambda a,b:('kappa',a,b)
def freeze(x):return tuple(map(freeze,x)) if isinstance(x,list) else x
def need(x,msg):
 if not x:raise ValueError(msg)
def label(x):
 return (type(x) is int and x>=0) or (type(x) is str and x in ('x','y','z')) or (type(x) is tuple and len(x)==3 and x[0]=='kappa' and label(x[1]) and label(x[2]))
def form(x):
 if not isinstance(x,tuple):return False
 if len(x)==2:return x[0]=='opaque' and x[1] in ('V','J')
 if len(x)!=3:return False
 t,a,b=x
 if t=='imp':return form(a) and form(b)
 if t=='all':return label(a) and form(b)
 return t in ('eq','rel') and label(a) and label(b)
def atoms(f):
 if f==F:return set()
 return atoms(f[1])|atoms(f[2]) if f[0]=='imp' else {f}
def val(f,env):
 if f==F:return False
 return not val(f[1],env) or val(f[2],env) if f[0]=='imp' else env[f]
def expected():
 x,y,z='x','y','z';e=E(x,y);H=I(e,Q(K(x,y),e));G=I(E(z,x),I(E(z,y),Q(K(x,y),e)))
 V=('opaque','V');J=('opaque','J');old=N(I(V,I(H,J)));new=N(I(V,J))
 return {'reflexivity':E(x,x),'ordinary_helper':H,'equality_box_elim':I(Q(K(x,y),e),e),'original_rho7':I(E(z,x),I(E(z,y),e)),'symmetry':I(e,E(y,x)),'merged_from_old':G,'old_bundle_to_new':I(old,new),'old_bundle_to_helper':I(old,H),'new_bundle_plus_helper_to_old':I(new,I(H,old))}
def check(d):
 need(d['format']=='uniform-label-terms-v1','format')
 fs=list(map(freeze,d['formulas']));ns=d['proof_nodes'];deps=[];counts={}
 need(all(form(f) for f in fs),'malformed formula/label term')
 for j,n in enumerate(ns):
  fi=n['formula'];need(type(fi) is int and 0<=fi<len(fs),'formula reference')
  r=n['rule'];f=fs[fi];a=freeze(n['args']);uses=[];counts[r]=counts.get(r,0)+1
  if r=='MP':
   need(len(a)==2 and all(type(i) is int and 0<=i<j for i in a),'MP references')
   need(fs[ns[a[0]]['formula']]==I(fs[ns[a[1]]['formula']],f),'MP formula');uses=list(a)
  elif r=='GEN':
   need(len(a)==2 and label(a[0]) and type(a[1]) is int and 0<=a[1]<j,'GEN reference')
   need(f==Q(a[0],fs[ns[a[1]]['formula']]),'GEN formula');uses=[a[1]]
  elif r=='TAUT':
   ats=sorted(atoms(f),key=repr);need(len(ats)<=10,'TAUT atom safety bound')
   need(all(val(f,dict(zip(ats,bits))) for bits in product((False,True),repeat=len(ats))),'TAUT')
  elif r=='rho1':
   t=f[1][1];e=f[1][2][1];need(e[0]=='eq' and e[1]==t and f==Ex(t,e),'rho1')
  elif r=='rho2':
   t=f[1][1];A=f[1][2][1];B=f[1][2][2];need(f==I(Q(t,I(A,B)),I(Q(t,A),Q(t,B))),'rho2')
  elif r=='rho6':
   t=f[1][1][1];A=f[2];need(f==I(Ex(t,Q(t,A)),A),'rho6')
  elif r in ('G','OLD_H','OLD_RHO7'):
   need(len(a)==(2 if r=='OLD_H' else 3) and all(label(i) for i in a),'schema parameters')
   x,y=a[:2];e=E(x,y)
   want=I(e,Q(K(x,y),e)) if r=='OLD_H' else I(E(a[2],x),I(E(a[2],y),Q(K(x,y),e) if r=='G' else e))
   need(f==want,'schema '+r)
  else:raise ValueError('unpermitted rule '+r)
  deps.append(uses)
 need(set(d['roots'])==set(expected()),'root names')
 roots={}
 for name,want in expected().items():
  q=d['roots'][name];need(type(q) is int and 0<=q<len(ns),'root reference');need(fs[ns[q]['formula']]==want,'root formula '+name)
  seen=set();todo=[q]
  while todo:
   i=todo.pop()
   if i in seen:continue
   seen.add(i);todo.extend(deps[i])
  used={ns[i]['rule'] for i in seen}
  if name in ('reflexivity','ordinary_helper','equality_box_elim','original_rho7','symmetry'):need(not used&{'OLD_H','OLD_RHO7'},'circular old axiom')
  if name=='merged_from_old':need('G' not in used,'circular G')
  roots[name]={'nodes':len(seen),'rules':sorted(used)}
 return {'status':'PASS_UNIFORM_SCHEMATIC_PROOFS','nodes':len(ns),'formulas':len(fs),'roots':roots,'rules':counts,'scope':'Every substitution of natural labels for x,y,z. No freshness or distinctness assumption; no hypothetical-premise rule; GEN only on closed derivations. TAUT uses the independently retained rho8/rho6 propositional bridge.'}
def main():
 p=argparse.ArgumentParser();p.add_argument('proof',type=Path);p.add_argument('--output',type=Path,required=True);a=p.parse_args();raw=a.proof.read_bytes();d=json.loads(raw);r=check(d);r['sha256']=hashlib.sha256(raw).hexdigest()
 bad=copy.deepcopy(d);bad['roots']['ordinary_helper']=bad['roots']['reflexivity']
 try:check(bad)
 except (ValueError,IndexError,KeyError,TypeError):r['negative_control_root']='REJECTED'
 else:raise ValueError('accepted corrupted root')
 bad=copy.deepcopy(d);i=next(i for i,n in enumerate(bad['proof_nodes']) if n['rule']=='G');bad['proof_nodes'][i]['args'][0]='not-a-label'
 try:check(bad)
 except (ValueError,IndexError,KeyError,TypeError):r['negative_control_G']='REJECTED'
 else:raise ValueError('accepted corrupted G')
 a.output.write_text(json.dumps(r,indent=2)+'\n');print(json.dumps(r,indent=2))
if __name__=='__main__':main()
