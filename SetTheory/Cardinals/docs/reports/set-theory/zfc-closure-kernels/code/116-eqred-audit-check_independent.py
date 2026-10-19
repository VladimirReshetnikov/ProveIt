#!/usr/bin/env python3
"""Independent replay and edge-label audit; upstream generators are untrusted.
Finite checks are regressions. See AUDIT.md for the uniform argument.
"""
from pathlib import Path
from functools import cache
from itertools import product
import sys,json,hashlib,time
ROOT=Path(__file__).resolve().parents[1]
SRC=ROOT/'proofs'
sys.path.insert(0,str(SRC))
import indiscernibility_certificates as g
F=('rel',0,0)
I=lambda p,q:('imp',p,q)
A=lambda i,p:('all',i,p)
N=lambda p:I(p,F)
X=lambda i,p:N(A(i,N(p)))
R=lambda i,j:('rel',i,j)
D=lambda i,j:('eq',i,j)
C=lambda p,q:N(I(p,N(q)))
code=lambda i,j:4*((i+j)*(i+j+1)//2+j)+3

def need(cond,why):
 if not cond:raise RuntimeError(why)
def tu(x):return tuple(map(tu,x)) if isinstance(x,list) else x
@cache
def valid_formula(f):
 need(isinstance(f,tuple),'formula tuple')
 if f[0] in ('rel','eq'):need(len(f)==3 and all(type(i)==int and i>=0 for i in f[1:]),'natural atomic labels')
 elif f[0]=='all':
  need(len(f)==3 and type(f[1])==int and f[1]>=0,'natural binder');valid_formula(f[2])
 elif f[0]=='imp':
  need(len(f)==3,'binary implication');valid_formula(f[1]);valid_formula(f[2])
 else:raise RuntimeError(('unknown formula constructor',f))
 return True
@cache
def atomlist(f):
 if f==F:return frozenset()
 if f[0]=='imp':return atomlist(f[1])|atomlist(f[2])
 return frozenset((f,))
@cache
def taut(f):
 av=tuple(atomlist(f));need(len(av)<=10,'unexpected taut complexity')
 def ev(q,v):
  if q==F:return False
  if q[0]=='imp':return not ev(q[1],v) or ev(q[2],v)
  return v[q]
 return all(ev(f,dict(zip(av,v))) for v in product((False,True),repeat=len(av)))

def replay(raw,expected):
 fs=list(map(tu,raw['formulas']));ns=raw['proof_nodes'];opens=[];counts={}
 for n,f in enumerate(fs):valid_formula(f)
 for n,p in enumerate(ns):
  f=fs[p['formula']];r=p['rule'];args=p['args'];dep=frozenset();counts[r]=counts.get(r,0)+1
  if r=='MP':
   need(len(args)==2 and all(type(j)==int and 0<=j<n for j in args),'MP dag')
   i,j=args;need(fs[ns[i]['formula']]==I(fs[ns[j]['formula']],f),'MP match');dep=opens[i]|opens[j]
  elif r=='GEN':
   i,j=args;need(type(i)==int and i>=0 and 0<=j<n,'GEN dag');need(not opens[j],'closed GEN');need(f==A(i,fs[ns[j]['formula']]),'GEN match')
  elif r=='HYP':dep=frozenset((f,))
  elif r=='TAUT':need(taut(f),'Boolean tautology')
  elif r=='K':need(f==I(f[1],I(f[2][1],f[1])),'K')
  elif r=='S':
   a,b,c=f[1][1],f[1][2][1],f[1][2][2];need(f==I(I(a,I(b,c)),I(I(a,b),I(a,c))),'S')
  elif r=='rho1':
   i=f[1][1];a=f[1][2][1];need(a[0]=='eq' and a[1]==i and f==X(i,a),'rho1')
  elif r=='rho2':
   i=f[1][1];a,b=f[1][2][1:];need(f==I(A(i,I(a,b)),I(A(i,a),A(i,b))),'rho2')
  elif r=='rho4':
   i,j,p=f[1][1],f[1][2][1],f[1][2][2];need(f==I(A(i,A(j,p)),A(j,A(i,p))),'rho4')
  elif r=='rho6':
   i=f[1][1][1];a=f[2];need(f==I(X(i,A(i,a)),a),'rho6')
  elif r in ('SYM','Sym'):
   a,b=f[1][1:];need(f==I(D(a,b),D(b,a)),'Sym')
  elif r=='rho3':
   a,b=f[1][1:];c=f[2][1][1];need(f==I(D(a,b),I(R(c,a),R(c,b))),'rho3')
  elif r=='rho5':
   a,b=f[1][1:];c=f[2][1][2];need(f==I(D(a,b),I(R(a,c),R(b,c))),'rho5')
  elif r=='rho7':
   c,a=f[1][1:];d,b=f[2][1][1:];need(c==d and f==I(D(c,a),I(D(c,b),D(a,b))),'rho7')
  elif r=='vacRel':
   a,b=f[1][1:];i=f[2][1];need(i not in (a,b) and f==I(R(a,b),A(i,R(a,b))),'gated membership vacuity')
  elif r=='V_eq':
   a,b=f[1][1:];need(f==I(D(a,b),A(code(a,b),D(a,b))),'actual canonical equality code')
  else:raise RuntimeError(('unlicensed leaf',r))
  opens.append(dep)
 need(set(raw['roots'])==set(expected),'root names')
 for k,n in raw['roots'].items():need(not opens[n] and fs[ns[n]['formula']]==expected[k],('closed expected root',k))
 return {'nodes':len(ns),'formulas':len(fs),'roots':len(expected),'rules':counts}

def body(a,b,z,out=False):
 p,q=(R(a,z),R(b,z)) if out else (R(z,a),R(z,b))
 return C(I(p,q),I(q,p))
def E(a,b,z=None):
 if z is None:z=code(a,b)
 return C(A(z,body(a,b,z)),A(z,body(a,b,z,True)))

def edge_suite():
 roots={};expected={}
 def add(k,p,e):roots[k]=p;expected[k]=e
 for a,b in ((0,2),(2,0),(0,0),(2,2),(2,7),(101,999)):
  z=code(a,b)
  for i in sorted({0,1,z,z+1,1024}-{a,b}):add(f'vac/{a}/{b}/{i}',g.e_vac(a,b,i),I(E(a,b),A(i,E(a,b))))
  for c in sorted({0,a,b,z,z+1}):
   add(f'in/{a}/{b}/{c}',g.e_rel(a,b,c),I(E(a,b),I(R(c,a),R(c,b))))
   add(f'out/{a}/{b}/{c}',g.e_rel(a,b,c,True),I(E(a,b),I(R(a,c),R(b,c))))
 for a,b,z,w in ((1,2,0,3),(1,2,3,0),(5,5,0,6),(5,5,6,0),(0,1,9,8),(100,999,0,1001)):
  add(f'aux/{a}/{b}/{z}/{w}',g.aux(a,b,z,w),I(E(a,b,z),E(a,b,w)))
 for a,b,c in ((0,0,0),(0,3,code(0,3)),(3,0,code(0,3)),(3,4,code(3,4)),(0,100,999),(999,0,100),(3,3,3)):
  add(f'rho7/{a}/{b}/{c}',g.e_rho7(a,b,c),I(E(c,a),I(E(c,b),E(a,b))))
 for a in (0,1,999):add(f'refl/{a}',g.e_refl(a),E(a,a))
 return replay(g.export(roots),expected)

def instantiate_bridge(a,b):
 raw=json.loads((SRC/'eq_to_indiscernibility_proofs.json').read_text())
 def inst(x):
  if x=='a':return a
  if x=='b':return b
  if not isinstance(x,list):return x
  if x[0]=='weq':return code(inst(x[1]),inst(x[2]))
  return tuple(inst(y) for y in x)
 # Remove projection nodes, retain canonical root dependency closure.
 selected={k:n for k,n in raw['roots'].items() if k.startswith('canonical')};used=set()
 def reach(n):
  if n in used:return
  used.add(n);p=raw['proof_nodes'][n]
  if p['rule']=='MP':
   for j in p['args']:reach(j)
  elif p['rule']=='GEN':reach(p['args'][1])
 for n in selected.values():reach(n)
 order=sorted(used);mp={n:k for k,n in enumerate(order)};ps=[];forms=[]
 for n in order:
  p=raw['proof_nodes'][n];args=p['args'];r=p['rule'];forms.append(inst(raw['formulas'][p['formula']]))
  args=[mp[j] for j in args] if r=='MP' else [inst(args[0]),mp[args[1]]] if r=='GEN' else []
  ps.append({'rule':r,'formula':len(forms)-1,'args':args})
 return replay({'formulas':forms,'proof_nodes':ps,'roots':{k:mp[n] for k,n in selected.items()}},{'canonical_Eq_to_E':I(D(a,b),E(a,b)),'canonical_exists_E':X(a,E(a,b))})

def original_equality(a,b,c):
 raw=json.loads((SRC/'equality_proofs.json').read_text())
 def inst(x):
  if x=='x':return a
  if x=='y':return b
  if x=='z':return c
  if not isinstance(x,list):return x
  if x[0]=='weq':return code(inst(x[1]),inst(x[2]))
  return tuple(inst(y) for y in x)
 raw['formulas']=[inst(f) for f in raw['formulas']]
 for p in raw['proof_nodes']:
  if p['rule']=='GEN':p['args'][0]=inst(p['args'][0])
 return replay(raw,{'equality_reflexivity':D(a,a),'equality_symmetry':I(D(a,b),D(b,a)),'equality_transitivity':I(D(a,b),I(D(b,c),D(a,c)))})

start=time.time();report={'valid':True,'edges':edge_suite(),'bridge_instantiations':{f'{a}/{b}':instantiate_bridge(a,b) for a,b in ((0,0),(0,1),(1,0),(1,1),(2,7),(100,999))},'scope':'Finite independent proof-local replay. No uniform-label theorem follows solely from these checks.'}
report['original_rho7_variant']={f'{a}/{b}/{c}':original_equality(a,b,c) for a,b,c in ((0,0,0),(0,1,2),(3,code(3,3),0),(100,999,2))}
report['seconds']=time.time()-start
report['inputs_sha256']={p.name:hashlib.sha256(p.read_bytes()).hexdigest() for p in (SRC/'indiscernibility_certificates.py',SRC/'eq_to_indiscernibility_proofs.json')}
Path(__file__).with_name('independent_results.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report,indent=2))
