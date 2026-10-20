#!/usr/bin/env python3
"""Independent strict DAG replay of new witnessed-equality bootstrap artifacts.
Imports no proof generator/checker. Formula DAG interning avoids repeated large
structural hashes. Only explicit local rules and Boolean tautologies are used.
"""
from pathlib import Path
from functools import cache
from itertools import product
import argparse,json,hashlib,time
ap=argparse.ArgumentParser();ap.add_argument('certificate',type=Path);ap.add_argument('--symmetric',action='store_true');ap.add_argument('--tag',type=int,default=1,choices=(1,3));ap.add_argument('--output',type=Path,required=True);a=ap.parse_args();start=time.monotonic()
def need(x,m):
 if not x:raise ValueError(m)
def nat(x):return type(x) is int and x>=0
DAG=[];ids={}
def make(tag,*fields):
 k=(tag,*fields)
 if k not in ids:ids[k]=len(DAG);DAG.append(k)
 return ids[k]
def parse(f):
 need(type(f) is list and f and type(f[0]) is str,'Malformed formula')
 tag=f[0]
 if tag in ('eq','rel'):
  need(len(f)==3 and all(nat(v) for v in f[1:]),'Non-natural atomic label');return make(tag,*f[1:])
 if tag=='all':
  need(len(f)==3 and nat(f[1]),'Non-natural binder');return make(tag,f[1],parse(f[2]))
 need(tag=='imp' and len(f)==3,'Unknown constructor/arity');return make(tag,parse(f[1]),parse(f[2]))
I=lambda p,q:make('imp',p,q);Q=lambda i,p:make('all',i,p);R=lambda x,y:make('rel',x,y);Eq=lambda x,y:make('eq',x,y)
F=R(0,0);N=lambda p:I(p,F);Ex=lambda i,p:N(Q(i,N(p)));And=lambda p,q:N(I(p,N(q)))
def code(x,y,tag):return 4*((x+y)*(x+y+1)//2+y)+tag
rawbytes=a.certificate.read_bytes();digest=hashlib.sha256(rawbytes).hexdigest();data=json.loads(rawbytes);del rawbytes
rawforms=data.pop('formulas');need(type(rawforms) is list,'Formula collection type');forms=[]
if data.get('format')=='formula_dag_v1':
 for j,f in enumerate(rawforms):
  need(type(f) is list and len(f)==3 and type(f[0]) is str,'Malformed DAG formula')
  tag,x,y=f
  if tag in ('eq','rel'):
   need(nat(x) and nat(y),'Non-natural atomic label');forms.append(make(tag,x,y))
  elif tag=='all':
   need(nat(x) and type(y) is int and 0<=y<j,'Invalid DAG binder/child');forms.append(Q(x,forms[y]))
  else:
   need(tag=='imp' and all(type(k) is int and 0<=k<j for k in (x,y)),'Invalid DAG implication/children');forms.append(I(forms[x],forms[y]))
else:
 need(data.get('format') is None,'Unknown certificate format');forms=[parse(f) for f in rawforms]
del rawforms
proof=data['proof_nodes'];need(type(proof) is list,'Proof collection type');need(data.get('kappa_tag')==a.tag,'Wrong tag metadata')
@cache
def atoms(f):
 if f==F:return frozenset()
 t=DAG[f]
 return atoms(t[1])|atoms(t[2]) if t[0]=='imp' else frozenset((f,))
maxatoms=0
@cache
def taut(f):
 global maxatoms
 av=sorted(atoms(f));k=len(av);maxatoms=max(maxatoms,k);need(k<=20,'Too many propositional atoms')
 n=1<<k;full=(1<<n)-1;vals={}
 for i,v in enumerate(av):
  block=1<<i;vals[v]=(full//((1<<(2*block))-1))*(((1<<block)-1)<<block)
 @cache
 def ev(q):
  if q==F:return 0
  t=DAG[q]
  return ((~ev(t[1])|ev(t[2]))&full) if t[0]=='imp' else vals[q]
 return ev(f)==full
@cache
def labels(f):
 if f==F:return frozenset()
 t=DAG[f]
 if t[0] in ('eq','rel'):return frozenset(t[1:])
 if t[0]=='imp':return labels(t[1])|labels(t[2])
 return frozenset((t[1],))|labels(t[2])
@cache
def rename(f,x,y):
 if f==F:return F
 t=DAG[f]
 if t[0]=='rel':return R(*(y if v==x else v for v in t[1:]))
 need(t[0]=='imp','Non-QF rename');return I(rename(t[1],x,y),rename(t[2],x,y))
def d(n):return DAG[n]
opens=[];counts={}
for j,node in enumerate(proof):
 need(type(node) is dict and set(node)=={'rule','formula','args'},'Malformed proof record')
 r,index,args=node['rule'],node['formula'],node['args'];need(type(index) is int and 0<=index<len(forms),'Formula index');need(type(args) is list,'Args type');f=forms[index];t=d(f);deps=frozenset();counts[r]=counts.get(r,0)+1
 if r=='MP':
  need(len(args)==2 and all(type(i) is int and 0<=i<j for i in args),'MP prior nonnegative indices');major,minor=args
  need(forms[proof[major]['formula']]==I(forms[proof[minor]['formula']],f),'MP mismatch');deps=opens[major]|opens[minor]
 elif r=='GEN':
  need(len(args)==2 and nat(args[0]) and type(args[1]) is int and 0<=args[1]<j,'GEN indices/binder');i,k=args;need(not opens[k] and f==Q(i,forms[proof[k]['formula']]),'Open/wrong GEN')
 elif r=='HYP':need(not args,'HYP args');deps=frozenset((f,))
 else:
  need(not args,'Axiom/tautology arguments')
  if r=='TAUT':need(taut(f),'False Boolean tautology')
  elif r=='K':need(t[0]=='imp' and d(t[2])[0]=='imp' and f==I(t[1],I(d(t[2])[1],t[1])),'K schema')
  elif r=='S':
   x=d(t[1])[1];y=d(d(t[1])[2])[1];z=d(d(t[1])[2])[2];need(f==I(I(x,I(y,z)),I(I(x,y),I(x,z))),'S schema')
  elif r=='UW':
   x=d(t[1])[1];inside=d(d(t[1])[2])[1];k=d(inside)[1];body=d(inside)[2]
   if a.symmetric:
    atom=d(d(body)[1])[1];need(d(atom)[0]=='eq','UW symmetric atom');xx,y=d(atom)[1:];want=And(Eq(x,y),Eq(y,x))
   else:
    need(d(body)[0]=='eq','UW atom');xx,y=d(body)[1:];want=Eq(x,y)
   need(xx==x and k==code(x,y,a.tag) and f==Ex(x,Q(k,want)),'Wrong UW instance')
  elif r=='SYM':
   need(not a.symmetric,'Forbidden SYM in symmetric witness basis');x,y=d(t[1])[1:];need(f==I(Eq(x,y),Eq(y,x)),'SYM schema')
  elif r=='rho2':
   i,sub=d(t[1])[1:];x,y=d(sub)[1:];need(f==I(Q(i,I(x,y)),I(Q(i,x),Q(i,y))),'rho2 schema')
  elif r=='rho4':
   i,sub=d(t[1])[1:];k,x=d(sub)[1:];need(f==I(Q(i,Q(k,x)),Q(k,Q(i,x))),'rho4 schema')
  elif r=='rho6':
   i=d(d(t[1])[1])[1];x=t[2];need(f==I(Ex(i,Q(i,x)),x),'rho6 schema')
  elif r in ('rho3','rho5'):
   x,y=d(t[1])[1:];first=d(d(t[2])[1]);z=first[1] if r=='rho3' else first[2];want=I(Eq(x,y),I(R(z,x),R(z,y))) if r=='rho3' else I(Eq(x,y),I(R(x,z),R(y,z)));need(f==want,r+' schema')
  elif r=='vacRel':
   x,y=d(t[1])[1:];i=d(t[2])[1];need(i not in (x,y) and f==I(R(x,y),Q(i,R(x,y))),'Membership vacuity/freshness')
  else:raise ValueError('Forbidden rule '+str(r))
 opens.append(deps)
 if (j+1)%100000==0:print('Checked',j+1,'nodes',flush=True)
def body(x,y,z,out=False):
 p,q=(R(x,z),R(y,z)) if out else (R(z,x),R(z,y));return And(I(p,q),I(q,p))
def Ez(x,y,z):need(z not in (x,y),'Unsafe E binder');return And(Q(z,body(x,y,z)),Q(z,body(x,y,z,True)))
def E(x,y):return Ez(x,y,code(x,y,3))
expected={}
for x,y in ((0,1),(1,0),(1,1),(0,0),(2,5)):
 z=code(x,y,3);w=z+1
 expected[f'exists_e_{x}_{y}']=Ex(x,E(x,y));expected[f'aux_{x}_{y}']=I(Ez(x,y,z),Ez(x,y,w));expected[f'aux_reverse_{x}_{y}']=I(Ez(x,y,w),Ez(x,y,z));expected[f'vac_internal_{x}_{y}']=I(E(x,y),Q(z,E(x,y)));expected[f'vac_external_{x}_{y}']=I(E(x,y),Q(w,E(x,y)))
 for c in (0,1,z):expected[f'rel_in_{x}_{y}_{c}']=I(E(x,y),I(R(c,x),R(c,y)));expected[f'rel_out_{x}_{y}_{c}']=I(E(x,y),I(R(x,c),R(y,c)))
for x,y,z in product(range(2),repeat=3):expected[f'e_rho7_{x}_{y}_{z}']=I(E(z,x),I(E(z,y),E(x,y)))
expected['e_rho7_distinct']=I(E(2,0),I(E(2,1),E(0,1)));expected['e_refl_zero']=E(0,0)
for x,y in ((0,0),(0,1),(1,0)):
 f=And(I(R(x,1),R(x,code(x,y,a.tag))),I(R(x,code(x,y,a.tag)),R(x,1)));expected[f'qf_spec_collision_{x}_{y}']=I(Q(x,f),rename(f,x,y))
for i in (0,1,2):expected[f'serial_{i}']=I(Q(i,F),F)
roots=data['roots'];need(set(roots)==set(expected),'Wrong root names')
for name,n in roots.items():need(type(n) is int and 0<=n<len(proof) and not opens[n] and forms[proof[n]['formula']]==expected[name],'Wrong/open root '+name)
result={'status':'STRICT_INDEPENDENT_WITNESSED_EQUALITY_PASS','symmetric_witness':a.symmetric,'tag':a.tag,'proof_nodes':len(proof),'formula_roots':len(forms),'interned_formula_nodes':len(DAG),'closed_roots':len(expected),'rules':counts,'maximum_tautology_atoms':maxatoms,'certificate_sha256':digest,'seconds':time.monotonic()-start,'checker_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),'scope':'Exact finite proof-local replay with independent natural-label/formula syntax, nonnegative earlier indices, explicit allowed-rule set, closed GEN, expected roots and Boolean TAUT checks. Uniform arbitrary-label and K-code coupling argument is separate; no source/machine state reduction certified.'};a.output.write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2),flush=True)
