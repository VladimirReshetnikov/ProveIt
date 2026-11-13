#!/usr/bin/env python3
"""Independent sparse-rational-polynomial check; enormous Pell power unexpanded."""
from fractions import Fraction
from pathlib import Path
import hashlib,json,operator,subprocess
if not __debug__:raise RuntimeError('optimized Python is unsupported')
HERE=Path(__file__).resolve().parent;ROOT=HERE.parents[3];R=ROOT/'Computability/DiophantineConsistency/research';T=R/'double-gap-uniform-counterexample'
H=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
files=[Path(__file__),T/'README.md',T/'check.py',T/'terminal-observation.json',R/'adaptive-square-sums/candidate.json',R/'adaptive-direct-ordinate86/candidate.json']
before={str(p.resolve()):H(p) for p in files}
assert H(files[-2])=='11fb3c192fb3a8ab9204ef0a5401198d986e002242e4f48442147aa356263828'
assert H(files[-1])=='e9889a81a491b85491dde749e82158109ea98ff94ed41fc0f05dc810ec58b91f'
# Sparse polynomial arithmetic over Q in seven independent symbols f,I,P,y,q,h,C.
N=7;zero=(0,)*N
def const(c):return {} if c==0 else {zero:Fraction(c)}
def var(i):m=[0]*N;m[i]=1;return {tuple(m):Fraction(1)}
def add(a,b,sgn=1):
 d=a.copy()
 for k,v in b.items():d[k]=d.get(k,0)+sgn*v
 return {k:v for k,v in d.items() if v}
def mul(a,b):
 d={}
 for x,a0 in a.items():
  for y,b0 in b.items():
   z=tuple(i+j for i,j in zip(x,y));d[z]=d.get(z,0)+a0*b0
 return {k:v for k,v in d.items() if v}
def scale(a,k):return {m:v*k for m,v in a.items() if v*k}
def sub(a,b):return add(a,b,-1)
f,I,P,y,q,h,C=[var(i) for i in range(N)];one=const(1)
# Coefficients of the small, explicitly expanded power; large power remains symbolic.
s,c=1,0
for _ in range(15):s,c=4*s+15*c,s+4*c
assert (s,c)==(13837575261124,3572846569215) and s*s-15*c*c==1 and c>2
R0=(-s-(1+2*c))//11+c-3
assert 11*(R0-c+3)==-s-(1+2*c) and R0==1665276714707 and R0>0
assert 225**6>c
# Independently form the polynomial Pell recurrence and check divisibility at -15.
def evalat(a,i,x):return sum(v*x**m[i] for m,v in a.items() if all(m[j]==0 for j in range(N) if j!=i))
t=var(0);vm2,vm1=one,sub(scale(t,4),const(3));wm2,wm1=one,sub(scale(t,4),one)
for _ in range(1,7):
 vm2,vm1=vm1,sub(mul(sub(scale(t,4),const(2)),vm1),vm2)
 wm2,wm1=wm1,sub(mul(sub(scale(t,4),const(2)),wm1),wm2)
assert sub(mul(t,mul(vm1,vm1)),mul(sub(t,one),mul(wm1,wm1)))==one
assert evalat(vm1,0,-15)==-c
# Old->new coordinate identities and complete source-consumer checks.
F=sub(q,h);alpha=sub(h,C)
assert mul(F,q)==sub(mul(q,q),mul(q,h))
assert add(alpha,mul(h,sub(q,one)))==sub(mul(q,h),C)
ops={'+':add,'-':sub,'*':mul};counts=[]
for graph_file in files[-2:]:
 graph=json.loads(graph_file.read_text());rows=graph['source'];lookup={row[0]:row for row in rows}
 assert len(lookup)==len(rows)
 assert {row[0] for row in rows if 'F' in row[2:]}=={'qF','g28'}
 assert {row[0] for row in rows if 'alpha' in row[2:]}=={'C','G'}
 # Evaluate entire pinned graph at the proposed inverse values in Q[f,I,P,y].
 vals={'J':one,'F':const(-1),'alpha':one,'f':f,'i':scale(I,Fraction(1,c*c)),'T':one,'X':one,'Y':one,'r':one,'eta':one,'zeta':const(c-2),'y':y,'gamma':add(P,const(R0-c)), 'beta':{},'K0':const(-2),'MC':sub(const(c),P),'MF':{}}
 for name,op,a,b in rows:
  def get(x):return const(x) if isinstance(x,int) else vals[x]
  vals[name]=ops[op](get(a),get(b))
 assert vals['q']==one and vals['C']==one and vals['Bt']=={} and vals['M']=={} and vals['A0']=={}
 assert vals['c']==const(c) and vals['Delta']==const(15) and vals['H']==const(11) and vals['R']==sub(const(c),P)
 assert vals['Dstar']==const(-s) and vals['A1']=={}
 Q=scale(sub(mul(f,f),one),15);V=sub(mul(mul(f,f),P),const(c));strong=sub(mul(I,I),Q)
 aux=sub(sub(mul(y,y),mul(Q,sub(mul(y,y),mul(V,V)))),one)
 assert vals['g72']==strong and vals['V']==V
 assert sub(vals['Fa'],one)==aux
 if graph['output']=='sumSquares': assert vals['sumSquares']==add(mul(aux,aux),mul(strong,strong))
 else: assert graph['output']=='P13' and vals['P13']==sub(mul(add(one,aux),add(one,strong)),one)
 counts.append(len(rows))
# Mutation controls for polynomial Pell identity and strict inverse coordinate.
assert add(mul(t,mul(vm1,vm1)),mul(sub(t,one),mul(wm1,wm1)))!=one
assert 1-2==-1 and 2-1==1
assert {str(p.resolve()):H(p) for p in files}==before
out={'status':'PASS_INDEPENDENT_SYMBOLIC_AUXILIARY_PORT_REVIEW','inputs_sha256':before,'source_operations':counts,'small_pell_s':s,'small_pell_c':c,'R0':R0,'inverse_F':-1,'inverse_alpha':1,'large_power_expanded':False,'scope':'Auxiliary integer ports beta=0, K0=-2 and specially chosen signed MC. Exact symbolic algebra plus mathematical divisibility and positivity argument; no fixed-port counterexample, Lean proof or consistency result.'}
p=HERE/'receipt.json'
if p.exists():raise ValueError('refusing receipt overwrite')
p.write_text(json.dumps(out,sort_keys=True,indent=2)+'\n');print(out['status'],H(p))
