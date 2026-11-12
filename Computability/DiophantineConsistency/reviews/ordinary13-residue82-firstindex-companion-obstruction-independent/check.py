#!/usr/bin/env python3
"""Independent invariant and modular complete-graph control; no Lean."""
import hashlib,json,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
D=Path(__file__).resolve().parents[2]
def pin(p,h):
 b=(D/p).read_bytes();assert hashlib.sha256(b).hexdigest()==h,p;return json.loads(b)
g=pin('research/ordinary13-residue-first82/candidate.json','bb90faa3815c5ff46f5fdbf41c2d001790d565baa17d97c79514c33fa928f1d2')
p=pin('research/ordinary13-qcube-unscale84/candidate.json','2293d98affce104dc1522ddd69a0cf904ee752034dbd8959f4d3f41a3c604a77')
author=pin('research/ordinary13-residue82-firstindex-companion-obstruction/result.json','9054e76ea5dc312b0952b945f256bee58bc7f6f1afdb7580ccdff5eca1763e38')
def var(x):return {(x,):1}
def add(a,b,k=1):
 d=a.copy()
 for t,c in b.items():d[t]=d.get(t,0)+k*c
 return {t:c for t,c in d.items() if c}
def mul(a,b):
 d={}
 for x,u in a.items():
  for y,v in b.items():
   t=tuple(sorted(x+y));d[t]=d.get(t,0)+u*v
 return {t:c for t,c in d.items() if c}
C=lambda n:{():n} if n else {}
m,j,h,w=map(var,['m','j','h','w']);D0=mul(m,add(m,C(1)));A=add(mul(C(2),m),C(1));T=add(C(1),mul(C(2),mul(m,h)));K=add(mul(C(2),j),mul(C(4),mul(m,w)))
T1=add(mul(A,T),mul(C(2),mul(D0,K)));K1=add(mul(C(2),T),mul(A,K))
h1=add(add(C(1),mul(A,h)),add(mul(C(2),mul(add(m,C(1)),j)),mul(C(4),mul(D0,w))))
w1=add(add(h,j),mul(A,w))
assert T1==add(C(1),mul(C(2),mul(m,h1))) and K1==add(mul(C(2),add(j,C(1))),mul(C(4),mul(m,w1)))
T,K=map(var,['tau','k']);T1=add(mul(A,T),mul(C(2),mul(D0,K)));K1=add(mul(C(2),T),mul(A,K))
assert add(mul(T1,T1),mul(D0,mul(K1,K1)),-1)==add(mul(T,T),mul(D0,mul(K,K)),-1)
q=47;beta=46;Y=q**3;mv=q*Y**2;R=(45+beta**2)*(q*q-1)+1+q;n=(R+1+q**4)//2
assert R==4771536 and n==4825609 and (R+1+q**4)%2==0 and n>=13
assert R+q**3+q+1<=q**4 and q**4<mv and mv%q**4==0
# Independent modular 2x2 matrix exponentiation of the recurrence.
def matmul(x,y,mod):
 return tuple(sum(x[2*i+k]*y[2*k+j] for k in range(2))%mod for i in range(2) for j in range(2))
def pell(mod):
 mat=((2*mv+1)%mod,(2*mv*(mv+1))%mod,2,(2*mv+1)%mod);acc=(1,0,0,1);power=n;steps=0
 while power:
  if power&1:acc=matmul(acc,mat,mod)
  mat=matmul(mat,mat,mod);power//=2;steps+=1
 return acc[0],acc[2],steps
T4,K4,steps=pell(4*mv)
assert T4%(2*mv)==1 and (K4-2*n)%(4*mv)==0 and K4%(q**4)==(R+1)%(q**4)
mod=1000003;T,K,steps2=pell(mod);assert steps==steps2==23
r=(45*K+1+T-mv*K)%mod
witness={'J':1,'F':1,'alpha':45,'f':2,'i':1,'T':1,'X':q,'s':1,'r':r,'eta':1,'zeta':(K-1)%mod,'y':1,'gamma':1}
ports={'beta':beta,'K0':0,'MC':1,'MF':1}
def calc(graph):
 env={**ports,**witness}
 for name,op,a,b in graph['source']:
  aa=a if type(a) is int else env[a];bb=b if type(b) is int else env[b]
  env[name]=(aa*bb if op=='*' else aa+bb if op=='+' else aa-bb)%mod
 return env
u=calc(g);v=calc(p)
assert u['A0']==0 and u['Bt']==46 and v['Bt']==0 and u['g72']==330566 and u['out']==937166
assert u['out']!=0 and u['g72']!=0 and q<q*q and 0<ports['MC']<beta and 0<ports['MF']<2*beta
assert author['graph_output_mod']==u['out'] and author['graph_strong_residual_mod']==u['g72']
print(json.dumps({'scope':'exact recurrence invariants and independent modular full-graph evaluation; partial assignment only, no Lean','symbolic_index':n,'matrix_exponent_steps':steps,'first_residual_zero_mod':True,'strong_residual_mod':u['g72'],'output_mod':u['out'],'output_nonzero':True,'companion_B_zero':True,'toy_ports_not_compact':True,'lean_elaborated':False},sort_keys=True,indent=2))
