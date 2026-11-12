#!/usr/bin/env python3
"""Symbolic Pell invariants and logarithmic modular graph check; no huge integers."""
from pathlib import Path
import hashlib,json,sys
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
P=Path(__file__).resolve().parent;D=P.parents[1]
def pin(p,h):
 b=p.read_bytes();assert hashlib.sha256(b).hexdigest()==h,str(p);return json.loads(b)
g=pin(D/'research/ordinary13-residue-first82/candidate.json','bb90faa3815c5ff46f5fdbf41c2d001790d565baa17d97c79514c33fa928f1d2')
p=pin(D/'research/ordinary13-qcube-unscale84/candidate.json','2293d98affce104dc1522ddd69a0cf904ee752034dbd8959f4d3f41a3c604a77')
# Generic polynomial arithmetic validates the two exact inductive invariants.
def con(n):return {():n} if n else {}
def var(n):return {(n,):1}
def add(a,b,s=1):
 z=dict(a)
 for m,v in b.items():z[m]=z.get(m,0)+s*v
 return {m:v for m,v in z.items() if v}
def mul(a,b):
 z={}
 for x,u in a.items():
  for y,v in b.items():
   m=tuple(sorted(x+y));z[m]=z.get(m,0)+u*v
 return {m:v for m,v in z.items() if v}
m,n,h,w=map(var,['m','n','h','w']);T=add(con(1),mul(con(2),mul(m,h)));K=add(mul(con(2),n),mul(con(4),mul(m,w)))
A=add(mul(con(2),m),con(1));Delta=mul(m,add(m,con(1)))
Tnext=add(mul(A,T),mul(con(2),mul(Delta,K)));Knext=add(mul(con(2),T),mul(A,K))
hnext=add(add(con(1),mul(A,h)),add(mul(con(2),mul(add(m,con(1)),n)),mul(con(4),mul(Delta,w))))
wnext=add(add(h,n),mul(A,w))
assert Tnext==add(con(1),mul(con(2),mul(m,hnext)))
assert Knext==add(mul(con(2),add(n,con(1))),mul(con(4),mul(m,wnext)))
# Norm invariance is a polynomial identity, independent of the numerical index.
t0,k0=map(var,['tau','k']);tn=add(mul(A,t0),mul(con(2),mul(Delta,k0)));kn=add(mul(con(2),t0),mul(A,k0))
assert add(mul(tn,tn),mul(Delta,mul(kn,kn)),-1)==add(mul(t0,t0),mul(Delta,mul(k0,k0)),-1)
q=47;b=46;Y=q**3;mv=q*Y*Y;Rv=(45+b*b)*(q*q-1)+1+q;nval=(Rv+1+q**4)//2
assert q==b+1 and Rv==4771536 and Rv+q**3+q+1<=q**4 and 24<=Rv and (Rv+1+q**4)%2==0
assert nval==4825609 and nval>=13 and 2*nval==Rv+1+q**4 and mv%q**4==0
# Fast exponentiation of the Pell unit in a quadratic ring modulo modulus.
def pell(mod):
 dd=mv*(mv+1)%mod
 def step(x,y):return ((x[0]*y[0]+dd*x[1]*y[1])%mod,(x[0]*y[1]+x[1]*y[0])%mod)
 acc=(1,0);base=((2*mv+1)%mod,2);power=nval;steps=0
 while power:
  if power&1:acc=step(acc,base)
  base=step(base,base);power//=2;steps+=1
 return acc,steps
(tau4,k4),steps=pell(4*mv);assert tau4%(2*mv)==1 and (k4-2*nval)%(4*mv)==0 and k4%q**4==(Rv+1)%q**4
mod=1000003;(tau,k),steps2=pell(mod);assert steps==steps2==23
r=(k*45+1+tau-mv*k)%mod
ports={'beta':b,'K0':0,'MC':1,'MF':1}
v={'J':1,'F':1,'alpha':45,'f':2,'i':1,'T':1,'X':q,'s':1,'r':r,'eta':1,'zeta':(k-1)%mod,'y':1,'gamma':1}
def evaluate(graph):
 env={**ports,**v}
 for name,o,a,c in graph['source']:
  a=a if type(a) is int else env[a];c=c if type(c) is int else env[c]
  env[name]=(a*c if o=='*' else a+c if o=='+' else a-c)%mod
 return env
new=evaluate(g);old=evaluate(p)
assert new['A0']==0 and new['Bt']==46 and old['Bt']==0 and new['g72']!=0
assert new['out']!=0 and v['X']<q*q
print(json.dumps({'scope':'symbolic positive first-norm/rank-congruence control; other residuals are not assumed zero; no Lean','beta':b,'q':q,'Y':Y,'m':mv,'rank':Rv,'index':nval,'modulus_q4':q**4,'k_minus_2n_divisible_by_4m':True,'k_mod_q4':k4%(q**4),'rank_plus_one':Rv+1,'residue_carrier':46,'companion_carrier':0,'ray_modulus':mod,'graph_first_residual_mod':new['A0'],'graph_strong_residual_mod':new['g72'],'graph_output_mod':new['out'],'full_output_nonzero':True,'binary_exponent_steps':steps,'lean_elaboration':False},sort_keys=True,indent=2))
