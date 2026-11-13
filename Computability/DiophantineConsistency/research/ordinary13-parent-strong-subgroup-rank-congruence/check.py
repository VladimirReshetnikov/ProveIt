#!/usr/bin/env python3
"""Bounded checks for universal subgroup descent and correlated congruences."""
import hashlib,json,math,subprocess,sys
from pathlib import Path
root=Path(__file__).resolve().parents[2];here=Path(__file__).resolve().parent
for p,h in json.loads((here/'pins.json').read_text()).items():assert hashlib.sha256((root/p).read_bytes()).hexdigest()==h,p
prev=root/'research/ordinary13-parent-even-index-unconditional-same-data-obstruction'
r=subprocess.run([sys.executable,'-I','-S','-B',str(prev/'check.py')],cwd=root,check=True,text=True,capture_output=True)
assert r.stdout==(prev/'receipt.json').read_text()
def pell(d,a,b,n,mod=None):
 def mul(x,y):
  z=(x[0]*y[0]+d*x[1]*y[1],x[0]*y[1]+x[1]*y[0])
  return tuple(v%mod for v in z) if mod else z
 out=(1,0);v=(a,b)
 while n:
  if n&1:out=mul(out,v)
  v=mul(v,v);n//=2
 return out
units=[(2,3,2),(3,2,1),(5,9,4),(6,5,2),(7,8,3),(10,19,6),(15,4,1)]
growth=0
for d,a,b in units:
 for r0 in range(1,5):
  A,t=pell(d,a,b,r0)
  for m in range(2,12):
   N=r0*m;k=N//2;_,u=pell(d,a,b,N);_,uk=pell(d,a,b,k)
   assert u>m*t*uk,(d,r0,m)
   growth+=1
# Exact odd-main fact-level control where h=15 is odd (rather than our even construction).
A=2;D=3;m=3;c=15;h=15;f,v=pell(D,A,1,h)
assert h%m==0 and h%2==1 and (D*v)%(c*c)==0
I=D*v;assert I*I==D*(f*f-1) and (f*f-1)%c==0
R=18;ell=3;sigma=-1;x,y=pell(I*I-1,I,1,ell);assert x%I==0
V=x//I;Tnum=V+c+f*f*R;assert Tnum%(f*f*c)==0
T=Tnum//(f*f*c)
assert T>0 and V==f*f*(T*c-R)-c and y*y-I*I*(y*y-V*V)==1
_,yl=pell(D,A,1,ell)
assert (yl+sigma*c)%(f*f)==0 and (ell+sigma*R)%c==0
# An independent bounded search checks the weaker c|I-based h multiple rm condition.
cases=hits=0
for A0 in range(2,81):
 Delta=A0*A0-1;z=Delta;d=t=1
 for p in range(2,math.isqrt(Delta)+1):
  e=0
  while z%p==0:z//=p;e+=1
  if e:d*=p**(e%2);t*=p**(e//2)
  if z==1:break
 if z>1:d*=z
 for b in range(1,t+1):
  a=math.isqrt(1+d*b*b)
  if a*a==1+d*b*b:break
 xx,uu=1,0
 for rr in range(1,100):
  xx,uu=a*xx+d*b*uu,b*xx+a*uu
  if xx>=A0:break
 assert (xx,uu)==(A0,t)
 xx,c0=1,0
 for mm in range(1,8):
  xx,c0=A0*xx+Delta*c0,xx+A0*c0
  if mm<2:continue
  mod=c0//math.gcd(c0,d*t)
  if mod>300000:continue
  aa,bb=1%mod,0;cases+=1
  for hh in range(1,5001):
   aa,bb=(a*aa+d*b*bb)%mod,(b*aa+a*bb)%mod
   if bb==0:
    hits+=1;assert hh%(rr*mm)==0,(A0,mm,rr,hh)
   if (aa,bb)==(1%mod,0):break
print(json.dumps({'prior_even_obstruction_reproduced':True,'Pell_growth_controls':growth,
 'bounded_kernel_cases':cases,'bounded_strong_index_hits':hits,
 'all_hits_multiples_of_rm':True,'odd_h_fact_level_toy':[A,m,h,R,ell,T],
 'correlated_sign_congruences_checked':True,'scalar_R_plusminus_m_proved':False,
 'actual_full_graph_zero_constructed':False,'lean_executed':False},indent=2,sort_keys=True))
