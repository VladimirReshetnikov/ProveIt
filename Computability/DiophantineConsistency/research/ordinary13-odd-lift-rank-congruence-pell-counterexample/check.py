#!/usr/bin/env python3
"""Exact fact-level counterexample using logarithmic-time modular powering."""
import hashlib,json,math,subprocess,sys
from pathlib import Path
root=Path(__file__).resolve().parents[2];here=Path(__file__).resolve().parent
for p,h in json.loads((here/'pins.json').read_text()).items():assert hashlib.sha256((root/p).read_bytes()).hexdigest()==h,p
prev=root/'research/ordinary13-parent-strong-subgroup-rank-congruence'
r=subprocess.run([sys.executable,'-I','-S','-B',str(prev/'check.py')],cwd=root,check=True,text=True,capture_output=True)
assert r.stdout==(prev/'receipt.json').read_text()
p=json.loads((root/'research/ordinary13-eta-zero-graph-adapter-audit/prototype.json').read_text());rows={x[0]:x[1:] for x in p['source']}
for k,v in {'I':['*','c2','i'],'Q':['*','Delta','rho'],'g72':['-','g71','Q'],
 'g74':['*','T','c'],'g75':['-','g74','R'],'g76':['*','f2','g75'],
 'V':['-','g76','c'],'y2':['*','n_y','n_y'],'Fa':['-','y2','g82']}.items():assert rows[k]==v
# Main/strong pairs are small exact integers, computed without any lookup.
def pell(A,n,mod=None):
 D=A*A-1
 def mul(x,y):
  v=(x[0]*y[0]+D*x[1]*y[1],x[0]*y[1]+x[1]*y[0])
  return tuple(z%mod for z in v) if mod else v
 ans=(1,0);base=(A,1)
 while n:
  if n&1:ans=mul(ans,base)
  base=mul(base,base);n//=2
 return ans
A=2;D=3;m=3;g,c=pell(A,m);f,v=pell(A,15)
assert (g,c,f,v)==(26,15,189750626,109552575)
I=D*v;i=I//(c*c)
assert (I,i)==(328657725,1460701) and I==c*c*i
assert I*I==D*(f*f-1) and f*f%c==1
ell=218943027;R=12;sigma=-1
assert ell%4==3 and ell%c==R%c and (R-m)%c!=0
assert pell(A,ell,f*f)[1]==c
assert (ell+sigma*R)%c==0
# The quotient W=x_ell(I)/I is computed as an integer polynomial in I².
# This never divides a modular residue, and the full Pell coordinates are not built.
mod=f*f*c;t=I*I%mod;j=(ell-1)//2;coef=(4*t-2)%mod
v0=1;v1=(4*t-3)%mod
# Binary power of [[coef,-1],[1,0]] to compute P_j(t) modulo f²*c.
def matmul(a,b):return ((a[0]*b[0]+a[1]*b[2])%mod,(a[0]*b[1]+a[1]*b[3])%mod,(a[2]*b[0]+a[3]*b[2])%mod,(a[2]*b[1]+a[3]*b[3])%mod)
z=(1,0,0,1);base=(coef,mod-1,1,0);n=j-1
while n:
 if n&1:z=matmul(z,base)
 base=matmul(base,base);n//=2
W=(z[0]*v1+z[1]*v0)%mod
assert W%(f*f)==(-c)%(f*f) and W%c==3
assert (W+c+f*f*R)%mod==0
# Reproduce the reported generalized-CRT index without invoking giant Pell values.
assert ell%3660==1827 and ell%3620==1807 and ell%39660==19827
print(json.dumps({'A':A,'Delta':D,'main_index':m,'c':c,'strong_f':f,'I':I,'i':i,
 'auxiliary_index':ell,'rank_placeholder':R,'sign_sigma':sigma,
 'modulus_f_squared':f*f,'quotient_mod_f_squared':W%(f*f),'quotient_mod_c':W%c,
 'original_scalar_c_divides_R_minus_m':False,'both_correlated_conditions':True,
 'positive_T_exists_by_exact_integer_recurrence':True,
 'giant_auxiliary_Pell_coordinates_materialized':False,
 'actual_graph_rank_or_graph_zero_proved':False,'lean_executed':False},indent=2,sort_keys=True))
