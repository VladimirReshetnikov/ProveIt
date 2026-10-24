#!/usr/bin/env python3
"""Supplemental finite controls, not substitutes for the unbounded proof."""
import json, math
from pathlib import Path

def need(x,msg):
 if not x:raise ValueError(msg)
def vp(n,p):
 n=abs(n);need(n!=0,'zero valuation');v=0
 while n%p==0:n//=p;v+=1
 return v
def pell(a,n,mod=None):
 D=a*a-1;out=(1,0);base=(a,1)
 def mul(x,y):
  u=x[0]*y[0]+D*x[1]*y[1];v=x[0]*y[1]+x[1]*y[0]
  return (u%mod,v%mod) if mod else (u,v)
 while n:
  if n&1:out=mul(out,base)
  n//=2
  if n:base=mul(base,base)
 return out
checks=0
for rho in range(2,31):
 for p in [2,3,5,7,11,13,17,19,23,29]:
  if rho%p:continue
  for D0 in [4,8,12,16,20,28,36,44]:
   xx,yy=pell(rho,D0)
   need(vp(yy,p)-vp(rho,p)==vp(D0,p),'second-coordinate lifting')
   need(vp(xx-1,p)==2*(vp(rho,p)+vp(D0,p))-(p==2),'first-coordinate lifting')
   for nu in [1,3,5,7,9]:
    x1,_=pell(rho,nu);x2,_=pell(rho,nu+D0)
    need(x1%rho==x2%rho==0,'odd quotient')
    need(vp((x2-x1)//rho,p)==vp(D0,p),'quotient isometry')
    checks+=1
A=2;R=3;c=15;s=2;target=4*s*c*c
m=1
while pell(A,m,target)[1]!=0 or m%2:m+=1
f,I=pell(A,m);need(I%target==0,'strong choice')
Delta=A*A-1;rho=Delta*I;r=I//(c*c);M=s*r
lam=4*m*f;d=math.lcm(lam,4*I);den=4*I*f*f
need(pell(A,lam,f*f)==(1,0),'actual squared-modulus period')
moduli=[8,9,25,32,27]
results=[]
for mod in moduli:
 vals=[]
 for h in range(mod):
  nu=R+d*h
  x,_=pell(rho,nu,rho*den*mod)
  need(x%rho==0,'division after modular quotient')
  V=x//rho
  numerator=V+c-f*f*(c-R)
  need(numerator%den==0,'integral T')
  vals.append((numerator//den)%mod)
 need(sorted(vals)==list(range(mod)),'supported residue permutation')
 results.append({'modulus':mod,'permutation':True,'first_residues':vals[:8]})
result={'status':'PASS','scope':'Supplemental finite lifting and fixed-pair interpolation controls; unbounded argument is in SEMANTIC_AUDIT.md.', 'lifting_cases':checks,'fixed_pair':{'A':A,'R':R,'c':c,'s':s,'m0':m,'I_bits':I.bit_length(),'f_bits':f.bit_length(),'4sc2_divides_I':True},'supported_modulus_permutations':results}
path=Path(__file__).with_name('INTERPOLATION_CONTROLS.json');path.write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
