#!/usr/bin/env python3
"""Exact checks for the second sparse p-adic root jump; no floating-point roots."""
from fractions import Fraction as F
from math import comb, gcd, lcm
from pathlib import Path
import json, sys, importlib.util
sys.path.insert(0,str(Path(__file__).parent))
from modp_scan import score, compositions


def vp(a,p):
 if not a:return None
 a=F(a);num=abs(a.numerator);den=a.denominator;r=0
 while num%p==0:num//=p;r+=1
 while den%p==0:den//=p;r-=1
 return r

def pmul(a,b):
 c=[0]*(len(a)+len(b)-1)
 for i,x in enumerate(a):
  for j,y in enumerate(b):c[i+j]+=x*y
 return c

def lam(p,j):
 return (pow(2,j,p)-2+(j==0)-2*j+2*(j==1)+2*(j==2)-(comb(j,p) if j>=p else 0)+(j==p)+(j==p+1))%p

def witness(p):
 assert p>=5
 E=sorted([p*j for j in range(p+2)]+[1+p*j for j in range(p+1)]+[2])
 t=len(E);K=p*p+p;M=[lam(p,j) for j in range(t)]
 assert t==2*p+4 and max(E)==K and M[0]==0
 cs=[]
 for n in E:
  a=[1];den=1
  for e in E:
   if e!=n:a=pmul(a,[-e,1]);den*=n-e
  cs.append(F(sum(x*y for x,y in zip(a,M)),den))
 for j,m in enumerate(M):assert sum(c*e**j for e,c in zip(E,cs))==m
 den=lcm(*(c.denominator for c in cs));cs=[int(c*den) for c in cs];g=gcd(*cs);cs=[c//g for c in cs]
 r=F(1,p-1)+F(1,2*(p-1)*K)
 def count(coeffs):
  vals=[]
  for j in range(K+1):
   a=sum(c*comb(e,j) for e,c in zip(E,coeffs) if e>=j)
   if a:vals.append((vp(a,p)+r*j,j))
  mu=min(v for v,j in vals);return max(j for v,j in vals if v==mu),mu
 N,mu=count(cs);assert N==K,(p,N,K)
 B=mu.numerator//mu.denominator+1;step=p**B
 cs=[c if c else step for c in cs]
 import sympy as sp
 x=sp.Symbol('X')
 for attempt in range(K+1):
  poly=sp.Poly.from_dict({(e,):c for e,c in zip(E,cs)},x,domain=sp.ZZ)
  if sp.gcd(poly,poly.diff()).degree()==0:break
  cs[0]+=step
 else:raise AssertionError('No squarefree perturbation')
 assert count(cs)==(N,mu)
 return {'p':p,'terms':t,'degree':K,'root_count':N,'closed_depth':str(r),'minimum_weight':str(mu),'squarefree':True,'perturbation_attempt':attempt,'coefficients':[[e,str(c)] for e,c in zip(E,cs)]}

def polynomial_checks(p,nu):
 """Verify normal-form relations independently on every local residue factor."""
 import sympy as sp
 x,y,z=sp.symbols('x y z');u=sp.Symbol('u')
 heavy=[c for c,v in enumerate(nu) if v>p];occ=[c for c,v in enumerate(nu) if v]
 if not heavy:rels=[z-y]
 elif len(heavy)==1 and nu[heavy[0]]<=2*p:
  c=heavy[0];rels=[y*z-y*y+c*y-c*z,z*z-y*y+2*c*y-2*c*z]
 elif len(heavy)==2 and len(occ)==2:
  c,d=heavy;rels=[z*z-(c+d)*z+c*d,2*y*z-y*y-(c+d)*z+c*d]
 elif len(heavy)==2 and max(nu[c]-p for c in heavy)==1:
  rels=[y*z-x*z-y*y+x*y,z*z-2*x*z-y*y+2*x*y]
 elif len(heavy)==2:
  c=next(c for c in heavy if nu[c]==p+2)
  rels=[(y-z)**2,(x-c)*(x-y)*(y-z),(y-c)*(x-y)*(y-z)]
 else:
  # The proof uses degree <= 2 CRT representatives for the two cubic relations.
  c=heavy[0]
  rels=[(z-c)*(y-z)]
 for rel in rels:
  for c,v in enumerate(nu):
   if not v:continue
   poly=sp.Poly(sp.expand(rel.subs({x:c+u,y:c+u**p,z:c},simultaneous=True)),u)
   assert all(int(coef)%p==0 for (power,),coef in poly.terms() if power<v),(p,nu,rel,c)
 return len(rels)

if __name__=='__main__':
 import argparse,time
 ap=argparse.ArgumentParser();ap.add_argument('--output',type=Path,default=Path(__file__).with_name('new_phase_certificates.json'));ap.add_argument('--large',action='store_true');a=ap.parse_args()
 out={'method':'Exact integer Taylor coefficient valuations, exact polynomial gcd, and residue-algebra identities.','witnesses':[],'profile_checks':[],'identity_checks':[]}
 for p in ([5,7,11,13,17] if a.large else [5,7,11]):
  row=witness(p);out['witnesses'].append(row);print('witness',p,row['root_count'],flush=True)
 for p,t in [(5,12),(5,13),(5,14)]:
  best=-1;examples=[];count=0
  for nu in compositions(t,p):
   if nu[0]<max(nu):continue
   val,_=score(p,nu);count+=1
   if val>best:best=val;examples=[nu]
   elif val==best:examples.append(nu)
  assert best==(p*p+p if t==2*p+4 else p*p+(t-p)//2-1)
  out['profile_checks'].append({'p':p,'t':t,'profiles_up_to_translation':count,'maximum':best,'maximizing_profiles':examples})
  print('profiles',p,t,count,best,flush=True)
 for p in [5,7,11]:
  cases=[(p, p, 4), (p+2,p+1,1), (p+3,p+1,0),(p+2,p+2,0),(2*p+1,2,1),(2*p+2,1,1),(2*p+3,1,0)]
  for a0,a1,a2 in cases:
   nu=(a0,a1,a2)+(0,)*(p-3)
   # Only use patterns covered by total budget.
   assert sum(nu)==2*p+4
   out['identity_checks'].append({'p':p,'multiplicities':nu,'relations_checked':polynomial_checks(p,nu)})
 print('PASS',len(out['witnesses']),'witnesses',len(out['profile_checks']),'profile searches',len(out['identity_checks']),'identity cases',flush=True)
 a.output.write_text(json.dumps(out,indent=2)+'\n')
