"""Independent root, trace-zero Wick, and algebraic k2 checks; no recurrence."""
import sympy as s
import json, hashlib
from pathlib import Path
from functools import lru_cache
from itertools import product
out={}
k=s.symbols('k',positive=True,integer=True)
P2,P3,P4=s.symbols('P2 P3 P4')
mu=(k+1)/k**2; a=(k+1)*(k+2)/k**3
b=(k+1)*(k*k+6*k+6)/k**4
c=(k+1)*(k**3+14*k*k+36*k+24)/k**5
beta=a/mu
# Implicit radial branch from Taylor series of h(w)=q exp(w)/(1-q exp(w)).
s2=a*P2/(2*k*mu)
s3=s.I*b*P3/(6*k*mu)
s4=-a*s2**2/(2*mu)+b*s2*P2/(2*k*mu)-c*P4/(24*k*mu)
logB1=-k*s3
logB2=s.expand(-a*s2/mu+b*P2/(2*k*mu)-k*P2/12+(k-1)*(s2-mu*P2/2)-k*s4)
# Direct Wick contractions for trace-zero Hermitian Gaussian matrix.
# Cov(H_ab,H_cd)=delta_ad delta_bc - delta_ab delta_cd/k at beta=1.
def pairings(items):
 if not items:
  yield [];return
 for j in range(1,len(items)):
  for tail in pairings(items[1:j]+items[j+1:]):yield [(items[0],items[j])]+tail

def trace_moment(lengths):
 n=sum(lengths);edges=[];start=0
 for length in lengths:
  edges += [(start+i,start+(i+1)%length) for i in range(length)];start+=length
 ans=0
 for pairing in pairings(list(range(n))):
  for choices in product((0,1),repeat=n//2):
   parent=list(range(n))
   def find(x):
    while parent[x]!=x:x=parent[x]
    return x
   def union(x,y):parent[find(x)]=find(y)
   for (i,j),choice in zip(pairing,choices):
    aa,bb=edges[i];cc,dd=edges[j]
    for u,v in ([(aa,dd),(bb,cc)] if choice==0 else [(aa,bb),(cc,dd)]):union(u,v)
   ans += (-1/k)**sum(choices)*k**len({find(i) for i in range(n)})
 return s.factor(ans)
moments={name:trace_moment(ls)/beta**(sum(ls)//2) for name,ls in [('P2',[2]),('P2_squared',[2,2]),('P4',[4]),('P3_squared',[3,3])]}
assert s.factor(moments['P2']-(k*k-1)/beta)==0
assert s.factor(moments['P2_squared']-(k*k-1)*(k*k+1)/beta**2)==0
assert s.factor(moments['P4']-(k*k-1)*(2*k*k-3)/(k*beta**2))==0
assert s.factor(moments['P3_squared']-3*(k*k-1)*(k*k-4)/(k*beta**3))==0
B2=s.Poly(s.expand(logB2+logB1**2/2),P2,P3,P4)
expect={(1,0,0):moments['P2'],(2,0,0):moments['P2_squared'],(0,0,1):moments['P4'],(0,2,0):moments['P3_squared']}
d1=s.factor(sum(co*expect[ex] for ex,co in B2.terms()))
claimed=-(k-1)*(k+1)*(2*k**4+8*k**3+9*k*k+6*k+12)/(12*k*(k+2)**2)
assert s.factor(d1-claimed)==0
out['independent_trace_zero_Wick_moments']={n:str(s.factor(v)) for n,v in moments.items()}
out['independent_radial_d1']=str(d1)
# Independent direct chamber counting, small dimensions.
@lru_cache(None)
def paths(lam):
 if not any(lam):return 1
 total=0
 for i,z in enumerate(lam):
  for jump in range(1,z+1):
   nu=lam[:i]+(z-jump,)+lam[i+1:]
   if all(nu[j]>=nu[j+1] for j in range(len(lam)-1)):total+=paths(nu)
 return total
out['direct_counts']={str(kk):[paths((nn,)*kk) for nn in range(5)] for kk in range(2,5)}
# Explicit k=2 radial branch: h(x1)+h(x2)=1 implies
# 3 r^2 - 4 r cos(tu)+1=0, r=q exp(sigma), root r(0)=1/3.
t,u=s.symbols('t u', real=True)
r=(2*s.cos(t*u)-s.sqrt(4*s.cos(t*u)**2-3))/3
sigma=s.series(s.log(3*r),t,0,8).removeO()
# Compute log amplitude through t^4, using exact products for k=2.
# S = sum xi/(1-xi)^2 = 6-2/(1-2r cos(tu)+r^2) on branch sum h=1.
den=1-2*r*s.cos(t*u)+r*r
S=6-2/den
logB=s.series(s.log(s.Rational(3,2)/S)+2*s.log(s.sin(t*u)/(t*u))+s.log(s.Rational(4,9)/den)-2*sigma/t**2+2*u*u,t,0,6).removeO().expand()
B=s.series(s.exp(logB),t,0,5).removeO().expand()
# beta=2, trace-zero density proportional u^2 exp(-2u^2).
def eu_power(m):
 if m%2:return 0
 return s.rf(s.Rational(3,2),m//2)/2**(m//2)
def ev_u(expr):return s.simplify(sum(co*eu_power(ex[0]) for ex,co in s.Poly(expr,u).terms()))
k2=[ev_u(B.coeff(t,2*j)) for j in range(3)]
assert k2[0]==1 and k2[1]==-s.Rational(39,32)
# GF singular expansion from sqrt(1-10x+9x^2)=(1-9x)^1/2(1-x)^1/2.
# Exact transfer asymptotics to relative order 2 for powers 1/2,3/2,5/2.
z=s.symbols('z')
local=s.series(-s.sqrt(1-(1-z)/9)/(8*((1-z)/9)),z,0,3).removeO()
# coefficient (1-9x)^rho =9^n n^(-rho-1)/Gamma(-rho)*[1+rho(rho+1)/2n+rho(rho+1)(rho+2)(3rho+1)/24n²+...]
terms=[]
for j in range(3):
 rho=s.Rational(1,2)+j
 terms.append(s.simplify(local.coeff(z,j)/s.gamma(-rho)))
gf=[s.Integer(1),s.simplify(s.Rational(3,8)+terms[1]/terms[0]),s.simplify(s.Rational(25,128)+(terms[1]/terms[0])*s.Rational(15,8)+terms[2]/terms[0])]
assert k2==gf,(k2,gf)
out['k2_generator_coefficients']=list(map(str,k2));out['k2_algebraic_GF_coefficients']=list(map(str,gf))
out['status']='All independent assertions passed'
print(json.dumps(out,indent=2))
Path('radial-wick-checks.json').write_text(json.dumps(out,indent=2)+'\n')
