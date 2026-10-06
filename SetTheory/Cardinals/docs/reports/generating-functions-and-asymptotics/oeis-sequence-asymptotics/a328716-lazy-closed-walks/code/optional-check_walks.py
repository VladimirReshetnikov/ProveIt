#!/usr/bin/env python3
"""Exact counts, symbolic saddle corrections, and high-precision diagnostics for A328716."""
import json, math, sys
sys.dont_write_bytecode = True
from pathlib import Path
import sympy as s
import mpmath as mp
ROOT=Path(__file__).absolute().parent
from utility import finish, need
b,v,x,a,z=s.symbols('b v x a z')
R=3
# D = z d/dz, x=z^2, a=D log I_0(2z)
kap={1:a}
for j in range(2,2*R+3):
 kap[j]=s.expand(2*x*s.diff(kap[j-1],x)+(4*x-a*a)*s.diff(kap[j-1],a))
k={j:s.factor(q.subs({a:1,x:(b+1)/4})) for j,q in kap.items()}
mu={j:sum(s.functions.combinatorial.numbers.stirling(j,h,kind=2)*((b+1)/4)**(h//2)*(v if h%2 else 1) for h in range(j+1)) for j in range(2*R+1)}
mu[0]=s.Integer(1)
def partitions_weight(total,h=3):
 if total==0:
  yield {}; return
 if h>total+2:return
 for m in range(total//(h-2)+1):
  for tail in partitions_weight(total-m*(h-2),h+1):
   yield ({h:m}|tail) if m else tail
S=[]
for ell in range(R+1):
 acc=0
 for j in range(2*ell+1):
  for counts in partitions_weight(2*ell-j):
   deg=j+sum(h*m for h,m in counts.items())
   term=mu[j]/s.factorial(j)*(-1)**(deg//2)*s.factorial2(deg-1)/b**(deg//2)
   for h,m in counts.items():term*=k[h]**m/(s.factorial(m)*s.factorial(h)**m)
   acc+=term
 S.append(s.factor(acc))
st=[1,s.Rational(1,12),s.Rational(1,288),-s.Rational(139,51840)]
cs=[s.factor(sum(st[j]*S[ell-j] for j in range(ell+1))) for ell in range(R+1)]
need(s.simplify(cs[1]-((9-7*b)/(24*b)-s.Rational(5,6)/b**3+(2-b)*v/(2*b*b)))==0, "optional independent identity failed")
mp.mp.dps=80
r=mp.findroot(lambda r:2*r*mp.besseli(1,2*r)/mp.besseli(0,2*r)-1,mp.mpf('.8'))
bv=4*r*r-1
d=mp.besseli(0,2*r)/(mp.e*r)
const={p:(mp.exp(r)+(-1)**p*mp.exp(-r))/mp.sqrt(bv) for p in [0,1]}
cv={p:[mp.mpf(str(q.subs({b:s.Float(str(bv),85),v:s.Float(str(r*(mp.tanh(r) if p==0 else mp.coth(r))),85)}).evalf(80))) for q in cs] for p in [0,1]}
# q[d][k]=(k!)^2 [t^k] I_0(2 sqrt(t))^d. Binomial convolution is integral.
N=161;K=N//2
choose=[[math.comb(i,j)**2 for j in range(i+1)] for i in range(K+1)]
q=[1]+[0]*K
rows=[q]
vals=[1]
marked={}
for dim in range(1,N+1):
 q=[sum(choose[k][j]*q[k-j] for j in range(k+1)) for k in range(K+1)]
 rows.append(q)
 terms={dim-2*k:math.comb(dim,2*k)*math.comb(2*k,k)*q[k] for k in range(dim//2+1)}
 vals.append(sum(terms.values()))
 if dim in [20,21,40,41,80,81,160,161]:marked[dim]=terms
known=[1,1,5,19,217,1451,26041,249705,6116209,76432627,2373097921,36562658573,1374991573825,25188442156333,1112491608614933,23620069750701091,1198207214200181217,28930659427538020915,1657461085278025906081,44848606508761385855085]
need(vals[:len(known)]==known, "optional independent identity failed")
out={'r':mp.nstr(r,70),'b':mp.nstr(bv,70),'d':mp.nstr(d,70),'C':{str(p):mp.nstr(const[p],70) for p in const},'c_symbolic':[str(q) for q in cs],'c_numeric':{str(p):[mp.nstr(q,45) for q in cv[p]] for p in cv},'cumulants':[str(k[j]) for j in range(1,2*R+3)],'checks':[],'oeis_terms_checked':len(known),'used_fraction':mp.nstr(1-1/mp.besseli(0,2*r),40),'used_variance':mp.nstr((1-1/mp.besseli(0,2*r))/mp.besseli(0,2*r)-1/(mp.besseli(0,2*r)**2*bv),40)}
for n,terms in marked.items():
 p=n%2; base=const[p]*(d*n)**n
 ratio=mp.mpf(vals[n])/base
 errors=[ratio-sum(cv[p][j]/mp.mpf(n)**j for j in range(L+1)) for L in range(R+1)]
 # Exact finite PGF versus limiting parity-conditioned Poisson, at u=0.7 and1.3
 pgf=[]
 for u in [mp.mpf('.7'),mp.mpf('1.3')]:
  actual=sum(mp.mpf(ct)*u**j for j,ct in terms.items())/vals[n]
  limit=(mp.exp(r*u)+(-1)**p*mp.exp(-r*u))/(mp.exp(r)+(-1)**p*mp.exp(-r))
  pgf.append({'u':str(u),'n_scaled_error':mp.nstr(n*(actual-limit),25)})
 def count_dim(D): return sum(math.comb(n,2*k)*math.comb(2*k,k)*rows[D][k] for k in range(n//2+1))
 empty1=mp.mpf(n)*count_dim(n-1)/vals[n]
 empty2=mp.mpf(n*(n-1))*count_dim(n-2)/vals[n]
 used_mean=n-empty1
 used_var=empty2+empty1-empty1**2
 vp=r*(mp.tanh(r) if p==0 else mp.coth(r))
 tv=mp.mpf(0);tv1=mp.mpf(0)
 for jj in range(p,n+101,2):
  lim=2*r**jj/(mp.factorial(jj)*(mp.exp(r)+(-1)**p*mp.exp(-r)))
  act=mp.mpf(terms.get(jj,0))/vals[n]
  q1=-(jj*jj-r*r-vp)/(2*bv)+(jj-vp)/(bv*bv)
  tv+=abs(act-lim)/2
  tv1+=abs(act-lim*(1+q1/n))/2
 q0=1/mp.besseli(0,2*r)
 offset=-(q0/bv)*(vp+(bv-1)/2-1/bv)
 out['checks'].append({'n_TV':mp.nstr(n*tv,25),'n2_TV_first':mp.nstr(n*n*tv1,25),'occupation_mean_offset':mp.nstr(offset,25),'occupation_mean_scaled_remainder':mp.nstr(n*(used_mean-n*(1-q0)-offset),25),'used_mean_over_n':mp.nstr(used_mean/n,25),'used_variance_over_n':mp.nstr(used_var/n,25),'n':n,'ratio':mp.nstr(ratio,30),'n_scaled_errors':[mp.nstr(errors[L]*n**(L+1),30) for L in range(R+1)],'pgf':pgf})
finish(out, ROOT.parent/'data/walk_checks.json')
