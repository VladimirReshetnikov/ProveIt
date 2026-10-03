"""Fresh frozen residual, exact finite-support algebra, and numerical sanity checks."""
import sympy as S
import numpy as np
from scipy.linalg import eigh_tridiagonal
from scipy.special import airy, ai_zeros, gammaln
from fractions import Fraction
from math import factorial
from pathlib import Path
import json
x,a,e=S.symbols('x a e')
def diff(u):return (S.expand(S.diff(u[0],x)+2*(x+a)*u[1]),S.expand(u[0]+S.diff(u[1],x)))
profile={0:(S.Integer(1),S.Integer(0)),2:(2*(-a+2*x)/15,x*(2*a+x)/15),3:(S.Rational(1,3),-x/3)}
def shift(sign):
 out=[S.Integer(0),S.Integer(0)]
 for k,v in profile.items():
  d=v
  for n in range(6-k):
   for t in range(2):out[t]+=e**(n+k)*sign**n*d[t]/S.factorial(n)
   d=diff(d)
 return out
bm=S.series(S.sqrt((1-x*e**2+3*e**3)/(1+x*e**2-e**3)),e,0,6).removeO()
bp=S.series(S.sqrt((1-x*e**2+2*e**3)/(1+x*e**2)),e,0,6).removeO()
la=2+2*a*e**2+3*e**3+13*a*a*e**4/15+5*a*e**5/3
pminus,pplus=shift(-1),shift(1)
for t in range(2):
 r=S.expand(bm*pminus[t]+bp*pplus[t]-la*sum(e**k*v[t] for k,v in profile.items()))
 assert all(S.expand(r.coeff(e,k))==0 for k in range(6))
assert all(S.expand(v[1].subs(x,0))==0 for v in profile.values())
# D^2 and Q^2 identities use exact rational arithmetic, including endpoints.
def d2(N,j):return Fraction(factorial(N+1)*factorial(N),factorial(N-j+1)*factorial(N+j))
for N in range(1,41):
 for j in range(1,N+2):assert d2(N,j)/d2(N,j-1)==Fraction(N-j+2,N+j)
 for j in range(N+1):assert d2(N-1,j)/d2(N,j)==1-Fraction(j*(j-1),N*(N+1))
# Numerical checks are diagnostics only; they are not proof of any bounds.
z=ai_zeros(2)[0];av=z[0]/2**(1/3);data=[]
for N in [80,160,320,640,1280,2560]:
 eps=N**(-1/3);j=np.arange(N+2);xx=(j+1)*eps
 edges=np.sqrt((N-np.arange(1,N+2)+2)/(N+np.arange(1,N+2)))
 vals,vec=eigh_tridiagonal(np.zeros(N+2),edges,select='i',select_range=(N,N+1))
 lam2,lam=vals;psi=vec[:,1];psi*=np.sign(psi[0])
 F,Ap,_,_=airy(z[0]+2**(1/3)*xx);Fp=2**(1/3)*Ap
 q=F+eps**2*(2*(-av+2*xx)*F/15+xx*(2*av+xx)*Fp/15)+eps**3*(F-xx*Fp)/3
 q/=np.linalg.norm(q)
 lhat=2+2*av*eps**2+3*eps**3+13*av**2*eps**4/15+5*av*eps**5/3
 Sq=np.zeros_like(q);Sq[:-1]+=edges*q[1:];Sq[1:]+=edges*q[:-1]
 Q=np.sqrt(np.maximum(0,1-j*(j-1)/(N*(N+1))))
 paritymass=[float(np.sum(psi[k::2]**2)) for k in (0,1)]
 assert max(abs(v-0.5) for v in paritymass)<1e-11
 data.append({'N':N,'ground_scaled':(2-lam)/eps**2,'gap_scaled':(lam-lam2)/eps**2,
 'quasimode_residual_over_eps6':float(np.linalg.norm(Sq-lhat*q)/eps**6),
 'eigenvector_error_over_eps4':float(np.linalg.norm(psi-q)/eps**4),
 'endpoint_ratio':float(psi[0]/(2**0.5*N**-0.5)),
 'Q_defect_over_N43':float(np.linalg.norm((1-Q)*psi)*N**(4/3))})
result={'frozen_residual_eps0_through_eps5':'exactly zero','boundary':'exactly zero',
'exact_gauge_identities':'all N=1..40 and all legal j verified',
'limiting_ground':float(-2**(2/3)*z[0]),'limiting_gap':float(2**(2/3)*(z[0]-z[1])),
'diagnostics':data}
Path(__file__).with_suffix('.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
# Independent exact comparison of both recurrences and the named sequence prefix.
r={(0,0):1}
for n in range(1,21):
 r[n,0]=1
 for m in range(1,n+1):r[n,m]=r[n,m-1]+(m+1)*r.get((n-1,m),0)
d={0:Fraction(1)}
for N in range(1,41):
 d={j:Fraction(N-j+2,N+j)*d.get(j-1,0)+d.get(j+1,0) for j in range(N%2,N+1,2)}
 for j,v in d.items():
  n=(N+j)//2;m=(N-j)//2
  if n<=20:assert v==Fraction(r[n,m],factorial(n))
assert [r[n,n] for n in range(10)]==[1,1,3,16,127,1363,18628,311250,6173791,142190703]
result['exact_original_recurrence']='all legal coordinates with N<=40, n<=20, and A082161 prefix n=0..9 verified'
Path(__file__).with_suffix('.json').write_text(json.dumps(result,indent=2)+'\n')
print(result['exact_original_recurrence'])
