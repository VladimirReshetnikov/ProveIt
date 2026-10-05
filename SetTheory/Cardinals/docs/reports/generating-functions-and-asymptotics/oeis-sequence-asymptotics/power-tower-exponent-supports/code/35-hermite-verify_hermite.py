"""Exact fixed-defect Hermite checks and optional root orientation.

The finite symbolic checks supplement the proof. Requires SymPy.
"""
import sympy as s
from pathlib import Path
import json
z,N,k,x,h,m=s.symbols('z N k x h m')
RMAX=10
A=s.series(s.sqrt(1+z)*s.log(1+z)/z,z,0,RMAX+1).removeO()
B=s.series(2/(s.sqrt(1+z)+1),z,0,RMAX+1).removeO()
la=s.series(s.log(A),z,0,RMAX+1).removeO()
lc=s.series(s.log(B/A),z,0,RMAX+1).removeO()
c=[s.expand(m*la+k*lc).coeff(z,j) for j in range(RMAX+1)]
polys=[s.Integer(1)]
for r in range(1,RMAX+1):
 polys.append(s.expand(sum(j*c[j]*polys[r-j] for j in range(1,r+1))/r))
records=[]
for r in range(RMAX+1):
 R=s.expand(polys[r].subs(m,N-r))
 for (i,j),coef in s.Poly(R,N,k).terms():
  if 2*i+j>r:raise RuntimeError(('weight',r,i,j,coef))
 Q=s.expand((-1)**r*s.factorial(r)*s.sqrt(12)**r*h**r*R.subs({N:h**-2,k:2*x/(s.sqrt(3)*h)}))
 Q=s.Poly(Q,h)
 if s.expand(Q.nth(0)-s.hermite_prob(r,x))!=0:raise RuntimeError(('Hermite',r))
 G=s.Integer(0)
 if r>=2:G+=13*x/(4*s.sqrt(3))*r*(r-1)*s.hermite_prob(r-2,x)
 if r>=3:G-=s.sqrt(3)*r*(r-1)*(r-2)*s.hermite_prob(r-3,x)
 if s.simplify(Q.nth(1)-G)!=0:raise RuntimeError(('correction',r))
 if s.Poly(Q.as_expr(),x).LC()!=1:raise RuntimeError(('monic',r))
 if r%2 and s.simplify(R.subs(k,-2*(r-1)))!=0:raise RuntimeError(('central root',r))
 if r>=1:
  shift=s.diff(s.hermite_prob(r,x),x)*(x*x/(4*s.sqrt(3))+s.sqrt(3)*(r-1))
  if s.simplify(s.rem(s.expand(G-shift),s.hermite_prob(r,x),x))!=0:raise RuntimeError(('root shift',r))
 if r>=2:
  reduced=s.cancel(R/(k+2*(r-1))) if r%2 else R
  degree=r//2
  edge=sum(coef*N**i*k**j for (i,j),coef in s.Poly(reduced,N,k).terms() if 2*i+j==2*degree)
  alpha=s.Rational(1,2) if r%2 else -s.Rational(1,2)
  factor=(-1)**(degree+1)*s.factorial(degree)/(4*s.factorial(r)) if r%2 else (-1)**degree*s.factorial(degree)/s.factorial(r)
  expected=factor*(N/6)**degree*s.assoc_laguerre(degree,alpha,3*k*k/(8*N))
  if s.expand(edge-expected)!=0:raise RuntimeError(('Laguerre edge',r))
 records.append({'defect':r,'residual':str(s.factor(R)), 'first_correction':str(s.expand(G))})
 print(r,s.factor(R),flush=True)
Path(__file__).with_name('hermite_checks.json').write_text(json.dumps({'checked_defects':list(range(RMAX+1)), 'records':records,'scope':'finite exact polynomial checks; asymptotic theorem proved analytically'},indent=2)+'\n')
