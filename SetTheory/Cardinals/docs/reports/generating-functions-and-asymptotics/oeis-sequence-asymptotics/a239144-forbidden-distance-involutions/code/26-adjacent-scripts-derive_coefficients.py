"""Exact rational Gaussian/Touchard extraction, no guessed recurrence."""
import sympy as S
import json
from pathlib import Path

def build(M=8):
 u,k,w,t,j=S.symbols('u k w t j'); R=S.Rational
 moments=[S.Integer(1),R(1,2)]
 for v in range(2,3*M+1):moments.append(S.expand(moments[-1]/2+R(v-1,2)*moments[-2]))
 def gaussian(poly):return S.expand(sum(c*moments[p[0]] for p,c in S.Poly(poly,u).terms()))
 q=[0]+[(-1)**(h+3)*u**(h+2)/S.Integer(h+2) for h in range(1,M+1)]
 f=[S.Integer(1)]
 for h in range(1,M+1):f.append(S.expand(sum(a*q[a]*f[h-a] for a in range(1,h+1))/S.Integer(h)))
 A=[gaussian(v) for v in f];lam=[0]
 for h in range(1,M+1):lam.append(S.expand(A[h]-sum(a*lam[a]*A[h-a] for a in range(1,h))/S.Integer(h)))
 H=0
 for r in range(1,M//2+1):H-=t**(2*r)*S.summation((k+j)**r,(j,0,k-1))/r
 v=1-2*k*t*t
 H+=S.series((v*S.log(v)+2*k*t*t)/(2*t*t)+(S.sqrt(v)-1)/t,t,0,M+1).removeO()
 for h in range(1,M+1):H+=S.series(lam[h]*t**h*(v**(-R(h,2))-1),t,0,M+1).removeO()
 H=S.Poly(S.expand(H),t)
 hs=[0]+[S.expand(H.coeff_monomial(t**a)) for a in range(1,M+1)]
 C=[S.Integer(1)]
 for h in range(1,M+1):C.append(S.expand(sum(a*hs[a]*C[h-a] for a in range(1,h+1))/S.Integer(h)))
 P=[S.expand(sum(co*S.bell(pow[0],w) for pow,co in S.Poly(v,k).terms())) for v in C]
 avoid=[v.subs(w,-1) for v in P]
 D=[S.expand(sum(A[a]*avoid[h-a] for a in range(h+1))) for h in range(M+1)]
 # Independent positive-sector extraction from the exact Chebyshev-Gaussian integral.
 extra=S.series(t/(1+t*u)-t*t/(2*(1+t*u)**2),t,0,M+1).removeO()
 qs=[0]+[S.expand(q[h]+extra.coeff(t,h)) for h in range(1,M+1)]
 fs=[S.Integer(1)]
 for h in range(1,M+1):fs.append(S.expand(sum(a*qs[a]*fs[h-a] for a in range(1,h+1))/S.Integer(h)))
 sector=[gaussian(v) for v in fs]
 assert sector==D, (sector,D)
 V=[0]+[S.expand(2*P[h].subs(w,-1)+S.diff(P[h],w).subs(w,-1)) for h in range(1,M+1)]
 beta=[0]
 for h in range(1,M+1):beta.append(S.expand(D[h]-sum(a*beta[a]*D[h-a] for a in range(1,h))/S.Integer(h)))
 return {name:[str(v) for v in vals] for name,vals in [('involution',A),('lambda',lam),('moment_polynomials',C),('pgf_polynomials',P),('avoidance_ratio',avoid),('avoidance_absolute',D),('avoidance_log',beta),('total_variation',V),('positive_sector',sector)]}
if __name__=='__main__':
 import argparse
 p=argparse.ArgumentParser();p.add_argument('--order',type=int,default=8);args=p.parse_args()
 d=build(args.order);Path('involution-coefficients.json').write_text(json.dumps(d,indent=2)+'\n')
 for key,vals in d.items():print(key,':',', '.join(vals))
