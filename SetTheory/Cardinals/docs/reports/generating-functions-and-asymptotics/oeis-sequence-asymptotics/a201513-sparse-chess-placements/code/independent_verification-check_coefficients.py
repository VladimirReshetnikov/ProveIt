from fractions import Fraction as F
import json, sympy as s
from sympy.functions.combinatorial.numbers import stirling
from pathlib import Path
here=Path(__file__).resolve().parent
root=here.parent
rows=json.loads((root/'cluster_coefficients.json').read_text())
checks=[]
for line in (here/'row_dp_counts.txt').read_text().splitlines():
 p,n,*cs=line.split();n=int(n);cs=list(map(int,cs));J=len(cs)-1
 log=[F(0)]*(J+1)
 for j in range(1,J+1):log[j]=F(j*cs[j]-sum(k*log[k]*cs[j-k] for k in range(1,j)),j)
 for j in range(1,min(J,6)+1):
  if n>=(1 if p=='king' else 2)*(j-1)+1:
   abc=list(map(F,rows[p]['b_j_coefficients_n2_n_1'][j]));target=abc[0]*n*n+abc[1]*n+abc[2]
   assert log[j]==target,(p,n,j,log[j],target)
   checks.append([p,n,j,str(log[j])])
print('Direct row-DP vs cluster polynomials:',len(checks),'exact checks passed')
x,t,m=s.symbols('x t m');M=4
# P_k(m) by finite exact product, then polynomial interpolation, rather than log/Faulhaber.
Pk=[]
for k in range(M+1):
 vals=[]
 for mm in range(2*k+1):
  prod=s.prod(1-i*x for i in range(mm));vals.append((mm,s.expand(prod).coeff(x,k)))
 Pk.append(s.interpolate(vals,m).expand())
out={}
for p in ('king','knight'):
 abc=[[s.Rational(v) for v in r] for r in rows[p]['b_j_coefficients_n2_n_1']]
 a=abc[2][0]
 h=sum(abc[j][r]*t**j*x**(j-2+r) for j in range(2,M+3) for r in range(3) if 0<j-2+r<=M)
 H=s.series(s.exp(h),x,0,M+1).removeO().expand()
 def expectation(poly):
  poly=s.Poly(poly,m)
  return sum(c*sum(stirling(e[0],k,kind=2)*a**k for k in range(e[0]+1)) for e,c in poly.terms())
 cs=[]
 for r in range(M+1):
  acc=0
  for k in range(r+1):
   for (d,),v in s.Poly(H.coeff(x,r-k),t).terms():
    acc+=v*expectation(Pk[k].subs(m,d+2*m))
  cs.append(s.factor(acc))
 known=json.loads((root/'asymptotic_coefficients.json').read_text())[p]
 assert [str(v) for v in cs]==known
 out[p]=list(map(str,cs))
 print(p,'independent Touchard/interpolated falling-factorial result',out[p])
(here/'check_results.json').write_text(json.dumps({'direct_checks':checks,'independent_asymptotic_coefficients':out},indent=2)+'\n')
