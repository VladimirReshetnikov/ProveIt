import json
from pathlib import Path
import sympy as s
x=s.symbols('x',positive=True)
G=s.EulerGamma
# Finite Euler--Maclaurin functional for rational poles at -1.
def functional_a1(r):
 z=s.symbols('z');ell=s.log(1+z)
 for j in range(r): ell=s.diff(ell,z)*z
 h=s.apart((-x)**r*ell.subs(z,x),x)
 result=0
 for term in s.Add.make_args(h):
  if not s.denom(term).has(x):
   p=s.Poly(term,x)
   result+=sum(c*s.zeta(-mon[0]) for mon,c in p.terms())
  else:
   den=s.denom(term);j=s.degree(den,x)
   c=s.cancel(term*(x+1)**j)
   if c.has(x): raise ValueError('Unexpected rational pole')
   value=-s.digamma(2) if j==1 else s.zeta(j)-1-s.Rational(1,j-1)
   result+=c*value
 return s.simplify(result/s.factorial(r))
C=[functional_a1(r) for r in range(1,7)]
if s.simplify(C[0]-(s.Rational(7,12)-G))!=0:raise ValueError('c1 mismatch')
if s.simplify(C[1]-(-s.Rational(1,24)+3*G/2-s.pi**2/12))!=0:raise ValueError('c2 mismatch')
# Independent Gaussian-moment construction of the weighted Edgeworth polynomial.
e,u=s.symbols('e u');k=s.symbols('k3:9');v=s.symbols('v',positive=True)
Q=sum(s.I**j*k[j-3]*u**j/s.factorial(j)/v**s.Rational(j,2)*e**(j-2) for j in range(3,9))
poly=s.series(s.exp(Q),e,0,7).removeO().expand()
def gaussian(term):
 p=s.Poly(term,u)
 return s.simplify(sum(c*(s.factorial2(n[0]-1) if n[0]%2==0 else 0) for n,c in p.terms()))
edge={w:gaussian(poly.coeff(e,w)) for w in range(7)}
if any(edge[w]!=0 for w in (1,3,5)):raise ValueError('Odd Gaussian term did not vanish')
expected1=k[1]/(8*v**2)-5*k[0]**2/(24*v**3)
expected2=-k[3]/(48*v**3)+7*k[0]*k[2]/(48*v**4)+35*k[1]**2/(384*v**4)-35*k[0]**2*k[1]/(64*v**5)+385*k[0]**4/(1152*v**6)
if s.simplify(edge[2]-expected1)!=0 or s.simplify(edge[4]-expected2)!=0:raise ValueError('Edgeworth mismatch')
data={'boundary_a1':{str(r):str(C[r-1]) for r in range(1,7)},'edgeworth':{str(w//2):str(edge[w]) for w in (0,2,4,6)},'checks_passed':True}
Path(__file__).with_suffix('.json').write_text(json.dumps(data,indent=2)+'\n')
print(json.dumps(data,indent=2))
