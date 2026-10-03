"""Exact symbolic general-beta checks from audited orbit polynomials."""
import sympy as s,json
from pathlib import Path
root=Path(__file__).parent
base=json.loads((root/'orbit-coefficients.json').read_text())
z,y,beta=s.symbols('z y beta');M=base['order']
v=[s.sympify(t,locals={'y':y}) for t in base['reciprocal_iterate']]
inside=1+beta*y*z+sum(v[j-1]*beta**(j+1)*z**(j+1) for j in range(1,M+1))
E=s.series(s.log(inside)/z-beta*y,z,0,M+1).removeO()+sum(s.bernoulli(2*j)*z**(2*j-1)/(2*j*(2*j-1)) for j in range(1,(M+1)//2+1))
R=s.series(s.exp(E),z,0,M+1).removeO().expand()
polys=[s.expand(R.coeff(z,j)) for j in range(M+1)]
assert polys[0]==1
assert s.expand(polys[1]-(s.Rational(1,12)+beta**2*(-y*y/2-y/3-s.Rational(1,18))))==0
for j,r in enumerate(polys):
 assert s.Poly(r,y).degree()<=2*j
 assert s.expand(r.subs(beta,1)-s.sympify(base['forward_integrand'][j],locals={'y':y}))==0
result={'order':M,'forward_integrand_general_beta':[str(t) for t in polys],'checks':'degree bounds, explicit first correction, and beta=1 agreement all passed'}
(root/'proportional-coefficients.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
