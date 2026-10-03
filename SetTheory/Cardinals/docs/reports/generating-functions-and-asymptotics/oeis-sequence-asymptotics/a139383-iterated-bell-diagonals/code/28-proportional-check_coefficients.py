"""Independent exact low-order checks; not a substitute for the analytic audit."""
import json
from pathlib import Path
import sympy as s
z,y,b,d=s.symbols('z y beta delta')
base=json.loads(Path('/workspace/shared/oeis-iterated-bell-report/results/coefficients.json').read_text())
v=[s.sympify(q,locals={'y':y}) for q in base['reciprocal_iterate']]
tr=lambda q,k:s.series(q,z,0,k).removeO().expand()
inside=1+b*y*z+sum(v[j-1]*b**(j+1)*z**(j+1) for j in range(1,3))
lognorm=tr(s.log(inside)/z-b*y+z/12,3)
R=tr(s.exp(lognorm),3)
r1=s.Rational(1,12)+b*b*(-y*y/2-y/3-s.Rational(1,18))
assert s.expand(R.coeff(z,1)-r1)==0
for j in range(3):
    assert s.Poly(R.coeff(z,j),y).degree()<=2*j
    assert s.expand(R.coeff(z,j).subs(b,1)-s.sympify(base['forward_integrand'][j],locals={'y':y}))==0
# Formal Abel-time translation to second order, q=1/z.
shifted=1/z+d+y-s.log(1+d*z)/3
for j in range(1,3):
    shifted+=v[j-1].subs(y,y-s.log(1+d*z)/3)*(z/(1+d*z))**j
translated=1/z+y+d+sum(v[j-1].subs(y,y+d)*z**j for j in range(1,3))
assert tr(shifted-translated,3)==0
out={'R1':str(s.factor(R.coeff(z,1))),'R2':str(s.expand(R.coeff(z,2))),'checks':'First correction, degrees through order 2, beta=1 agreement through order 2, Abel bounded-shift translation through order 2 all passed.'}
Path('/workspace/shared/iterated-bell-proportional-audit/coefficient-checks.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
