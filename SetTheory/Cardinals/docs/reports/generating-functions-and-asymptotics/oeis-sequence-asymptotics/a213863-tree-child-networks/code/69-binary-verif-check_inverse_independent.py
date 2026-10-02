"""Expand the actual logarithmic model, independently of proposed residual list."""
from pathlib import Path
import sympy as s
import json
t,A,L,D,E,p,q,S,d=s.symbols('t A L D E p q S d')
u=-A/S;v=-q/S
w=-L/S+A**2/(3*S**2)-d*A**2/(2*S**3)
r=-D/S+A*(p+q/3)/S**2-d*A*q/S**3
f=-E/S+p*q/S**2-d*(A*L+q**2/2)/S**3+d*A**3/(3*S**4)-d**2*A**3/(2*S**5)
delta=u/t+v+w*t+r*t**2+f*t**3
z=s.expand(delta*t**3)
cut=lambda a,k:s.series(a,t,0,k+1).removeO().expand()
# d[(x+delta)log(k(x+delta)/e)-xlog(kx/e)], with S=d log(kx).
base=S*delta+d*(cut((1+z)*s.log(1+z)-z,6))/t**3
model=base+A/t*cut((1+z)**s.Rational(1,3),4)+q+p*cut(s.log(1+z),3)+L*t*cut((1+z)**(-s.Rational(1,3)),2)+D*t**2*cut((1+z)**(-s.Rational(2,3)),1)+E*t**3
checks={str(k):str(s.simplify(s.expand(model).coeff(t,k))) for k in range(-1,4)}
assert all(v=='0' for v in checks.values())
report={'actual_model_residual_coefficients_t_minus1_through3':checks,'parameters':'A,L,D,E,p,q,S,d'}
Path(__file__).with_name('independent-inverse-checks.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(report,indent=2))
