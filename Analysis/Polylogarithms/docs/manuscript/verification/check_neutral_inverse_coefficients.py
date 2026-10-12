"""Exact finite checks of the new neutral inverse coefficient identity.

The general convergence and asymptotic conclusions have analytic proofs.
This program checks a universal fifth-degree jet, independently composing
the resulting inverse, with controls that deliberately corrupt the formula.
"""
from pathlib import Path
import json
import sympy as s

t,z=s.symbols('t z')
a=s.symbols('a1:6',nonzero=True)
H=sum(a[j]*t**j for j in range(5))
v=s.expand(H/a[0]-1)
coeff=[]
for k in range(1,6):
    truncated=sum(s.binomial(-k,j)*v**j for j in range(k))
    coeff.append(s.expand(truncated).coeff(t,k-1)/(k*a[0]**k))
inverse=sum(coeff[k-1]*z**k for k in range(1,6))
# Work modulo z^6 throughout the independent direct composition.
power=s.Poly(1,z);res=s.Poly(0,z)
for j in range(1,6):
    product=power*s.Poly(inverse,z)
    power=s.Poly.from_dict({m:c for m,c in product.terms() if m[0]<=5},z)
    res+=a[j-1]*power
identities=[s.cancel(res.nth(k)-(1 if k==1 else 0))==0 for k in range(1,6)]
assert all(identities)
assert s.cancel(coeff[0]-1/a[0])==0
assert s.cancel(coeff[1]+a[1]/a[0]**3)==0
x=s.symbols('x',real=True)
sigma=1+s.exp(-x);model=sigma*x*x
full=s.diff(model,x);fixed=2*sigma*x
controls={
    'reversed_first_displacement_rejected':s.cancel(-a[0]*coeff[0]-1)!=0,
    'omitted_quadratic_curvature_rejected':s.cancel(a[1]*coeff[0]**2)!=0,
    'wrong_quadratic_sign_rejected':s.cancel(-a[0]*coeff[1]+a[1]*coeff[0]**2)!=0,
    'frozen_order_chain_rule_rejected':s.simplify(full-fixed)!=0,
}
assert all(controls.values())
record=dict(passed=True,scope='Finite exact polynomial identities; not a convergence proof',
            maximum_degree=5,composition_coefficients_checked=len(identities),
            coefficients=[str(s.factor(c)) for c in coeff],
            convention='P(w+t)-P(w)=a1*t+a2*t^2+...; a2=P_second(w)/2',
            moving_order_toy_derivative=str(full),corruption_controls=controls)
Path(__file__).with_name('neutral-inverse-coefficients.json').write_text(json.dumps(record,indent=2)+'\n',encoding='utf-8')
print(json.dumps(record,indent=2))
