"""Exact symbolic checks for every critical coefficient used in the proof."""
import json
from pathlib import Path
import sympy as sp
ROOT = Path(__file__).resolve().parents[1]
z, u, B, delta = sp.symbols('z u B delta')
y = 1 - delta
F = z + (y*y+B)/2 + z*u/2*(y*y/(1-y)**2 + B/(1-B))
D = 1-2*z-B-z*u*B/(1-B)
P = delta**4-D*delta**2+z*u*(1-delta)**2
assert sp.factor(2*delta**2*(F-y)-P) == 0
R, A, t = sp.symbols('R A t', positive=True)
verified = []
for sign in (1, -1):
    critical_delta = sign*R**sp.Rational(1,4)*t-sp.sqrt(R)*t*t/4
    critical_rho = R-sp.sqrt(R)/A*t*t+sign*R**sp.Rational(3,4)/A*t**3
    char = sp.series(critical_delta**4-critical_rho*t**4*(1-critical_delta), t, 0, 6).removeO()
    # D=-2A(rho-R)+O(t^4), sufficient through total degree five.
    quartic = sp.series(critical_delta**4+2*A*(critical_rho-R)*critical_delta**2+critical_rho*t**4*(1-critical_delta)**2, t, 0, 6).removeO()
    assert sp.simplify(char) == 0
    assert sp.simplify(quartic) == 0
    verified.append('positive' if sign == 1 else 'negative')
a=sp.sqrt(R)/A; b=R**sp.Rational(3,4)/A
c=a/R; d=b/R; gamma=sp.sqrt(2*R*A)
assert sp.simplify(d*(2/c)**sp.Rational(3,2)-2*gamma) == 0
pressure = sp.series(-sp.log(R-a*t*t+b*t**3),t,0,4).removeO()
assert sp.simplify(pressure-(-sp.log(R)+c*t*t-d*t**3)) == 0
out = {'exact_quartic': True, 'critical_branches_through_t5': verified,
       'pressure_through_t3': True, 'penalty_constant_identity': True,
       'no_second_crossover_term_claimed': True}
(ROOT / 'results/algebra-checks.json').write_text(json.dumps(out, indent=2)+'\n')
print(json.dumps(out, indent=2))
