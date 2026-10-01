"""Exact algebraic checks accompanying the written proofs."""
from pathlib import Path
import json
import sympy as s

v, r, p, a, u = s.symbols('v r p a u')
G = (1-v)*(4+8*v+3*v*v-v*v*r)/(4*(1+2*v)*(1+v)**2)
ell = v*(12+(25+r)*v+(11-r)*v*v)/(4*(1+2*v)*(1+v)**2)
assert s.cancel(1-G-ell) == 0
rem = v*v*((r-23)-(49+r)*v-24*v*v)/(4*(1+2*v)*(1+v)**2)
assert s.cancel(ell-3*v-rem) == 0
primitive = -2*s.atanh(s.sqrt(1-u))+4*s.sqrt(1-u)-s.log(u)
integrand = (1-2*u)/(u*s.sqrt(1-u))-1/u
assert s.simplify(s.diff(primitive, u)-integrand) == 0
Psi = a*(1-2*u)/s.sqrt(u*(1-u))
rho = a/(2*(u*(1-u))**s.Rational(3,2))
assert s.simplify(s.diff(Psi,u)+rho) == 0
series = s.series(1-G.subs(r, s.sqrt((1+v)/2)), v, 0, 4)
assert s.expand(series.removeO()).coeff(v,1) == 3
result = {'status': 'PASS', 'identities_checked': 5,
          'one_minus_G_expansion': str(series),
          'scope': 'Exact rational/algebraic identities; not an asymptotic proof assistant.'}
path = Path(__file__).resolve().parent.parent/'data'/'symbolic_checks.json'
path.write_text(json.dumps(result, indent=2)+'\n')
print(json.dumps(result, indent=2))
