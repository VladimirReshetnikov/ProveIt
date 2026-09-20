#!/usr/bin/env python3
"""Optional SymPy checks of derivatives, partial fractions, and volume formulas.

The main verifier needs only Python's standard library. This independent
symbolic companion additionally checks the integrations for the two-bound
volume theorem. Tested with SymPy 1.14.0; no floating-point arithmetic is used.
"""
from __future__ import annotations

import json
import time
from pathlib import Path

try:
    import sympy as s
except ImportError as exc:
    raise SystemExit('Optional dependency missing. Install SymPy to run this companion.') from exc

from verify import P, Q


def zero(expression: s.Expr, label: str) -> None:
    if s.cancel(expression) != 0:
        raise AssertionError(label)
    print('PASS:', label, flush=True)


def main() -> None:
    started = time.perf_counter()
    u, v, z = s.symbols('u v z')
    G = (1 + 5*u + 5*v + u*v)/((1-u)*(1-v))
    D = lambda f: u*s.diff(f, u) + v*s.diff(f, v)
    G1 = 6*(u+v)*(1-u*v)/((1-u)**2*(1-v)**2)
    G2 = 6*(u+v)*(1+u+v-6*u*v+u**2*v+u*v**2+u**2*v**2)/((1-u)**3*(1-v)**3)
    zero(D(G)-G1, 'First Euler derivative of the chamber generating function')
    zero(D(G1)-G2, 'Second Euler derivative of the chamber generating function')
    poly = lambda cs: sum(c*z**i for i, c in enumerate(cs))
    F = poly(P)/poly(Q)
    built = ((1+11*z+11*z*z+z**3)/(1-z)**5*G +
             2*(1+4*z+z*z)/(1-z)**4*G1 + (1+z)/(1-z)**3*G2)
    zero(built.subs({u:z**2, v:z**3})-F, 'Independent rational-function simplification')

    a, b, p, q = s.symbols('a b p q')
    integrand = 12*(a-p-2*q)**2*(b-2*p-3*q)**2
    small = s.integrate(s.integrate(integrand, (p, 0, (b-3*q)/2)), (q, 0, b/3))
    large = s.integrate(s.integrate(integrand, (p, 0, a-2*q)), (q, 0, a/2))
    middle = (s.integrate(s.integrate(integrand, (p, 0, (b-3*q)/2)), (q, 0, 2*a-b)) +
              s.integrate(s.integrate(integrand, (p, 0, a-2*q)), (q, 2*a-b, a/2)))
    small_formula = b**4*(540*a*a-252*a*b+37*b*b)/3240
    large_formula = a**4*(37*a*a-84*a*b+60*b*b)/120
    middle_formula = -(27*a**6-108*a**5*b+180*a**4*b*b-160*a**3*b**3+
                       60*a*a*b**4-12*a*b**5+b**6)/120
    zero(small-small_formula, 'Volume integral in b <= 3a/2')
    zero(middle-middle_formula, 'Volume integral in 3a/2 <= b <= 2a')
    zero(large-large_formula, 'Volume integral in b >= 2a')
    zero(middle_formula-small_formula+(2*b-3*a)**6/3240,
         'First wall correction for the truncated-power volume formula')
    zero(large_formula-middle_formula-(b-2*a)**6/120,
         'Second wall correction for the truncated-power volume formula')
    zero(small_formula.subs(b, a)-s.Rational(65,648)*a**6,
         'Equal-bound leading coefficient')
    report = {'status': 'all symbolic checks passed', 'sympy_version': s.__version__,
              'elapsed_seconds': round(time.perf_counter()-started, 3),
              'checks': 9, 'arithmetic': 'exact rational functions and polynomial integration'}
    destination = Path(__file__).parent/'data'/'symbolic_verification.json'
    destination.parent.mkdir(exist_ok=True)
    destination.write_text(json.dumps(report, indent=2)+'\n')
    print(json.dumps(report, indent=2))


if __name__ == '__main__':
    main()
