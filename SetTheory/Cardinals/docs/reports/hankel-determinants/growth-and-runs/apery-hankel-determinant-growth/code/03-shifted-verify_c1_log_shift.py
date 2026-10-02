#!/usr/bin/env python3
"""Exact check of the first correction against a Selberg exponent shift.

For f(t)=gamma log(t), multiplication by exp(f) replaces r by r+gamma.
The independently expanded gamma product must match the correction formula.
This finite symbolic identity does not replace the analytic remainder proof.
"""

import json
import sympy as S


def verify():
    s, a = S.symbols("s a", positive=True)
    gamma = S.symbols("gamma", real=True)
    q = (1-S.sqrt(a)) / (1+S.sqrt(a))
    U = 2*gamma*S.log((1+S.sqrt(a))/2)
    energy = -gamma**2*S.log(1-q*q)
    D = 2*a**S.Rational(3, 2)*(1-a)*S.diff(U, a)/s
    functional = (D*S.diff(energy, a)/6 + D*S.diff(U, a)/8
                  + D/24*(1/(1-a) + S.Rational(3, 2)/a)
                  + a**S.Rational(3, 2)/(12*s)
                  * ((1-a)*S.diff(U, a, 2) - S.diff(U, a)))
    functional = S.simplify(functional.subs(a, (s/(s+2))**2))
    leading = ((s+1)**2*S.log(s+1) - s*s*S.log(s)/2
               - (s+2)**2*S.log(s+2)/2)
    linear = S.log(2*S.pi) + ((s+1)*S.log(s+1)-(s+2)*S.log(s+2))/2
    constant = S.log(s)/12 - (S.log(s+1)+S.log(s+2))/24
    shifted = (gamma**3*S.diff(leading, s, 3)/6
               + gamma**2*S.diff(linear, s, 2)/2
               + gamma*S.diff(constant, s))
    assert S.simplify(functional-shifted) == 0
    explicit = gamma*(-8*gamma**2 + 6*gamma*s + 3*s + 4)/(24*s*(s+1)*(s+2))
    assert S.simplify(functional-explicit) == 0
    return {"status": "PASS: exact Selberg logarithmic-shift identity",
            "scope": "s > 0, real gamma; finite symbolic check",
            "c_rel": str(S.factor(functional))}


if __name__ == "__main__":
    print(json.dumps(verify(), indent=2))
