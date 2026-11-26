#!/usr/bin/env python3
"""Exact symbolic checks for the analytic/covolume transfer note.

These validate the displayed identities and counterexample, not the analytic
Landau theorem or any unproved arithmetic estimate.  Requires SymPy.
"""
import json
from pathlib import Path
import sympy as sp

x = sp.symbols('x', positive=True)
a, tau = sp.symbols('a tau', positive=True)
s = sp.symbols('s')
k = sp.symbols('k', integer=True, nonnegative=True)
primitive = x**a * sp.sin(tau * sp.log(x))
remainder = x**(a-1) * (a*sp.sin(tau*sp.log(x)) + tau*sp.cos(tau*sp.log(x)))
assert sp.simplify(sp.diff(primitive, x) - remainder) == 0

# Integrating the sine and cosine terms after x=exp(v) gives these
# standard elementary Laplace integrals. The rational identity is exact.
mellin_from_terms = (a*tau + tau*(s-a)) / ((s-a)**2 + tau**2)
mellin = tau*s / ((s-a)**2 + tau**2)
assert sp.simplify(mellin_from_terms - mellin) == 0
residue_plus = sp.simplify(sp.limit((s-a-sp.I*tau)*mellin, s, a+sp.I*tau))
residue_minus = sp.simplify(sp.limit((s-a+sp.I*tau)*mellin, s, a-sp.I*tau))
assert sp.simplify(residue_plus - (a+sp.I*tau)/(2*sp.I)) == 0
assert sp.simplify(residue_minus + (a-sp.I*tau)/(2*sp.I)) == 0

# A dyadic endpoint has phase 2*pi*k exactly.
phase_endpoint = sp.sin(2*sp.pi*k)
assert phase_endpoint == 0
assert sp.sin(2*sp.pi*(k+1)) == 0

# Algebra used BEFORE taking positive parts in the rank-sensitive bound.
alpha, H, L, U, I, M, R = sp.symbols('alpha H L U I M R', real=True)
raw_difference = alpha*(H-M*R+U) + 2*I - (H-L)
rearranged_difference = L+alpha*U+2*I-(1-alpha)*H-alpha*M*R
assert sp.expand(raw_difference-rearranged_difference) == 0
assert sp.simplify((L+alpha*U+2*I)/(alpha*M) - (U+(L+2*I)/alpha)/M) == 0

# Moving-window Mellin identity on the monomial R(t)=t^(b-1).
# Here y=h^b, z=h^s. This algebraic check handles the finite correction.
b, y, z = sp.symbols('b y z')
moving_from_formula = (z-1)/(s*(s-b)) - ((y-z)/(b-s)-(y-1)/b)/s
moving_direct = (y-1)/(b*(s-b))
assert sp.factor(moving_from_formula-moving_direct) == 0

aa = sp.Rational(3,4)
tt = 2*sp.pi/sp.log(2)
u1 = (sp.pi-sp.atan(tt/aa))/tt
positive_bin_constant = tt/sp.sqrt(aa**2+tt**2) * sp.exp(aa*u1)*(1+sp.exp(aa*sp.log(2)/2))
result = {
    'all_symbolic_checks_passed': True,
    'checks': [
        'remainder is the derivative of the displayed primitive',
        'Mellin rational function matches sine/cosine transform',
        'two nonzero residues have the stated values',
        'dyadic endpoint sine values vanish exactly',
        'rank-sensitive rearrangement is an exact identity',
        'coarse rank-loss expression is an exact identity',
        'moving-window transform with finite correction matches monomials'
    ],
    'counterexample_a': '3/4',
    'counterexample_tau': '2*pi/log(2)',
    'positive_part_dyadic_bin_constant_approx': str(sp.N(positive_bin_constant, 30)),
    'scope': 'Symbolic identities only; no new L-function zero-free estimate is certified.'
}
out = Path(__file__).resolve().parents[1]/'checks'/'mean_transfer_checks.json'
out.write_text(json.dumps(result, indent=2) + '\n')
print(json.dumps(result, indent=2))
