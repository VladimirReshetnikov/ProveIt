#!/usr/bin/env python3
"""Exact symbolic checks for necessary hypotheses in one-sided zero criteria.

This checks rational identities and residues. It is not a GRH proof and does
not numerically test zeta zeros. Requires SymPy.
"""
import json
import sympy as sp

s = sp.symbols('s')
alpha = sp.Rational(3, 4)
tau = sp.Integer(2)
models = {
    'negative_real_mode': -1 / (s-alpha),
    'nonpositive_oscillation': (s-alpha) / ((s-alpha)**2 + tau**2) - 1/(s-alpha),
    'double_pole_zero_residue': -1 / (s-alpha)**2,
}
expected = {
    'negative_real_mode': [(alpha, -1)],
    'nonpositive_oscillation': [(alpha, -1), (alpha+sp.I*tau, sp.Rational(1,2)), (alpha-sp.I*tau, sp.Rational(1,2))],
    'double_pole_zero_residue': [(alpha, 0)],
}
result = {}
for name, expr in models.items():
    checks = []
    for pole, residue in expected[name]:
        actual = sp.residue(expr, s, pole)
        assert sp.simplify(actual-residue) == 0
        checks.append({'pole': str(pole), 'residue': str(actual)})
    result[name] = {'transform': str(expr), 'checks': checks}

rho = alpha+sp.I*tau
F = s-rho
G = s-rho
assert sp.simplify(sp.diff(G,s)/G-sp.diff(F,s)/F) == 0
result['auxiliary_cancellation'] = {'target_zero': str(rho), 'log_derivative_difference': '0'}

N, n, M, m, R, u, v, delta = sp.symbols('N n M m R u v delta')
comparison_gap = n*(M-m*R+u)+2*N*delta-N*(M-v)
rearranged_gap = n*u+N*v+2*N*delta-(N-n)*M-n*m*R
assert sp.expand(comparison_gap-rearranged_gap) == 0
result['covolume_comparison'] = {'symbolic_rearrangement': 'passed'}

print(json.dumps(result, indent=2))
