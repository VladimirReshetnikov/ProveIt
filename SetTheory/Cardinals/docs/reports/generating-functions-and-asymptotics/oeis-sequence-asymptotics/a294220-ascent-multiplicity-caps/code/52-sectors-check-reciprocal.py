#!/usr/bin/env python3
"""Exact algebra used in the reciprocal corollary; asymptotic scope is proved in TeX."""
import json
import sympy as S
tau, delta = S.symbols('tau delta', positive=True)
deficit = 1/tau - 1/(tau+delta)
linear_minus_quadratic = delta/tau**2 - delta**2/(tau**2*(tau+delta))
identity = S.cancel(deficit-linear_minus_quadratic) == 0
first_constant = S.simplify((S.pi**2/6)**(-2)/4 - 9/S.pi**4) == 0
assert identity and first_constant
print(json.dumps({'exact_reciprocal_identity': identity, 'leading_deficit_constant': first_constant, 'all_checks_pass': True}, indent=2))
