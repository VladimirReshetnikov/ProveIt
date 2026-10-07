#!/usr/bin/env python3
"""Independent SymPy checks of exact amplitude and inverse cancellations.

These checks verify symbolic identities and finite series coefficients.
Analytic convergence, remainder bounds, and eventual inverse monotonicity
are proved in the report, not by this finite computation.
"""
from collections import Counter
import sympy as sp
from magma import amplitude, partitions, require, sectors_through_defect, trace_orbits


def sympy_amplitude(mu, order=5):
    t = sp.Symbol('t')
    n = sp.Symbol('n', integer=True, positive=True)
    s, c = sum(mu), len(mu)
    h = trace_orbits(mu)
    beta = s - c * s + sum(h.values()) + s * (s - 1) // 2
    power = s + (n - s) * (n - s + 1) / 2 + (n - s) * c + sum(h.values()) - n * (n + 1) / 2
    require(sp.expand(power + (s - c) * n - beta) == 0, 'Sector power cancellation failed')
    fixed = lambda power: sum(k for k in mu if power % k == 0)
    constant = sp.Rational(3 * s * s, 4) - sp.Rational(s, 2) - c * s + sum(fixed(k) for k in mu)
    expr = sum(sp.log(1 - j * t) for j in range(s))
    expr += (1 / t - s) * (1 / t - s + 1) / 2 * sp.log(1 - s * t)
    expr += (1 / t - s) * sum(sp.log(1 - (s - fixed(k)) * t) for k in mu)
    expr += sum(hh * sp.log(1 - (s - fixed(length)) * t) for length, hh in h.items())
    raw = sp.series(expr, t, 0, order + 1).removeO().expand()
    require(raw.coeff(t, -1) == -sp.Rational(s, 2), 'Symbolic amplitude pole mismatch')
    require(raw.coeff(t, 0) == constant, 'Symbolic amplitude constant mismatch')
    logs = [raw.coeff(t, j) for j in range(1, order + 1)]
    coefficients = [sp.Integer(1)]
    for j in range(1, order + 1):
        value = 0
        for p in partitions(j):
            term = sp.Integer(1)
            for k, multiplicity in Counter(p).items():
                term *= logs[k - 1]**multiplicity / sp.factorial(multiplicity)
            value += term
        coefficients.append(sp.factor(value))
    expected = amplitude(mu, order)
    require([str(v) for v in logs] == expected['log_coeff'], 'SymPy logarithmic coefficients disagree')
    require([str(v) for v in coefficients] == expected['relative_coeff'], 'SymPy amplitude coefficients disagree')
    return {'mu': list(mu), 'pole': str(raw.coeff(t, -1)), 'constant': str(constant),
            'power_of_n': str(sp.expand(power)), 'beta': beta,
            'log_coeff': [str(v) for v in logs],
            'relative_coeff': [str(v) for v in coefficients]}


def inverse_cancellations():
    # Treat w=log(u), ell=log(2*pi), t=1/u as formal symbols. Holding w
    # symbolic while expanding log(1+delta*t) preserves every log(u) term.
    t = sp.Symbol('t', positive=True)
    w, ell, delta, epsilon = sp.symbols('w ell delta epsilon', real=True)
    x = 1 / t + delta + epsilon * t
    logx = w + sp.log(1 + delta * t + epsilon * t**2)
    stirling_F = x**2 * logx / 2 - x * logx / 2 + x - logx / 2 - ell / 2 - 1 / (12 * x)
    residual = sp.series(stirling_F - w / (2 * t**2), t, 0, 2).removeO().expand()
    delta_solution = (w / 2 - 1) / (w + sp.Rational(1, 2))
    alternative = sp.Rational(1, 2) - 5 / (4 * w + 2)
    require(sp.cancel(delta_solution - alternative) == 0, 'Inverse delta identities disagree')
    leading = sp.factor(residual.coeff(t, -1))
    require(sp.cancel(leading - (delta * (w + sp.Rational(1, 2)) - w / 2 + 1)) == 0,
            'Inverse leading discrepancy was not as derived')
    require(sp.cancel(leading.subs(delta, delta_solution)) == 0, 'Inverse order-u cancellation failed')
    require(residual.coeff(t, -2) == 0, 'Inverse leading H(u) cancellation failed')
    constant = sp.factor(residual.coeff(t, 0).subs({delta: delta_solution, epsilon: 0}))
    next_epsilon = sp.factor(-constant / (w + sp.Rational(1, 2)))
    remaining_constant = residual.coeff(t, 0).subs(delta, delta_solution).subs(epsilon, next_epsilon)
    require(sp.cancel(remaining_constant) == 0, 'Inverse order-one cancellation failed')
    require(sp.limit(delta_solution, w, sp.oo) == sp.Rational(1, 2), 'Delta limit mismatch')
    require(sp.limit(next_epsilon, w, sp.oo) == sp.Rational(5, 8), 'Next inverse coefficient limit mismatch')
    # For v=W(4L), u=exp(v/2) gives u^2*log(u)/2=v*exp(v)/4=L.
    v = sp.Symbol('v', positive=True)
    u = sp.exp(v / 2)
    lambert_residual = sp.simplify(u**2 * (v / 2) / 2 - v * sp.exp(v) / 4)
    require(lambert_residual == 0, 'Lambert seed identity failed')
    return {'formal_symbols': {'t': '1/u', 'w': 'log(u)', 'ell': 'log(2*pi)'},
            'seed': 'u=sqrt(4*L/W(4*L)); H(u)=L with H(x)=x^2*log(x)/2',
            'leading_residual_before_delta': str(leading),
            'delta': str(delta_solution), 'alternative_delta': str(alternative),
            'order_u_residual_after_delta': '0',
            'order_one_residual_after_delta': str(constant),
            'optional_next_inverse_coefficient': str(next_epsilon),
            'order_one_residual_after_next_coefficient': '0',
            'next_inverse_coefficient_limit': '5/8',
            'scope': 'Finite symbolic cancellations. The report supplies the analytic O(1/u) inverse-error argument.'}


def run():
    return {'status': 'pass', 'dependency': {'sympy': sp.__version__},
            'description': 'Independent direct CAS expansion of exact logarithmic factors; symbolic inverse cancellations',
            'amplitudes': [sympy_amplitude(mu) for mu in sectors_through_defect(4)],
            'inverse_cancellations': inverse_cancellations(),
            'limitations': ['Finite symbolic checks do not replace the analytic convergence and global-tail proofs.',
                           'No numerical cutoff for eventual inverse monotonicity is certified.']}
