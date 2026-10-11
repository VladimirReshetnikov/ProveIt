#!/usr/bin/env python3
"""Independent finite algebra and numerical audits of mixed endpoint formulas."""
from pathlib import Path
import json
import sympy as sp
import mpmath as mp

HERE = Path(__file__).resolve().parent
x, a, b = sp.symbols('x a b')
pi, I = sp.pi, sp.I
exact = []
for M in range(1, 10):
    E = 2*a + M
    expr = sp.exp(I*pi*E*x)*(pi*x/sp.sin(pi*x))**M
    lhs = sp.expand(sp.series(expr, x, 0, M).removeO()).coeff(x, M-1)
    rhs = (2*pi*I)**(M-1)*sp.prod(a+k for k in range(1, M))/sp.factorial(M-1)
    residual = sp.simplify(sp.expand(lhs-rhs))
    assert residual == 0
    exact.append({'M': M, 'endpoint_binomial_residual': str(residual)})

# Degree-two numerator determines constant and first logarithmic moments.
c, theta = sp.symbols('c theta')
q1 = -c*(a+b)+theta*(a-b)/2
numerator = -2*theta*a*(1+q1) + theta*(a-b)+theta**2*(a-b)**2/2
H1 = sp.cancel(numerator/(a+b))
expected = -theta+(2*theta*c-theta**2/2)*a+(theta**2/2)*b
assert sp.expand(H1-expected) == 0
exact.append({'first_log_moments_residual': '0'})

mp.mp.dps = 80
def mean(alpha, beta):
    total, orient = alpha+beta, alpha-beta
    return (mp.exp(mp.pi*1j*orient/2)*mp.gamma(1+total)
            *mp.rgamma(1+alpha)*mp.rgamma(1+beta)/(2*mp.pi)**total)

def encode(z):
    z = mp.mpc(z)
    return {'real': mp.nstr(z.real, 55), 'imag': mp.nstr(z.imag, 55)}

alpha = mp.mpc('0.7', '0.2')
beta = mp.mpc('0.8', '-0.1')
integral = mp.quad(lambda t: (mp.sin(mp.pi*t)/mp.pi)**(alpha+beta)
                   *mp.exp(mp.pi*1j*(alpha-beta)*t), [0, mp.mpf('0.5'), 1])
gamma_mean = mean(alpha, beta)
assert abs(integral-gamma_mean) < mp.mpf('1e-75')
numeric = {'working_dps': mp.mp.dps,
           'ordinary_beta_mean': {'integral': encode(integral),
                                  'gamma': encode(gamma_mean),
                                  'absolute_residual': mp.nstr(abs(integral-gamma_mean), 12)},
           'ray_checks': [], 'quadratic_path_checks': []}

tiny = mp.mpf('1e-30')
for av, bv in [(1, 0), (1, 1), (0, 1), (2, -1)]:
    aa, bb = -1+av*tiny, bv*tiny
    raw = mean(aa, bb)
    quotient = (1+mp.exp(mp.pi*1j*(aa-bb)))/(aa+bb+1)
    raw_limit = -2*mp.pi*1j*av/(av+bv)
    completed = raw-quotient
    assert abs(raw-raw_limit) < mp.mpf('1e-26')
    assert abs(completed+mp.pi*1j) < mp.mpf('1e-26')
    numeric['ray_checks'].append({'a': av, 'b': bv, 'raw': encode(raw),
                                 'raw_limit': encode(raw_limit),
                                 'completed': encode(completed)})

for cv in [1, 2, -1]:
    D = mp.mpf('1e-20')
    T = cv*D**2
    aa, bb = -1+(T+D)/2, -1+(T-D)/2
    raw = mean(aa, bb)
    quotient = (1-mp.exp(mp.pi*1j*D))*mp.pi*1j*D/T
    assert abs(raw-mp.pi**2/cv) < mp.mpf('1e-17')
    assert abs(raw-quotient) < mp.mpf('1e-17')
    numeric['quadratic_path_checks'].append({'c': cv, 'raw': encode(raw),
                                            'expected_limit': encode(mp.pi**2/cv),
                                            'completed': encode(raw-quotient)})

report = {'status': 'passed', 'exact_checks': exact,
          'numerical_diagnostics': numeric,
          'scope': 'Finite symbolic identities plus numerical audits; analytic proofs in article section 2.'}
(HERE/'mixed_orientation_checks.json').write_text(json.dumps(report, indent=2)+'\n')
print(json.dumps({'status':'passed', 'exact_checks':len(exact),
                  'beta_mean_residual':numeric['ordinary_beta_mean']['absolute_residual'],
                  'ray_checks':len(numeric['ray_checks']),
                  'quadratic_path_checks':len(numeric['quadratic_path_checks'])}, indent=2))
