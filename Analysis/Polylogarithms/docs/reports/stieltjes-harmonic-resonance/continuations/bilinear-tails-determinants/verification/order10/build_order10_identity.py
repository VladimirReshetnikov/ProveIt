"""Reconstruct and audit the explicit (10,12) power-difference identity.

The exact matrix and Euler--Maclaurin coefficient checks constitute the
algebraic verification. The high-precision finite-sum/tail calculation is
an independent numerical diagnostic, not a replacement for the proof.
"""
from __future__ import annotations
import json
from pathlib import Path
import sympy as s
import mpmath as mp

ROOT = Path(__file__).resolve().parent


def main():
    x = s.Symbol('x')
    a, b = 5, 6
    mu = lambda j: s.bernoulli(2*j)/s.factorial(2*j) if j >= 0 else s.S.Zero
    M = s.Matrix(b, b, lambda t, k: mu(t+k-4)*(
        s.factorial(2*b+2*t-9)/s.factorial(2*b-2*k)
        +(s.factorial(2*t+1)/s.factorial(10-2*k) if k < a else 0)))
    coefficients = [28468113, -73310041, 92514527,
                    -98765059, 145331415, 58535757]
    scale = s.Rational(574862427, 4)
    assert s.Matrix([coefficients])*M == s.Matrix([[scale, 0, 0, 0, 0, 0]])
    P = sum(v*x**(13+2*t) for t, v in enumerate(coefficients))
    Q = s.Poly(s.expand(P.subs(x, x+s.Rational(1, 2))
                        -P.subs(x, x-s.Rational(1, 2))), x)
    assert all(Q.nth(j) == 0 for j in range(1, 23, 2))
    eta = lambda order, j: (s.Rational(1, order-1) if j == 0 else
        s.rf(order, 2*j-1)*s.bernoulli(2*j, s.Rational(1, 2))/s.factorial(2*j))
    L = 48
    c = [sum(eta(10, j)*eta(12, ell-j) for j in range(ell+1))
         for ell in range(L+2)]
    counter = s.expand(Q.nth(22)*c[0]*x**2 + Q.nth(22)*c[1] + Q.nth(20)*c[0])
    expected = (149591379*x**2+1835020425)/11
    assert s.expand(counter-expected) == 0
    rhs = -scale/2
    tail = [sum(Q.nth(2*r)*c[r+h-10] for r in range(12) if r+h >= 10)
            for h in range(1, L+1)]
    mp.mp.dps = 100
    mpr = lambda val: mp.mpf(int(s.numer(val)))/mp.mpf(int(s.denom(val)))
    def evalP(n):
        return sum(mp.mpf(v)*n**(13+2*t) for t, v in enumerate(coefficients))
    reports = []
    for N in (64, 96):
        partial = mp.fsum((evalP(mp.mpf(n+1))-evalP(mp.mpf(n)))
                         *mp.zeta(10, n+1)*mp.zeta(12, n+1)
                         -(mp.mpf(149591379)*(mp.mpf(n)+mp.mpf('.5'))**2
                           +mp.mpf(1835020425))/11
                         for n in range(N))
        correction = mp.fsum(mpr(tail[h-1])*mp.zeta(2*h, mp.mpf(N)+mp.mpf('.5'))
                             for h in range(1, L+1))
        residual = partial+correction-mpr(rhs)
        assert abs(residual) < mp.mpf('1e-60')
        reports.append({'partial_terms': N, 'asymptotic_tail_terms': L,
                        'decimal_precision': mp.mp.dps,
                        'value': mp.nstr(partial+correction, 85),
                        'absolute_residual': mp.nstr(abs(residual), 10),
                        'kind': 'numerical diagnostic; rigorous proof is the exact reconstruction argument'})
    result = {'orders': [10, 12], 'zeta_coordinate': 0,
              'power_difference_coefficients_ascending': coefficients,
              'power_difference_exponents': list(range(13, 24, 2)),
              'scale': str(scale), 'P': str(P),
              'Q_even_coefficients': [str(Q.nth(2*r)) for r in range(12)],
              'counterterm': str(counter), 'right_hand_side': str(rhs),
              'exact_inverse_row_check': True, 'exact_counterterm_check': True,
              'numerical_diagnostics': reports, 'status': 'all checks passed'}
    output = ROOT/'order10_explicit_identity_verified.json'
    output.write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps({'status': result['status'], 'output': str(output),
                      'residuals': [r['absolute_residual'] for r in reports]}, indent=2))


if __name__ == '__main__':
    main()
