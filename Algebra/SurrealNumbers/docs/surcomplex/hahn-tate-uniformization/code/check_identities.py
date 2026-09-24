#!/usr/bin/env python3
"""Exact finite checks for the Hahn--Tate article (Python 3.9+, SymPy).

These checks verify specified truncations, not the infinite-series theorems.
No network access or floating-point arithmetic is used.
"""
from __future__ import annotations
import json
from pathlib import Path
import platform
import sympy as s


def convolution(a, b, n):
    return [s.expand(sum(a[k] * b[d-k] for k in range(d+1)))
            for d in range(n+1)]


def main() -> None:
    u, q, h, J = s.symbols('u q h J')
    n = 5
    a4 = [s.Integer(0)] + [-5 * sum(m**3 for m in s.divisors(d))
                           for d in range(1, n+1)]
    a6 = [s.Integer(0)] + [-sum(s.Rational(5*m**3+7*m**5, 12)
                               for m in s.divisors(d)) for d in range(1, n+1)]
    x = [u / (1-u)**2]
    y = [u**2 / (1-u)**3]
    for d in range(1, n+1):
        x.append(s.expand(sum(m*(u**m+u**(-m)-2) for m in s.divisors(d))))
        y.append(s.expand(sum(s.Rational(m*(m-1), 2)*u**m
                            - s.Rational(m*(m+1), 2)*u**(-m) + m
                            for m in s.divisors(d))))
    xx = convolution(x, x, n)
    xxx = convolution(xx, x, n)
    yy = convolution(y, y, n)
    xy = convolution(x, y, n)
    a4x = convolution(a4, x, n)
    curve = [s.cancel(yy[d]+xy[d]-xxx[d]-a4x[d]-a6[d]) for d in range(n+1)]
    diff = [s.cancel(u*s.diff(x[d], u)-x[d]-2*y[d]) for d in range(n+1)]
    inversion = [s.cancel(y[d].subs(u, 1/u)+x[d]+y[d]) for d in range(n+1)]
    assert all(c == 0 for c in curve+diff+inversion)

    # All modular computations use rational formal q-series.
    order = 9
    A4 = -5 * sum(sum(m**3 for m in s.divisors(d))*q**d for d in range(1, order+1))
    A6 = -sum(sum(s.Rational(5*m**3+7*m**5,12) for m in s.divisors(d))*q**d
              for d in range(1, order+1))
    # a1=1, a2=a3=0: b2=1, b4=2a4, b6=4a6, b8=a6-a4^2.
    delta = s.series(-(A6-A4**2)-8*(2*A4)**3-27*(4*A6)**2
                     +9*(2*A4)*(4*A6), q, 0, order+1).removeO().expand()
    product = q
    for k in range(1, order+1):
        product = s.series(product*(1-q**k)**24, q, 0, order+1).removeO().expand()
    assert s.expand(delta-product) == 0
    c4 = 1-48*A4
    # Dividing by q loses one order; only claim coefficients known from the input.
    jseries = s.series(c4**3/delta, q, 0, 6).removeO().expand()
    invj = s.series(delta/c4**3, q, 0, 8).removeO().expand()
    q_of_J = J
    inverse_coefficients = {1: 1}
    for degree in range(2, 7):
        c = s.Symbol('c')
        candidate = q_of_J+c*J**degree
        coeff = s.series(invj.subs(q, candidate), J, 0, degree+1).removeO().expand().coeff(J, degree)
        root = s.solve(coeff, c)[0]
        q_of_J += root*J**degree
        inverse_coefficients[degree] = int(root)
    assert s.series(invj.subs(q, q_of_J), J, 0, 7).removeO().expand() == J

    # The q^0 formal parameter has positive linear coefficient, not its negative.
    z0 = s.cancel(-x[0]/y[0]).subs(u, 1+h)
    z0_series = s.series(z0, h, 0, 5).removeO().expand()
    assert z0_series == h-h**2+h**3-h**4

    # Bilateral theta identity coefficient comparison, excluding truncation edges.
    theta_shift_checks = []
    for k in range(-5, 5):
        # q^k a_k = -a_(k+1); integer rational signs avoid float arithmetic.
        lhs = s.Integer(-1)**k*q**(k*(k-1)//2+k)
        rhs = -s.Integer(-1)**(k+1)*q**((k+1)*k//2)
        assert s.expand(lhs-rhs) == 0
        theta_shift_checks.append(k)

    # Lexicographic rank-two witnesses: alpha=(0,1), beta=(1,0).
    descending_theta = [(-k, k*(k+1)//2) for k in range(1, 8)]
    assert all(descending_theta[k+1] < descending_theta[k] for k in range(6))
    # Finite-index ramification in Z^r: order(alpha mod n Gamma).
    from math import gcd
    degree_examples = []
    for n_root, alpha in [(12, (6, 4)), (4, (0, 6)), (5, (0, 1))]:
        common = n_root
        for a in alpha:
            common = gcd(common, a)
        degree_examples.append({'n': n_root, 'alpha': alpha, 'degree': n_root//common})

    report = {
        'status': 'PASS',
        'python': platform.python_version(),
        'sympy': s.__version__,
        'scope': 'Exact finite truncation checks only; not a formal proof of the article.',
        'curve_equation_q_degrees_checked': list(range(n+1)),
        'differential_identity_q_degrees_checked': list(range(n+1)),
        'inversion_identity_q_degrees_checked': list(range(n+1)),
        'a4_coefficients_q_0_to_5': [str(c) for c in a4],
        'a6_coefficients_q_0_to_5': [str(c) for c in a6],
        'delta_product_degrees_checked': list(range(order+1)),
        'delta': str(delta),
        'j_through_q5': str(jseries),
        'q_as_series_in_J_through_J6': str(q_of_J),
        'inverse_j_coefficients': inverse_coefficients,
        'formal_parameter_at_q0': str(z0_series),
        'theta_shift_indices_checked': theta_shift_checks,
        'rank_two_descending_leading_exponents': descending_theta,
        'torsion_degree_examples': degree_examples,
    }
    out = Path(__file__).resolve().parents[1]/'data'/'verification.json'
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(report, indent=2)+'\n', encoding='utf-8')
    print(json.dumps(report, indent=2))


if __name__ == '__main__':
    main()
