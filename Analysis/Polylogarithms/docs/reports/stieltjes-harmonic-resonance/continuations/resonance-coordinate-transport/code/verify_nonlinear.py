"""Exact finite-algebra checks for the nonlinear finite-part theorem.

These complement its analytic proof; they do not numerically certify it.
"""
from __future__ import annotations

import json
from pathlib import Path

import sympy as s
from independent_cutoff import run_checks as run_cutoff_checks

t, L, a, b, A, B = s.symbols('t L a b A B')


def E(r):
    return s.prod(1-L/s.Integer(j) for j in range(1, r+1))


def alpha(n, r):
    e = s.Poly(E(r), L)
    return s.expand(s.factorial(n)*sum(
        e.nth(j)*L**(n+1-j)/s.factorial(n+1-j)
        for j in range(min(r, n)+1)
    ))


def differentiated_log_polynomial(n, r):
    # D_x[x^(-k)P(log x)] = x^(-k-1)[P' - kP].
    P = L**n
    for k in range(1, r+1):
        P = s.diff(P, L)-k*P
    return s.expand(P)


def coordinate_correction(n, r, normalized_jet, scale=1, log_scale=None):
    """Return coefficients of delta^(j), j=0,...,r, for f(t)=scale*t*jet.

    The normalized jet has constant coefficient one. A symbolic log_scale
    may represent log(scale) independently, useful for exact scale tests.
    Only its terms through t**r are used. This computes pullback of the
    pointwise finite part T_{n,r}; pullback of D**r G_n uses b instead.
    """
    if n < 0 or r < 0 or int(n) != n or int(r) != r:
        raise ValueError('n and r must be nonnegative integers')
    n, r = int(n), int(r)
    normalized_jet = s.sympify(normalized_jet)
    scale = s.sympify(scale)
    if s.expand(normalized_jet).subs(t, 0) != 1 or scale == 0:
        raise ValueError('The normalized jet must begin with 1 and scale must be nonzero')
    if log_scale is None:
        log_scale = s.log(scale)
    log_jet = s.series(s.log(normalized_jet), t, 0, r+1).removeO()
    inverse = s.series(normalized_jet**(-r-1), t, 0, r+1).removeO()
    composed_alpha = s.series(alpha(n,r).subs(L, log_scale+log_jet),
                             t, 0, r+1).removeO()
    product = s.Poly(s.expand(inverse*composed_alpha), t)
    return tuple(s.expand(scale**(-r-1)*(-1)**(r+j)*s.factorial(r)
                          /s.factorial(j)*product.nth(r-j))
                 for j in range(r+1))


def run_checks():
    checks = []
    for r in range(9):
        for n in range(11):
            P = differentiated_log_polynomial(n, r)
            Q = s.integrate(P, (L, 0, L))
            assert s.expand(Q-(-1)**r*s.factorial(r)*alpha(n, r)) == 0
            checks.append(f'generator r={r} n={n}')

    # Universal composition is a finite antiderivative identity. Keep both
    # coordinate logarithms independent so the scale terms are tested too.
    for ell in range(13):
        rhs = B**(ell+1)/s.Integer(ell+1)+sum(
            s.binomial(ell,k)*B**(ell-k)*A**(k+1)/s.Integer(k+1)
            for k in range(ell+1)
        )
        assert s.expand(rhs-(A+B)**(ell+1)/s.Integer(ell+1)) == 0
        checks.append(f'cocycle logarithmic degree={ell}')

    # Direct finite-jet multiplication for generic r=1,2, retaining arbitrary
    # log(q)=L. The omitted overall factors q^(-r-1) are scalar.
    U = 1+a*t+b*t*t
    tables = {}
    for r in (1, 2):
        for n in range(7):
            al = alpha(n, r)
            actual = coordinate_correction(n,r,U,log_scale=L)
            if r == 1:
                expected = [a*(2*al-s.diff(al,L)), al]
            else:
                expected = [
                    (12*a*a-6*b)*al+(2*b-7*a*a)*s.diff(al,L)+a*a*s.diff(al,L,2),
                    2*a*(3*al-s.diff(al,L)), al,
                ]
            assert all(s.expand(x-y) == 0 for x,y in zip(actual, expected))
            if n <= 4:
                tables[f'r={r},n={n},q=1'] = [str(s.expand(x.subs(L,0))) for x in actual]
            checks.append(f'generic nonlinear table r={r} n={n}')

    # The sharpness coefficient and high-index vanishing are checked from
    # polynomial order, for a wide finite range independent of the proof.
    for r in range(1, 13):
        for n in range(r,2*r):
            d = n+1-r
            p = s.Poly(alpha(n,r),L)
            assert all(p.nth(j) == 0 for j in range(d))
            assert p.nth(d) == s.Rational((-1)**r*s.factorial(n),
                                          s.factorial(r)*s.factorial(d))
        n = 2*r-1
        p = s.Poly(alpha(n,r), L)
        expected = s.Rational((-1)**r*s.factorial(2*r-1),s.factorial(r)**2)
        assert all(p.nth(j) == 0 for j in range(r))
        assert p.nth(r) == expected
        for n in range(2*r, 2*r+7):
            p = s.Poly(alpha(n,r), L)
            assert all(p.nth(j) == 0 for j in range(r+1))
        checks.append(f'sharp filtration and vanishing r={r}')

    cutoff = run_cutoff_checks()
    # Cross-check the reusable coefficient API against the independent
    # original-coordinate primitive calculation on every recorded test jet.
    normalized_jet = 1+s.Rational(2,3)*t-s.Rational(1,5)*t**2+s.Rational(1,7)*t**3
    for case in cutoff['cases']:
        n, r, q = case['n'], case['r'], s.Integer(case['scale'])
        coefficients = coordinate_correction(n,r,normalized_jet,scale=q)
        expected_pairings = [(-1)**j*s.factorial(j)*value
                             for j,value in enumerate(coefficients)]
        actual_pairings = [s.sympify(value) for value in case['cutoff_pairings_on_monomials']]
        assert all(s.expand(left-right) == 0
                   for left,right in zip(expected_pairings,actual_pairings)), case

    result = {
        'status': 'passed',
        'exact_checks': len(checks),
        'tests': checks,
        'tangent_identity_tables_delta_order_ascending': tables,
        'independent_cutoff': cutoff,
        'scope': 'Exact polynomial and inverse-Jacobian cutoff-primitive checks; analytic distribution theorem proved separately.',
    }
    out = Path(__file__).resolve().parents[1] / 'results' / 'nonlinear_checks.json'
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps({'status':result['status'],'exact_algebra_cases':len(checks),
                      'cutoff_cases':cutoff['case_count'],
                      'cutoff_monomial_pairings':cutoff['monomial_pairing_count'],
                      'table_rows':len(tables),'output':str(out)}))
    return result


if __name__ == "__main__":
    run_checks()
