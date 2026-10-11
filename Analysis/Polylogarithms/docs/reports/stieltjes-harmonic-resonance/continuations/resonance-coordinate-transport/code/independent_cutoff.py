"""Independent lower-cutoff primitive check for nonlinear finite parts.

The actual cutoff correction is computed in the source coordinate x:
  1. invert f formally;
  2. transform the test jet with the inverse Jacobian;
  3. integrate each x^m log(x)^ell singular monomial;
  4. compose the primitive with f and extract its cutoff constant.
No residue or alpha polynomial occurs on that side of the comparison.
The same local calculation applies to a compactly supported test function
which agrees with the specified polynomial near the origin.
"""
from __future__ import annotations

import json
from pathlib import Path

import sympy as s

t, x, Z = s.symbols('t x Z')


def trunc(expr, variable, degree):
    return s.series(expr, variable, 0, degree + 1).removeO().expand()


def inverse_jet(f, degree):
    """Solve f(g(x)) = x through the requested degree, by coefficients."""
    q = s.expand(f).coeff(t, 1)
    g = x/q
    for k in range(2, degree + 1):
        # Unknown coefficient enters f(g) linearly with multiplier q.
        residual = trunc(f.subs(t, g), x, k).coeff(x, k)
        g -= residual*x**k/q
    return s.expand(g)


def singular_polynomial(n, r):
    """Obtain d_x^r(log(x)^n/x) = x^(-r-1) P(log(x)) by Leibniz."""
    P = Z**n
    for power in range(1, r + 1):
        P = s.diff(P, Z) - power*P
    return s.expand(P)


def monomial_primitive_polynomial(P, exponent):
    """Integral x^(exponent-1) P(log x) dx = x^exponent Q(log x).

    For exponent 0, the prefactor is 1 and Q(0)=0. This normalization
    makes every lower-endpoint primitive have zero cutoff constant in x.
    """
    if exponent == 0:
        return s.integrate(P, (Z, 0, Z))
    Q = s.S.Zero
    derivative = P
    while derivative != 0:
        Q += derivative/exponent
        derivative = -s.diff(derivative, Z)/exponent
    return s.expand(Q)


def primitive_cutoff_values(n, r, f, g=None):
    """Actual f^*FP_x h - FP_t(h o f) on each test t^k, 0<=k<=r."""
    if g is None:
        g = inverse_jet(f, r+1)
    q = s.expand(f).coeff(t, 1)
    U = s.cancel(f/(q*t))
    # The log(t)^0 coefficient of log(f(t)) is log(q)+log(U(t)).
    logarithm = s.log(q) + trunc(s.log(U), t, r)
    P = singular_polynomial(n, r)
    source_primitives = [monomial_primitive_polynomial(P, j-r)
                         for j in range(r+1)]
    result = []
    for k in range(r+1):
        # This inverse Jacobian distinguishes scalar distribution pullback.
        psi = trunc(g**k*s.diff(g, x), x, r)
        correction = s.S.Zero
        for j in range(r+1):
            coefficient = psi.coeff(x, j)
            if coefficient == 0:
                continue
            exponent = j-r
            Q = source_primitives[j]
            # Primitive term x^(j-r) Q(log x), composed with x=f(t).
            # Extract t^0 log(t)^0 from its finite Laurent-log expansion.
            analytic = q**exponent*U**exponent*Q.subs(Z, logarithm)
            correction += coefficient*trunc(analytic, t, -exponent).coeff(t, -exponent)
        # Keep a polynomial in log(q); generic simplify can combine its
        # rational linear terms into logarithms of enormous integers.
        result.append(s.expand(correction))
    return result


def residue_prediction(n, r, f):
    """Prediction under audit, independently built from its z-generator."""
    z = s.symbols('z')
    E = s.prod(1-z/s.Integer(j) for j in range(1, r+1))
    alpha = s.factorial(n)*trunc(E*(sum((Z*z)**h/s.factorial(h)
                                     for h in range(1, n+2))), z, n+1).coeff(z, n+1)
    q = s.expand(f).coeff(t, 1)
    U = s.cancel(f/(q*t))
    logarithm = s.log(q) + trunc(s.log(U), t, r)
    analytic = q**(-r-1)*U**(-r-1)*alpha.subs(Z, logarithm)
    jet = trunc(analytic, t, r)
    return [s.expand((-1)**r*s.factorial(r)*jet.coeff(t, r-k))
            for k in range(r+1)]


def run_checks():
    # Generic nonlinear jets, one with scale and one with unit tangent.
    normalized = t+s.Rational(2,3)*t**2-s.Rational(1,5)*t**3+s.Rational(1,7)*t**4
    cases = []
    for q in [s.S.One, s.Integer(2)]:
        f = q*normalized
        for r in range(4):
            g = inverse_jet(f, r+1)
            for n in range(2*r+3):
                actual = primitive_cutoff_values(n, r, f, g)
                predicted = residue_prediction(n, r, f)
                assert all(s.expand(a-b) == 0 for a,b in zip(actual, predicted)), (q,n,r,actual,predicted)
                cases.append({'scale':str(q),'n':n,'r':r,
                              'test_count':r+1,
                              'cutoff_pairings_on_monomials':[str(v) for v in actual]})
    return {'status':'passed',
            'method':'Integrate the singular source germ against (phi o f^{-1})(f^{-1})\u2032, then extract the constant of the composed primitive.',
            'scope':'Exact rational and symbolic log(2) comparisons; not a numerical truncation or proof by residue substitution.',
            'case_count':len(cases),
            'monomial_pairing_count':sum(c['test_count'] for c in cases),
            'cases':cases}


if __name__ == '__main__':
    result = run_checks()
    path = Path(__file__).resolve().parents[1] / 'results' / 'independent_cutoff_checks.json'
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps({k:v for k,v in result.items() if k != 'cases'}))
