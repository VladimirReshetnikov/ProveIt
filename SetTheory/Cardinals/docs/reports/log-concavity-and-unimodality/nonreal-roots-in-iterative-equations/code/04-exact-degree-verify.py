#!/usr/bin/env python3
"""Exact checks for Two Observations Determine the Coordinate.

Tested with Python 3.13.5 and SymPy 1.14.0. No numerical root approximations
are used. These finite checks supplement, and do not prove, the theorems.
Run from the package root: python code/verify.py --output-dir results
"""
from __future__ import annotations
import argparse
import json
import platform
import random
from pathlib import Path
from typing import Any
import sympy as sp

T, t, X, Y, z = sp.symbols('T t X Y z')


def polynomial(expr: sp.Expr, variable: sp.Symbol = t) -> sp.Poly:
    """Construct an exact polynomial, allowing algebraic coefficients."""
    return sp.Poly(sp.expand(expr), variable, extension=True)


def normalized_candidate(H: sp.Expr, d: int) -> sp.Expr:
    """The only possible monic, zero-constant right factor of degree d.

    The top d-1 nonleading coefficients of H determine this candidate;
    existence as an actual compositional factor is checked separately.
    """
    p = polynomial(H)
    n = p.degree()
    if n < 1 or d < 1 or n % d:
        raise ValueError('Require a nonconstant H and a positive divisor d of deg H.')
    m = n // d
    F = sp.expand(H / p.LC())
    W = t**d
    for j in range(1, d):
        target = polynomial(F).nth(n - j)
        known = polynomial(W**m).nth(n - j)
        W += sp.cancel((target - known) / m) * t**(d - j)
    return sp.expand(W)


def composition_quotient(H: sp.Expr, W: sp.Expr) -> sp.Expr | None:
    """Return A(s), represented using z, with H=A(W), or None."""
    d = polynomial(W).degree()
    if d < 1:
        raise ValueError('W must be nonconstant.')
    leading = polynomial(W).LC()
    remaining = sp.expand(H)
    A = sp.Integer(0)
    while remaining != 0:
        p = polynomial(remaining)
        e = p.degree()
        if e % d:
            return None
        k = e // d
        c = sp.cancel(p.LC() / leading**k)
        A += c * z**k
        remaining = sp.expand(remaining - c * W**k)
    assert sp.expand(A.subs(z, W) - H) == 0
    return sp.expand(A)


def common_field_generator(H: sp.Expr, a: sp.Expr) -> tuple[int, sp.Expr]:
    """Compute the maximal normalized eigen-right-factor.

    This implements the article's theorem-based algorithm. The verifier
    compares it with an independent generic-fiber polynomial gcd.
    """
    H, a = sp.sympify(H), sp.sympify(a)
    n = polynomial(H).degree()
    if n < 1 or a == 0:
        raise ValueError('Require nonconstant H and a nonzero multiplier.')
    for d in reversed(sp.divisors(n)):
        W = normalized_candidate(H, d)
        if sp.expand(W.subs(t, a*t) - a**d * W) != 0:
            continue
        if composition_quotient(H, W) is not None:
            return int(d), W
    raise AssertionError('The linear right factor must always pass.')


def independent_fiber_degree(H: sp.Expr, a: sp.Expr) -> int:
    """Degree in T of the generic common fiber, independent of factor search."""
    first = sp.expand(H.subs(t, T) - H)
    second = sp.expand(H.subs(t, a*T) - H.subs(t, a*t))
    domain = sp.QQ_I if (first.has(sp.I) or second.has(sp.I)) else sp.QQ
    g = sp.gcd(sp.Poly(first, T, t, domain=domain),
               sp.Poly(second, T, t, domain=domain))
    return int(g.degree(T))


def support_gcd(H: sp.Expr) -> int:
    exponents = [mon[0] for mon, c in polynomial(H).terms() if c != 0 and mon[0] > 0]
    if not exponents:
        raise ValueError('H must be nonconstant.')
    value = exponents[0]
    for exponent in exponents[1:]:
        value = int(sp.igcd(value, exponent))
    return int(value)


def certify_near_reflection(n: int, start: int = 100) -> dict[str, Any]:
    """Find rational epsilon with positive derivative and squarefree critical values.

    Search epsilon=1/((n-1)M), M>=max(start,2). The article proves
    termination because only finitely many epsilon are exceptional.
    """
    if n < 3 or n % 2 == 0:
        raise ValueError('n must be odd and at least 3.')
    M = max(start, 2)
    while True:
        eps = sp.Rational(1, (n-1)*M)
        H = t + t**n + eps*t**(n-1)
        D = sp.Poly(sp.discriminant(H-X, t), X, domain=sp.QQ)
        if D.degree() == n-1 and sp.gcd(D, D.diff()).degree() == 0:
            break
        M += 1
    d = independent_fiber_degree(H, sp.Integer(-1))
    assert d == 1
    G = (X+Y)*(X+Y+2*eps)**(n-1) - 2*eps**n*(X-Y)**(n-1)
    coordinates = {X:H, Y:H.subs(t,-t)}
    assert sp.expand(G.subs(coordinates, simultaneous=True)) == 0
    assert sp.expand((eps*(X-Y)-t*(X+Y+2*eps)).subs(
        coordinates, simultaneous=True)) == 0
    if n <= 5:
        assert sp.expand(sp.resultant(H-X,H.subs(t,-t)-Y,t)+G) == 0
    bound = sp.Rational(M+1, M-1)
    return {'n': n, 'M': M, 'epsilon': str(eps), 'field_index': d,
            'algebraic_degree': n, 'critical_discriminant_degree': D.degree(),
            'critical_discriminant_squarefree': True,
            'critical_discriminant': str(D.as_expr()),
            'graph_polynomial': str(G),
            'rational_recovery_identity_verified': True,
            'resultant_identity_verified': (n <= 5),
            'lip_and_inverse_lip_upper_bound': str(bound),
            'distortion_upper_bound': str(bound**2),
            'sharper_rational_distortion_bound': str(((1+eps)/(1-eps))**2)}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output-dir', type=Path, default=Path('results'))
    args = parser.parse_args()
    counts: dict[str, int] = {}
    records: dict[str, Any] = {}

    # Exhaustive small support atlas: every nonempty subset of {1,...,6}.
    atlas = 0
    for mask in range(1, 1 << 6):
        H = sum(t**(k+1) for k in range(6) if (mask >> k) & 1)
        for a in (sp.Integer(2), sp.Integer(-2), sp.Rational(1, 2),
                  sp.Integer(-1), sp.Integer(1)):
            d, W = common_field_generator(H, a)
            assert d == independent_fiber_degree(H, a), (H, a, d, W)
            if a not in (-1, 1):
                assert d == support_gcd(H), (H, a, d)
            atlas += 1
    counts['binary_support_polynomials'] = (1 << 6)-1
    counts['binary_support_multiplier_cases'] = atlas
    print(f'PASS: {atlas} exhaustive support/multiplier cases', flush=True)

    rng = random.Random(20260929)
    random_cases = 0
    for _ in range(30):
        n = rng.randint(2, 9)
        H = t**n + sum(sp.Integer(rng.randint(-2, 2))*t**k for k in range(n))
        for a in (sp.Integer(-2), sp.Integer(-1), sp.Rational(1, 2)):
            d, _ = common_field_generator(H, a)
            assert d == independent_fiber_degree(H, a)
            if a != -1:
                assert d == support_gcd(H)
            random_cases += 1
    counts['seeded_polynomials'] = 30
    counts['seeded_multiplier_cases'] = random_cases
    print(f'PASS: {random_cases} seeded exact cases', flush=True)

    U3 = z + z**3 + sp.Rational(1, 4)*z**2
    W3 = t+t**3
    named = [
        ('decomposable_hyperbolic', sp.expand(W3.subs(t, W3)), -2, 1),
        ('odd_reflection', t+t**9, -1, 9),
        ('degree_nine_degree_three_involution', sp.expand(U3.subs(z, W3)), -1, 3),
        ('primitive_degree_nine_involution', t+t**9+sp.Rational(1,16)*t**8, -1, 1),
        ('support_gcd_two', t**6+t**4, 2, 2),
        ('support_gcd_three', t**6+t**3+7, -2, 3),
        ('fourth_root_scalar', t+t**5, sp.I, 5),
        ('fourth_root_quotient', sp.expand((z+z**2).subs(z,t+t**5)), sp.I, 5),
    ]
    named_results = []
    for name,H,a,expected in named:
        a = sp.sympify(a)
        d,W = common_field_generator(H,a)
        assert d == independent_fiber_degree(H,a) == expected
        named_results.append({'name':name,'H':str(H),'a':str(a),'W':str(W),
                              'field_index':d,'algebraic_degree':int(sp.degree(H,t))//d})
    counts['structured_cases'] = len(named)
    records['structured_cases'] = named_results
    print(f'PASS: {len(named)} structured cases including fourth roots of unity', flush=True)

    divisor_cases = 0
    for n in range(1, 16, 2):
        for m in sp.divisors(n):
            d = n // m
            W = t if d == 1 else t+t**d
            U = z if m == 1 else z+z**m+sp.Rational(1,2*(m-1))*z**(m-1)
            H = sp.expand(U.subs(z,W))
            assert independent_fiber_degree(H,sp.Integer(-1)) == d
            divisor_cases += 1
    counts['odd_divisor_realizations_through_degree_fifteen'] = divisor_cases
    print(f'PASS: {divisor_cases} odd-divisor realization cases', flush=True)

    families = []
    a = sp.Integer(-2)
    for n in range(3,16,2):
        H = t+t**n
        delta = a-a**n
        Phi = (Y-a**n*X)**n + delta**(n-1)*(Y-a*X)
        assert sp.expand(Phi.subs({X:H,Y:H.subs(t,a*t)}, simultaneous=True)) == 0
        assert sp.expand(H.subs(t,a*a*t) -(a+a**n)*H.subs(t,a*t)
                         +a**(n+1)*H) == 0
        assert independent_fiber_degree(H,a) == 1
        disc = sp.discriminant(H-X,t)
        expected = (-1)**(n*(n-1)//2)*(n**n*X**(n-1)+(n-1)**(n-1))
        assert sp.expand(disc-expected) == 0
        families.append({'n':n,'a':str(a),'inverse_discriminant':str(disc)})
    counts['hyperbolic_family_degrees'] = len(families)
    records['hyperbolic_family'] = families
    print(f'PASS: {len(families)} hyperbolic family degrees and discriminants', flush=True)

    # Independent symbolic identities for subresultant recovery in a non-binomial example.
    H = t+t**2+t**3
    numerator, denominator = 16*X-Y, 16*X-2*Y+14
    assert sp.expand(numerator.subs({X:H,Y:H.subs(t,2*t)}, simultaneous=True)
                     -t*denominator.subs({X:H,Y:H.subs(t,2*t)}, simultaneous=True)) == 0
    subresultants = sp.subresultants(H-X,H.subs(t,2*t)-Y,t)
    assert sp.degree(subresultants[-2],t) == 1
    assert sp.expand(subresultants[-2]-2*(denominator*t-numerator)) == 0
    counts['rational_recovery_identities'] = 1
    records['rational_recovery'] = {'H':str(H),'a':'2',
        't_numerator':str(numerator),'t_denominator':str(denominator)}

    # Resultant multiplicity at a genuine nontrivial common factor.
    H = t**6+t**3
    res = sp.resultant(H-X,H.subs(t,2*t)-Y,t)
    _, factors = sp.factor_list(res)
    assert len(factors) == 1 and factors[0][1] == 3
    assert sp.degree(factors[0][0],Y) == 2
    counts['resultant_power_checks'] = 1
    records['resultant_power'] = {'H':str(H),'a':'2','factorization':str(sp.factor(res))}
    print('PASS: rational recovery and resultant multiplicity', flush=True)

    involutions = [certify_near_reflection(n) for n in (3,5,7,9,11)]
    counts['certified_involution_degrees'] = len(involutions)
    counts['near_reflection_resultant_identities'] = 2
    records['certified_near_reflections'] = involutions
    print(f'PASS: {len(involutions)} exact near-reflection certificates', flush=True)

    report = {'status':'all_checks_passed',
              'scope':'Finite exact algebraic checks; not a proof of universal theorems.',
              'python_version':platform.python_version(),'sympy_version':sp.__version__,
              'seed':20260929,'counts':counts,'records':records}
    args.output_dir.mkdir(parents=True,exist_ok=True)
    (args.output_dir/'verification.json').write_text(json.dumps(report,indent=2)+'\n')
    lines = ['All exact checks passed.','',report['scope'],'',
             f"Python {report['python_version']}; SymPy {report['sympy_version']}",
             f"Seed: {report['seed']}",'']
    lines += [f'{key}: {value}' for key,value in counts.items()]
    lines += ['','Near-reflection certificates:']
    lines += [f"n={r['n']}, epsilon={r['epsilon']}, degree={r['algebraic_degree']}, "
              f"Morse certificate=True, distortion<={r['distortion_upper_bound']}"
              for r in involutions]
    (args.output_dir/'verification.txt').write_text('\n'.join(lines)+'\n')
    print('ALL CHECKS PASSED',flush=True)

if __name__ == '__main__':
    main()
