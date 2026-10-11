#!/usr/bin/env python3
"""Exact rational coefficient checks for the mixed-inner-sign theorem.

This validates finite identities, not analytic continuation.  The theorem's
proof supplies continuation separately.  All quantities here use SymPy exact
rationals; no floating-point tolerance is used.
"""
from collections import Counter, defaultdict
from functools import lru_cache
from itertools import product
from pathlib import Path
import json
import sympy as S

t, u, v, y = S.symbols("t u v y")


def rat_li(a, z):
    """Li_{-a}(z), a >= 0."""
    f = y / (1-y)
    for _ in range(a):
        f = y * S.diff(f, y)
    return S.cancel(f.subs(y, z))


def roots(p, X):
    if p == 1:
        return [X]
    if p == 2:
        z = S.sqrt(X)
        assert z.is_Rational
        return [z, -z]
    raise ValueError("This exact test fixture uses weights one and two.")


def shuffles(a, b):
    if not a:
        return [b]
    if not b:
        return [a]
    return [(a[0],)+z for z in shuffles(a[1:], b)] + [
        (b[0],)+z for z in shuffles(a, b[1:])]


def shuffle_words(words):
    out = Counter({(): S.Integer(1)})
    for word in words:
        nxt = Counter()
        for old, multiplicity in out.items():
            for new in shuffles(old, word):
                nxt[new] += multiplicity
        out = nxt
    return out


def word_indices(word):
    indices, colors, zeroes = [], [], 0
    for letter in word:
        if letter == 0:
            zeroes += 1
        else:
            indices.append(zeroes+1)
            colors.append(letter)
            zeroes = 0
    assert zeroes == 0
    return tuple(indices), tuple(colors)


def partial_fractions(spec):
    R = S.Integer(1)
    multiplicities = defaultdict(int)
    for s, p, X in spec:
        if s <= 0:
            R *= rat_li(-s, X*t**p)
            for a in roots(p, X):
                multiplicities[a] += 1-s
    R = S.cancel(R)
    fractions = []
    for a, M in multiplicities.items():
        g = S.cancel(u**M * R.subs(t, (1-u)/a))
        coeffs = S.Poly(S.series(g, u, 0, M).removeO(), u)
        for h in range(1, M+1):
            c = coeffs.nth(M-h)
            if c:
                fractions.append((a, h, c))
    return R, fractions


def mix_terms(spec):
    positive = [(s, p, X) for s, p, X in spec if s > 0]
    assert positive and len(positive) < len(spec)
    R, fractions = partial_fractions(spec)
    factor = S.prod(p**(s-1) for s, p, X in positive)
    result = defaultdict(lambda: S.Integer(0))
    for choice in product(*(roots(p, X) for s, p, X in positive)):
        words = [(0,)*(s-1)+(a,) for (s, p, X), a
                 in zip(positive, choice)]
        for word, mult in shuffle_words(words).items():
            ks, bs = word_indices(word)
            for a, h, c in fractions:
                eh = S.Poly(S.prod(1+v/S.Integer(j)
                                  for j in range(1, h)), v)
                colors = (a, bs[0]/a) + tuple(
                    bs[j]/bs[j-1] for j in range(1, len(bs)))
                for r in range(h):
                    for ell in range(r+1):
                        indices = (-r+ell, ks[0]-ell)+ks[1:]
                        result[(indices, colors)] += (
                            factor * mult * c * eh.nth(r)
                            * (-1)**ell * S.binomial(r, ell))
    return R, {k: S.cancel(c) for k, c in result.items() if c}


def polynomial_boundaries(M, b):
    if b == 1:
        upper = S.bernoulli(M+1, v)/S.Integer(M+1)
        lower = -S.bernoulli(M+1, v+1)/S.Integer(M+1)
    else:
        f = 1/(1-y)
        Q = 0
        for r in range(M+1):
            Q += S.binomial(M, r)*v**(M-r)*f.subs(y, b)
            f = S.cancel(y*S.diff(f, y))
        upper = -Q
        lower = b*Q.subs(v, v+1)
    return S.Poly(S.expand(upper), v), S.Poly(S.expand(lower), v)


def eliminate_terms(terms):
    out = defaultdict(lambda: S.Integer(0))

    def rec(coefficient, indices, colors):
        j = next((j for j in range(1, len(indices))
                  if indices[j] <= 0), None)
        if j is None:
            out[(indices, colors)] += coefficient
            return
        M, b = -indices[j], colors[j]
        upper, lower = polynomial_boundaries(M, b)
        for side, poly in ((-1, upper), (1, lower)):
            neighbor = j+side
            if neighbor == len(indices):
                scalar = poly.eval(0)
                if scalar:
                    rec(coefficient*scalar,
                        indices[:j]+indices[j+1:],
                        colors[:j]+colors[j+1:])
                continue
            for (degree,), scalar in poly.terms():
                if not scalar:
                    continue
                inds, cols = list(indices), list(colors)
                inds[neighbor] -= degree
                cols[neighbor] *= b
                del inds[j]
                del cols[j]
                rec(coefficient*scalar, tuple(inds), tuple(cols))

    for (indices, colors), coefficient in terms.items():
        rec(coefficient, indices, colors)
    return {k: S.cancel(c) for k, c in out.items() if c}


@lru_cache(None)
def nested_coefficient(n, indices, colors):
    if not indices:
        return S.Integer(1)
    return sum((colors[0]**m * S.Integer(m)**(-indices[0])
                * nested_coefficient(m, indices[1:], colors[1:])
                for m in range(1, n)), S.Integer(0))


def rhs_coeff(n, terms):
    return S.cancel(sum((
        c * S.Integer(n)**(-indices[0])*colors[0]**n
        * nested_coefficient(n, indices[1:], colors[1:])
        for (indices, colors), c in terms.items()), S.Integer(0)))


def original_coeffs(spec, N):
    coeffs = [S.Integer(1)]+[S.Integer(0)]*N
    for s, p, X in spec:
        nxt = [S.Integer(0)]*(N+1)
        for n in range(N+1):
            for m in range(1, n//p+1):
                nxt[n] += coeffs[n-p*m]*X**m*S.Integer(m)**(-s)
        coeffs = nxt
    return coeffs


def main():
    Q = S.Rational
    fixtures = [
        ("three factors, all colors equal", [(1,1,Q(1,2)), (1,1,Q(1,2)), (0,1,Q(1,2))]),
        ("negative first moment, coincident", [(1,1,Q(1,2)), (1,1,Q(1,2)), (-1,1,Q(1,2))]),
        ("four factors and repeated rational pole", [(1,1,Q(1,2)), (1,1,Q(1,2)), (0,1,Q(1,2)), (0,1,Q(1,2))]),
        ("fourth order rational pole", [(1,1,Q(1,2)), (1,1,Q(1,2)), (-3,1,Q(1,2))]),
        ("unequal colors", [(2,1,Q(1,2)), (1,1,-Q(1,3)), (-2,1,Q(1,4))]),
        ("weighted positive and rational factors", [(2,2,Q(1,4)), (1,1,Q(1,3)), (0,2,Q(1,9))]),
        ("weighted repeated rational roots", [(2,1,Q(1,2)), (0,2,Q(1,4)), (-1,2,Q(1,4))]),
        ("two distinct rational sectors", [(2,1,Q(1,2)), (1,1,Q(1,3)), (-1,1,Q(1,2)), (-1,1,-Q(1,3))]),
        ("three positive factors and one negative", [(1,1,Q(1,2)), (1,1,Q(1,3)), (2,1,-Q(1,2)), (-1,1,Q(1,4))]),
        ("unit confluent colors", [(1,1,S.Integer(1)), (2,1,S.Integer(1)), (-2,1,S.Integer(1))]),
        ("opposite unit colors", [(2,1,S.Integer(-1)), (1,1,S.Integer(1)), (-1,1,S.Integer(-1))]),
    ]
    N = 22
    rows = []
    checks = 0
    for name, spec in fixtures:
        R, before = mix_terms(spec)
        after = eliminate_terms(before)
        q = sum(s > 0 for s, p, X in spec)
        assert all(len(inds) <= q+1 for inds, cols in after)
        assert all(all(k > 0 for k in inds[1:]) for inds, cols in after)
        original = original_coeffs(spec, N)
        for n in range(1, N+1):
            assert rhs_coeff(n, before) == original[n], (name, n, "convolution")
            assert rhs_coeff(n, after) == original[n], (name, n, "elimination")
            checks += 2
        rows.append({
            "case": name,
            "inputs": [[s,p,str(X)] for s,p,X in spec],
            "rational_function": str(R),
            "terms_before_elimination": len(before),
            "terms_after_elimination": len(after),
            "maximum_output_depth": max(len(inds) for inds, cols in after),
            "permitted_depth": q+1,
            "coefficients_checked": N,
            "exact": True,
        })
    # Independently test the finite antidifference formulas, including beta=1.
    boundary_checks = 0
    for M, b in product(range(7), [S.Integer(1), -S.Integer(1), Q(1,2), Q(3,2)]):
        upper, lower = polynomial_boundaries(M, b)
        for lo, hi in [(0,1), (0,7), (2,3), (2,9), (5,10)]:
            rhs = b**hi*upper.eval(hi) + b**lo*lower.eval(lo)
            lhs = sum((b**n*n**M for n in range(lo+1, hi)), S.Integer(0))
            assert S.cancel(rhs-lhs) == 0
            boundary_checks += 1
    result = {
        "status": "passed",
        "arithmetic": "exact rational SymPy arithmetic",
        "sympy_version": S.__version__,
        "coefficient_identity_checks": checks,
        "finite_antidifference_checks": boundary_checks,
        "total_exact_checks": checks+boundary_checks,
        "cases": rows,
        "limitations": "Analytic continuation and normal differentiation are proved in the article, not certified by these finite checks. Weight fixtures use p=1 or 2; the proof covers every positive integer weight.",
    }
    dest = Path(__file__).with_name("mixed_reduction_checks.json")
    dest.write_text(json.dumps(result, indent=2)+"\n")
    print(json.dumps({k:v for k,v in result.items() if k != "cases"}, indent=2))


if __name__ == "__main__":
    main()
