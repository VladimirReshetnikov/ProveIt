#!/usr/bin/env python3
"""Exact finite checks for Fractions of Omnific Integers.

Requires Python 3.10+ and SymPy 1.14.0. This checks polynomial certificates,
examples, and finite coefficient layers, NOT full surreal or class-size proofs.
Run: python verify.py --output verification.json
"""
from __future__ import annotations

import argparse
import json
import random
from collections import Counter
from pathlib import Path
from typing import Iterable

import sympy as sp

T, U = sp.symbols('T U')
r = sp.sqrt(2)
SEED = 23092026
counts: Counter[str] = Counter()


def check(condition: bool, category: str, message: str) -> None:
    if not bool(condition):
        raise AssertionError(f'{category}: {message}')
    counts[category] += 1


def poly(expr: sp.Expr, var: sp.Symbol = T) -> sp.Poly:
    return sp.Poly(expr, var, extension=r)


def exact_zero(expr: sp.Expr, var: sp.Symbol = T) -> bool:
    return poly(sp.expand(expr), var).is_zero


def reduce_vector(vector: list[sp.Poly]) -> list[sp.Poly]:
    if vector[0].is_zero:
        raise ValueError('The denominator polynomial must be nonzero.')
    d = vector[0]
    for p in vector[1:]:
        d = sp.gcd(d, p)
    return [p.exquo(d) for p in vector]


def polynomial_bezout(vector: list[sp.Poly]) -> list[sp.Poly]:
    """Return exact coefficients for a polynomial vector whose gcd is one."""
    current = vector[0]
    weights = [poly(1)]
    for p in vector[1:]:
        s, t, d = sp.gcdex(current, p)
        weights = [s * w for w in weights] + [t]
        current = d
    if current.degree() != 0:
        raise ValueError('The vector is not unimodular over the polynomial ring.')
    return [w.exquo(current) for w in weights]


def integer_bezout(values: Iterable[int]) -> list[int]:
    def egcd(a: int, b: int) -> tuple[int, int, int]:
        old_r, new_r, old_s, new_s, old_t, new_t = abs(a), abs(b), 1, 0, 0, 1
        while new_r:
            q = old_r // new_r
            old_r, new_r = new_r, old_r - q * new_r
            old_s, new_s = new_s, old_s - q * new_s
            old_t, new_t = new_t, old_t - q * new_t
        return old_r, old_s * (-1 if a < 0 else 1), old_t * (-1 if b < 0 else 1)

    g, weights = 0, []
    for v in values:
        g, s, t = egcd(g, v)
        weights = [s * w for w in weights] + [t]
    if g != 1:
        raise ValueError('Integer residue vector is not primitive.')
    return weights


def normalize(vector: list[sp.Poly]) -> tuple[str, list[sp.Poly]]:
    constants = [p.nth(0) for p in vector]
    pivot = next((c for c in constants if c != 0), None)
    if pivot is None:
        raise ValueError('The projective residue vector is zero.')
    ratios = [sp.simplify(c / pivot) for c in constants]
    if not all(c.is_Rational is True for c in ratios):
        return 'irrational', vector
    denominator = sp.ilcm(*[sp.denom(c) for c in ratios])
    integer_vector = [int(denominator * c) for c in ratios]
    divisor = int(sp.igcd(*integer_vector))
    scale = sp.simplify(denominator / (divisor * pivot))
    return 'rational', [poly(scale * p.as_expr()) for p in vector]


def is_integer_constant(expr: sp.Expr) -> bool:
    return sp.simplify(expr).is_Integer is True


def run() -> dict[str, object]:
    rng = random.Random(SEED)
    data: list[tuple[str, list[sp.Poly]]] = []
    for index in range(40):
        size = 2 + index % 3
        intended = 'rational' if index % 2 == 0 else 'irrational'
        if intended == 'rational':
            factor = [sp.S.One, r, 1 + r][index % 3]
            constants = [factor] + [factor * rng.randint(-3, 3) for _ in range(size - 1)]
        else:
            constants = [sp.S.One, r] + [sp.Integer(rng.randint(-2, 2)) for _ in range(size - 2)]
        vector = []
        for c in constants:
            tail = sum((rng.randint(-2, 2) + rng.randint(-1, 1) * r) * T**j
                       for j in range(1, 2 + index % 3))
            vector.append(poly(c + tail))
        reduced = reduce_vector(vector)
        kind, normalized = normalize(reduced)
        check(kind == intended, 'classification', f'Unexpected class in case {index}')
        check(any(p.nth(0) != 0 for p in normalized), 'classification', 'Zero residue vector')
        # Common normalization and cancellation preserve every rational function.
        for a, b in zip(vector[1:], normalized[1:]):
            check((a * normalized[0] - b * vector[0]).is_zero,
                  'representation', 'Normalization changed a rational function')
        bezout = polynomial_bezout(normalized)
        check(sum((u * p for u, p in zip(bezout, normalized)), poly(0)) == poly(1),
              'polynomial_bezout', 'Polynomial Bezout identity failed')
        if kind == 'rational':
            residues = [int(p.nth(0)) for p in normalized]
            u = integer_bezout(residues)
            check(sum(a * b for a, b in zip(u, residues)) == 1,
                  'integer_bezout', 'Integer Bezout identity failed')
            S = sum((a * p for a, p in zip(u, normalized)), poly(0))
            lifted = [poly(a) + (poly(1) - S) * b for a, b in zip(u, bezout)]
            for v, a in zip(lifted, u):
                check(v.nth(0) == a, 'lifted_bezout', 'Lifted coefficient has wrong residue')
            check(sum((v * p for v, p in zip(lifted, normalized)), poly(0)) == poly(1),
                  'lifted_bezout', 'Lifted omnific certificate failed')
        # Test exact constant-term membership on finitely many multipliers.
        for c in [sp.Integer(-2), sp.Rational(-1, 2), sp.S.Zero, sp.S.One,
                  sp.Rational(2, 3), r, 1 + r]:
            h = poly(c + T * (1 + r + T))
            membership = all(is_integer_constant((h * p).nth(0)) for p in normalized)
            predicted = is_integer_constant(c) if kind == 'rational' else c == 0
            check(membership == predicted, 'scalar_membership', 'Scalar classification mismatch')
        data.append((kind, normalized))
        if index < 8:
            for m in range(2, 7):
                expr = sum(u.as_expr().subs(T, U**m) * p.as_expr().subs(T, U**m)
                           for u, p in zip(bezout, normalized)) - 1
                check(exact_zero(expr, U), 'scale_substitution', 'Bezout lost under substitution')

    # Table and simultaneous-denominator examples.
    examples = [
        ('rational', [poly(3), poly(2)]),
        ('irrational', [poly(1), poly(r)]),
        ('irrational', [poly(1), poly(T+r)]),
        ('rational', [poly(T), poly(1)]),
        ('rational', [poly(T), poly(r)]),
        ('rational', [poly(T+1), poly(r*T+1)]),
        ('irrational', [poly(T+1), poly(T+r)]),
        ('irrational', [poly(T), poly(1), poly(r)]),
        ('rational', [poly(1-T*T), poly(2*T), poly(1+T*T)]),
        ('irrational', [poly(1), poly(r+T), poly(T*T)]),
    ]
    for expected, vector in examples:
        kind, _ = normalize(reduce_vector(vector))
        check(kind == expected, 'examples', 'An article example was misclassified')
    _, normalized = normalize([poly(T), poly(r)])
    check(normalized[0] == poly(T/r) and normalized[1] == poly(1),
          'examples', 'sqrt(2)/T normalization mismatch')
    check(exact_zero((1+T*T/2)*(1-T*T)+(T*T/2)*(1+T*T)-1),
          'examples', 'Pythagorean Bezout certificate failed')
    check(exact_zero((1-T*T)**2+(2*T)**2-(1+T*T)**2),
          'examples', 'Pythagorean identity failed')
    check(sp.cancel((1/T) + (r-1/T) - r) == 0,
          'examples', 'Addition counterexample identity failed')
    check(sp.cancel(T*(r/T)-r) == 0,
          'examples', 'Multiplication counterexample identity failed')

    # Independent specialization and standard-part identities.
    R, Q = sp.symbols('R Q')
    interpolation = (R*T+Q)/(T+1)
    check(sp.cancel(interpolation-R-(Q-R)/(T+1)) == 0,
          'residue_identities', 'Interpolation identity failed')
    check(sp.simplify(interpolation.subs(T, 0)-Q) == 0,
          'residue_identities', 'Specialization value failed')
    check(sp.limit(interpolation, T, sp.oo) == R,
          'residue_identities', 'Ordinary rational-function limit failed')
    check(sp.cancel(T/(T+1)+1/(T+1)-1) == 0,
          'residue_identities', 'Comaximal-kernel certificate failed')

    # Truncated coefficient spaces and explicit nonextended relations.
    for m in range(2, 13):
        basis = [U**j for j in range(1, m)]
        matrix = sp.Matrix([[sp.expand(b).coeff(U, j) for b in basis]
                            for j in range(1, m)])
        check(matrix.rank() == m-1, 'defect_layers', f'Wrong truncation dimension m={m}')
        for k in range(1, m+4):
            remainder = sp.rem(U**k, U**m, U)
            check(remainder == (U**k if k < m else 0),
                  'defect_layers', 'Wrong monomial quotient representative')
        check(exact_zero(r*U**m*U + U**m*(-r*U), U),
              'nonflat_relation', 'New relation does not vanish')
        check(sp.rem(U, U**m, U) == U,
              'nonflat_relation', 'New relation erroneously belongs to old image')
        for k in range(1, 5):
            monomial = r*U**k
            check(exact_zero(monomial**m-r**m*(U**m)**k, U),
                  'integrality_equations', 'Integral monomial equation failed')

    # Finite linear independence input in the nonrational-series example.
    N = sp.symbols('N')
    for degree in range(1, 9):
        falling = [sp.prod(N-j for j in range(k)) for k in range(degree+1)]
        matrix = sp.Matrix([[sp.expand(f).coeff(N, j) for f in falling]
                            for j in range(degree+1)])
        check(matrix.det() == 1, 'falling_factorials', 'Falling factorials not independent')

    return {
        'status': 'PASS',
        'python_scope': 'exact finite symbolic checks, not proof-assistant verification',
        'sympy_version': sp.__version__,
        'seed': SEED,
        'polynomial_vector_cases': len(data),
        'assertions_passed': sum(counts.values()),
        'by_category': dict(sorted(counts.items())),
        'not_checked_by_computation': [
            'full surreal normal-form constructions and proper-class arguments',
            'universal quantification over arbitrary infinite-support representations',
            'theorem novelty or historical priority',
            'Lean formalization or repository build',
            'Tor and flatness beyond the displayed finite relation identities',
        ],
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, default=Path(__file__).with_name('verification.json'))
    args = parser.parse_args()
    report = run()
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(report, indent=2) + '\n', encoding='utf-8')
    print(json.dumps(report, indent=2))


if __name__ == '__main__':
    main()
