#!/usr/bin/env python3
"""Exact finite certificates for 'Finite Models and Real Degenerations ...'.

Requires Python 3.10+ and SymPy. No network access or floating-point arithmetic
is used. These tests check finite identities and examples, not the general
ordered-field or mixed-volume theorems in the manuscript.

Run: python verify.py --output verification_results.json
"""
from __future__ import annotations

import argparse
from collections import Counter
from itertools import combinations, product
import json
from pathlib import Path
import platform
import random
from typing import Iterator, Sequence

import sympy as sp

LINES = {
    (0, 1, 2), (0, 3, 4), (0, 5, 6), (1, 3, 5),
    (1, 4, 6), (2, 3, 6), (2, 4, 5),
}
BASES = [b for b in combinations(range(7), 3) if b not in LINES]


def require(condition: bool, message: str) -> None:
    if not condition:
        raise AssertionError(message)


def compositions(total: int, length: int) -> Iterator[tuple[int, ...]]:
    if length == 1:
        yield (total,)
        return
    for first in range(total + 1):
        for tail in compositions(total - first, length - 1):
            yield (first,) + tail


def gf2_rank(labels: Sequence[int]) -> int:
    """Rank of the binary columns represented by integers 1,...,7."""
    pivots: dict[int, int] = {}
    for label in labels:
        v = label
        while v:
            bit = v.bit_length() - 1
            if bit in pivots:
                v ^= pivots[bit]
            else:
                pivots[bit] = v
                break
    return len(pivots)


def exponent_valuation(coefficient: sp.Expr, t: sp.Symbol) -> int:
    p = sp.Poly(coefficient, t)
    require(not p.is_zero, 'A coefficient unexpectedly vanished.')
    return min(m[0] for m, c in p.terms() if c != 0)


def verify_fano() -> dict:
    x = sp.symbols('x1:8')
    t, z = sp.symbols('t z')
    s = sum(x)
    e2 = sum(x[i] * x[j] for i, j in combinations(range(7), 2))
    b = sum(sp.prod(x[i] for i in base) for base in BASES)
    f = sp.Poly(sp.expand(b.xreplace({xi: xi + t * s for xi in x})), *x)
    expected = sp.expand(b + 4 * t * s * e2 + (12 * t**2 + 28 * t**3) * s**3)
    require(sp.expand(f.as_expr() - expected) == 0, 'Fano expansion failed.')
    require(len(BASES) == 28 and len(LINES) == 7, 'Wrong Fano counts.')
    for triple in combinations(range(7), 3):
        require((gf2_rank([i + 1 for i in triple]) == 2) == (triple in LINES),
                f'Binary Fano incidence failed: {triple}')

    h: dict[tuple[int, ...], int] = {}
    rows = []
    classes: Counter[str] = Counter()
    expected_coefficients = {
        'basis': 1 + 12*t + 72*t**2 + 168*t**3,
        'line': 12*t + 72*t**2 + 168*t**3,
        'double': 4*t + 36*t**2 + 84*t**3,
        'cube': 12*t**2 + 28*t**3,
    }
    for a in compositions(3, 7):
        coeff = sp.expand(f.coeff_monomial(a))
        support = tuple(i for i, ai in enumerate(a) if ai)
        kind = ('cube' if len(support) == 1 else 'double' if len(support) == 2
                else 'line' if support in LINES else 'basis')
        require(sp.expand(coeff - expected_coefficients[kind]) == 0,
                f'Wrong coefficient at {a}.')
        require(all(c > 0 for _, c in sp.Poly(coeff, t).terms()),
                f'Nonpositive coefficient at {a}.')
        val = exponent_valuation(coeff, t)
        h[a] = val
        require(val == 3 - gf2_rank([i + 1 for i in support]),
                f'Rank-deficiency formula failed at {a}.')
        classes[kind] += 1
        rows.append({'alpha': a, 'type': kind, 'coefficient': str(coeff),
                     'valuation_in_units_of_gamma': val})

    # Exhaustive symmetric M-exchange: every ordered pair and every excess index.
    obligations = 0
    for a in h:
        for c in h:
            for i in range(7):
                if a[i] <= c[i]:
                    continue
                obligations += 1
                witnesses = []
                for j in range(7):
                    if a[j] >= c[j]:
                        continue
                    aa, cc = list(a), list(c)
                    aa[i] -= 1; aa[j] += 1
                    cc[i] += 1; cc[j] -= 1
                    if h[a] + h[c] >= h[tuple(aa)] + h[tuple(cc)]:
                        witnesses.append(j)
                require(bool(witnesses), f'M-exchange failed at {a}, {c}, {i}.')

    hs = [sp.hessian(sp.diff(b, xi), x) for xi in x]
    J = sp.ones(7)
    I = sp.eye(7)
    require(sum(hs, sp.zeros(7)) == 4 * (J - I), 'Hessian sum identity failed.')
    A = I + t * J
    target_charpoly = (z + 4*t)**3 * (z + 2 + 4*t)**2 * (z**2 - (4 + 20*t)*z - 96*t**2)
    for j in range(7):
        middle = hs[j] + 4*t*(J-I)
        require(sp.expand(middle.charpoly(z).as_expr() - target_charpoly) == 0,
                f'Hessian spectral identity failed for j={j}.')
        actual = sp.hessian(sp.diff(expected, x[j]), x)
        require((actual - A.T * middle * A).applyfunc(sp.expand) == sp.zeros(7),
                f'Chain-rule congruence failed for j={j}.')
    fano_det = sp.Matrix.hstack(sp.Matrix([1,1,0]), sp.Matrix([1,0,1]),
                               sp.Matrix([0,1,1])).det()
    require(fano_det == -2, 'Fano characteristic-zero obstruction failed.')
    return {
        'bases': len(BASES), 'lines': len(LINES), 'monomials': len(h),
        'coefficient_classes': dict(classes),
        'valuation_histogram': dict(sorted(Counter(h.values()).items())),
        'ordered_pairs_checked': len(h)**2, 'M_exchange_obligations': obligations,
        'all_M_exchange_obligations_pass': True,
        'all_seven_Hessian_congruences_pass': True,
        'middle_Hessian_characteristic_polynomial': str(target_charpoly),
        'Fano_obstruction_determinant': int(fano_det),
        'coefficient_table': rows,
    }


def rational_sandwich(vertices: Sequence[Sequence[int | sp.Rational]]) -> dict:
    """Construct and verify the manuscript's maximum-minor certificate.

    Input is a nonempty finite rational point configuration. The first point
    is the anchor; it need not be an extreme point for this certificate.
    """
    if not vertices or not vertices[0]:
        raise ValueError('A nonempty point configuration is required.')
    d = len(vertices[0])
    if any(len(v) != d for v in vertices):
        raise ValueError('Point dimensions must agree.')
    pts = [sp.Matrix([sp.Rational(a) for a in v]) for v in vertices]
    p0 = pts[0]
    differences = [p - p0 for p in pts]
    V = sp.Matrix.hstack(*differences)
    r = V.rank()
    if r == 0:
        return {'dimension': 0, 'point_count': len(pts), 'passed': True}
    # Find a row projection injective on the r-dimensional column span.
    rows = next(rows for rows in combinations(range(d), r)
                if V[list(rows), :].rank() == r)
    candidates = [(abs(V[list(rows), list(cols)].det()), cols)
                  for cols in combinations(range(len(pts)), r)]
    maximum, chosen = max(candidates, key=lambda pair: pair[0])
    require(maximum > 0, 'Selected determinant must be nonzero.')
    B = V[:, list(chosen)]
    C = B[list(rows), :].inv() * V[list(rows), :]
    require(B * C == V, 'Projection reconstruction failed.')
    require(all(abs(c) <= 1 for c in C), 'Cramer coordinate bound failed.')
    delta = sp.Rational(1, r*(r+1))
    centroid = sp.ones(r, 1) / (r+1)
    require(all(abs(C[i,j] - centroid[i]) <= 2
                for i in range(r) for j in range(C.cols)), 'Outer bound failed.')
    for corner in product([-1,1], repeat=r):
        u = centroid + delta * sp.Matrix(corner)
        require(all(ui >= 0 for ui in u) and sum(u) <= 1,
                'An inner parallelotope corner escaped the selected simplex.')
    return {'dimension': r, 'point_count': len(pts), 'rows': rows,
            'selected_indices': chosen, 'selected_absolute_minor': str(maximum),
            'inner_factor': str(delta), 'outer_factor': 2, 'passed': True}


def verify_sandwiches() -> dict:
    rng = random.Random(20260930)
    certificates = []
    for d in range(1, 5):
        for _ in range(5):
            n = d + 4
            vertices = [[rng.randint(-6,6) for _ in range(d)] for _ in range(n)]
            certificates.append(rational_sandwich(vertices))
    certificates.append(rational_sandwich([[1,2,3],[1,2,3]]))
    certificates.append(rational_sandwich([[0,0,0],[1,2,3],[-2,-4,-6],[3,6,9]]))
    certificates.append(rational_sandwich([[0,0,0],[1,0,1],[0,1,1],[2,3,5],[-1,2,1]]))
    return {'seed': 20260930, 'examples': len(certificates),
            'all_pass': True, 'certificates': certificates}


def verify_quadratic_and_boxes() -> dict:
    x = sp.symbols('y1:5')
    t = sp.symbols('t')
    s = sum(x)
    e2 = sum(x[i]*x[j] for i,j in combinations(range(4),2))
    regularized = sp.expand(e2.xreplace({xi: xi+t*s for xi in x}))
    require(sp.expand(regularized-e2-(3*t+6*t**2)*s**2) == 0,
            'Quadratic regularization failed.')
    A = sp.eye(4)+t*sp.ones(4)
    require(sp.hessian(regularized,x) ==
            (A.T*(sp.ones(4)-sp.eye(4))*A).applyfunc(sp.expand),
            'Quadratic Hessian identity failed.')
    # Four thin parallelograms P_i = [0,(1,i)] + [0,(0,t)].
    zpoly = t*sum(xi**2 for xi in x)
    zpoly += sum((j-i+2*t)*x[i]*x[j] for i,j in combinations(range(4),2))
    hp = {a: exponent_valuation(sp.Poly(regularized,*x).coeff_monomial(a),t)
          for a in compositions(2,4)}
    hz = {a: exponent_valuation(sp.Poly(zpoly,*x).coeff_monomial(a),t)
          for a in compositions(2,4)}
    require(hp == hz, 'Quadratic valuation realization failed.')
    signs = [a-b+c for a,b,c in product([-1,1],repeat=3)]
    require(0 not in signs, 'Odd-sign Pluecker contradiction failed.')
    X,Y,u,v = sp.symbols('X Y u v')
    box_polynomial = sp.expand((X+v*Y)*(u*X+Y))
    require(sp.expand(box_polynomial - (u*X**2+(1+u*v)*X*Y+v*Y**2)) == 0,
            'Box polynomial failed.')
    return {'quadratic_regularization': str(regularized),
            'thin_parallelotope_polynomial': str(zpoly),
            'identical_quadratic_valuation_profiles': True,
            'quadratic_profile_size': len(hp),
            'possible_signed_Pluecker_sums': sorted(set(signs)),
            'box_polynomial': str(box_polynomial)}


def rational_function_valuation(expression: sp.Expr, t: sp.Symbol) -> int | float:
    expression = sp.cancel(expression)
    if expression == 0:
        return float('inf')
    numerator, denominator = sp.fraction(expression)
    return exponent_valuation(numerator, t) - exponent_valuation(denominator, t)


def rank_two_matrix(weights: dict[tuple[int, int], int], n: int,
                    t: sp.Symbol) -> sp.Matrix:
    """Realize a finite integer-valued rank-two tropical Pluecker vector.

    The manuscript proves the same construction for arbitrary ordered value
    groups; this executable specialization uses Laurent polynomials in t.
    """
    def w(i: int, j: int) -> int:
        return weights[tuple(sorted((i, j)))]
    for a,b,c,d in combinations(range(n), 4):
        sums = [w(a,b)+w(c,d), w(a,c)+w(b,d), w(a,d)+w(b,c)]
        require(sums.count(min(sums)) >= 2, 'Four-point condition failed.')
    if n == 2:
        return sp.Matrix([[0, t**w(0,1)], [1, 0]])
    indices = list(range(1, n))
    u = {(i,j): w(i,j)-w(0,i)-w(0,j) for i,j in combinations(indices, 2)}
    def uv(i: int, j: int) -> int | float:
        return float('inf') if i == j else u[tuple(sorted((i,j)))]
    for i,j,k in combinations(indices, 3):
        vals = [uv(i,j),uv(i,k),uv(j,k)]
        require(vals.count(min(vals)) >= 2, 'Ultrametric condition failed.')
    levels = sorted(set(u.values()))
    z = {}
    for i in indices:
        z[i] = sum(min(j for j in indices if uv(i,j) > level) * t**level
                   for level in levels)
    cols = [sp.Matrix([0,1])]
    for i in indices:
        ci = t**w(0,i)
        cols.append(sp.Matrix([ci, sp.expand(ci*z[i])]))
    A = sp.Matrix.hstack(*cols)
    for i,j in combinations(range(n),2):
        require(rational_function_valuation(A[:,[i,j]].det(),t) == w(i,j),
                f'Rank-two realization failed at {i},{j}.')
    return A


def verify_rank_two() -> dict:
    rng = random.Random(20260930)
    t = sp.symbols('t')
    records = []
    total_minors = 0
    for m in range(1, 6):
        for trial in range(3):
            # Generate a full-dimensional parallelogram profile, then discard
            # its matrix and reconstruct it from its polarized weights only.
            cols = []
            for i in range(m):
                a,b,c = [rng.randint(-3,4) for _ in range(3)]
                cols.extend([sp.Matrix([t**a,(i+1)*t**b]), sp.Matrix([0,t**c])])
            source = sp.Matrix.hstack(*cols)
            h = {}
            for i in range(m):
                for j in range(i,m):
                    pairs = ([(2*i,2*i+1)] if i == j else
                             [(a,b) for a in [2*i,2*i+1] for b in [2*j,2*j+1]])
                    h[(i,j)] = min(rational_function_valuation(source[:,[a,b]].det(),t)
                                   for a,b in pairs)
                    require(h[(i,j)] != float('inf'), 'Profile must be finite.')
            weights = {(a,b): h[tuple(sorted((a//2,b//2)))]
                       for a,b in combinations(range(2*m),2)}
            result = rank_two_matrix(weights, 2*m, t)
            count = len(weights)
            total_minors += count
            records.append({'m': m, 'trial': trial, 'columns': result.cols,
                            'all_prescribed_minor_values_verified': True,
                            'checked_minors': count,
                            'profile': {f'{i+1},{j+1}': int(v) for (i,j),v in h.items()}})
    return {'seed': 20260930, 'reconstructions': len(records),
            'exact_minor_checks': total_minors, 'all_pass': True,
            'records': records}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, default=Path('verification_results.json'))
    args = parser.parse_args()
    results = {'status': 'all exact checks passed',
               'python_version': platform.python_version(),
               'sympy_version': sp.__version__,
               'scope': 'Finite certificates only; not a formal proof of general theorems.',
               'fano': verify_fano(),
               'sandwich': verify_sandwiches(),
               'examples': verify_quadratic_and_boxes(),
               'rank_two': verify_rank_two()}
    args.output.write_text(json.dumps(results, indent=2)+'\n', encoding='utf-8')
    print(results['status'])
    print('Fano monomials:', results['fano']['monomials'])
    print('M-exchange obligations:', results['fano']['M_exchange_obligations'])
    print('Hessian congruences: 7 of 7 exact')
    print('Rational sandwich configurations:', results['sandwich']['examples'])
    print('Quadratic reconstructions:', results['rank_two']['reconstructions'])
    print('Reconstructed maximal minors:', results['rank_two']['exact_minor_checks'])
    print('Results:', args.output.resolve())


if __name__ == '__main__':
    main()
