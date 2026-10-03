#!/usr/bin/env python3
"""Exact finite checks for Finite-Scale Geometry of Surreal Liftings.

Python 3.10+, standard library only. Coefficients are fractions.Fraction.
Finite series are stored as {p: coefficient vector}, representing epsilon**p,
where epsilon is positive infinitesimal. No floating-point tests or general
surreal arithmetic are used. These finite checks supplement the proofs; they
are not a proof assistant or a decision procedure for arbitrary normal forms.

Run from any directory: python3 code/verify.py
Outputs are written to the sibling data/ directory.
"""
from __future__ import annotations
from fractions import Fraction as Q
from itertools import combinations
from pathlib import Path
import json
import random

Vector = list[Q]
Matrix = list[Vector]
Series = dict[int, Vector]


def dot(a: Vector, b: Vector) -> Q:
    if len(a) != len(b):
        raise ValueError('Dimension mismatch')
    return sum((x * y for x, y in zip(a, b)), Q(0))


def rank(rows: Matrix) -> int:
    if not rows:
        return 0
    a = [list(map(Q, row)) for row in rows]
    n = len(a[0])
    if any(len(row) != n for row in a):
        raise ValueError('Ragged matrix')
    r = 0
    for j in range(n):
        k = next((k for k in range(r, len(a)) if a[k][j]), None)
        if k is None:
            continue
        a[r], a[k] = a[k], a[r]
        pivot = a[r][j]
        a[r] = [v / pivot for v in a[r]]
        for k in range(r + 1, len(a)):
            f = a[k][j]
            if f:
                a[k] = [u - f * v for u, v in zip(a[k], a[r])]
        r += 1
        if r == len(a):
            break
    return r


def solve(a: Matrix, b: Vector) -> Vector:
    n = len(a)
    if len(b) != n or any(len(row) != n for row in a):
        raise ValueError('Expected square linear system')
    aug = [list(map(Q, row)) + [Q(v)] for row, v in zip(a, b)]
    for j in range(n):
        k = next((k for k in range(j, n) if aug[k][j]), None)
        if k is None:
            raise ValueError('Singular system')
        aug[j], aug[k] = aug[k], aug[j]
        f = aug[j][j]
        aug[j] = [x / f for x in aug[j]]
        for k in range(n):
            if k != j:
                f = aug[k][j]
                aug[k] = [u - f * v for u, v in zip(aug[k], aug[j])]
    return [row[-1] for row in aug]


def determinant(a: Matrix) -> Q:
    if not a:
        return Q(1)
    n = len(a)
    if any(len(row) != n for row in a):
        raise ValueError('Expected square matrix')
    b = [list(map(Q, row)) for row in a]
    out = Q(1)
    for j in range(n):
        k = next((k for k in range(j, n) if b[k][j]), None)
        if k is None:
            return Q(0)
        if k != j:
            b[j], b[k] = b[k], b[j]
            out = -out
        p = b[j][j]
        out *= p
        for k in range(j + 1, n):
            f = b[k][j] / p
            for z in range(j + 1, n):
                b[k][z] -= f * b[j][z]
    return out


def augmented(a: Matrix) -> Matrix:
    return [[Q(1)] + list(map(Q, p)) for p in a]


def affine_bases(a: Matrix) -> list[tuple[int, ...]]:
    u = augmented(a)
    d1 = len(u[0])
    return [b for b in combinations(range(len(a)), d1)
            if determinant([u[i] for i in b])]


def slack_form(a: Matrix, b: tuple[int, ...], i: int) -> Vector:
    u = augmented(a)
    mat = [[u[j][k] for j in b] for k in range(len(b))]
    lam = solve(mat, u[i])
    c = [Q(0)] * len(a)
    c[i] = Q(1)
    for j, v in zip(b, lam):
        c[j] -= v
    return c


def minor_forms(a: Matrix) -> list[Vector]:
    u = augmented(a)
    n, r = len(a), len(u[0])
    out = []
    for inds in combinations(range(n), r + 1):
        c = [Q(0)] * n
        for j, idx in enumerate(inds):
            mat = [[u[k][z] for k in inds if k != idx] for z in range(r)]
            c[idx] = Q((-1) ** (r + j)) * determinant(mat)
        out.append(c)
    return out


def linear_series(c: Vector, s: Series) -> dict[int, Q]:
    return {p: v for p in sorted(s) if (v := dot(c, s[p]))}


def lead(f: dict[int, Q]) -> tuple[int, Q] | None:
    if not f:
        return None
    p = min(f)
    return p, f[p]


def sign(x: Q) -> int:
    return (x > 0) - (x < 0)


def series_sign(c: Vector, s: Series) -> int:
    z = lead(linear_series(c, s))
    return 0 if z is None else sign(z[1])


def evaluate(s: Series, t: Q) -> Vector:
    if not s:
        raise ValueError('Series must carry its dimension, even when zero')
    n = len(next(iter(s.values())))
    return [sum((v[i] * t ** p for p, v in s.items()), Q(0)) for i in range(n)]


def gauge(a: Matrix, s: Series, b: tuple[int, ...]) -> Series:
    forms = [slack_form(a, b, i) for i in range(len(a))]
    return {p: [dot(c, row) for c in forms] for p, row in s.items()}


def compress(g: Series) -> Series:
    pivots: Series = {}
    rows: Matrix = []
    for p in sorted(g):
        if rank(rows + [g[p]]) > len(rows):
            rows.append(g[p])
            pivots[p] = g[p][:]
    return pivots


def polynomial_model(a: Matrix, s: Series, b: tuple[int, ...],
                     preserve_shadow: bool = True) -> tuple[Series, Series]:
    g = gauge(a, s, b)
    piv = compress(g)
    n = len(a)
    if preserve_shadow:
        if any(p < 0 and any(v) for p, v in s.items()):
            raise ValueError('Finite heights are required for a real shadow')
        h0 = s.get(0, [Q(0)] * n)
        g0 = g.get(0, [Q(0)] * n)
        # Start with the standard part of the affine gauge component.
        out = {0: [x - y for x, y in zip(h0, g0)]}
        shift = 0 if 0 in piv else 1
    else:
        out = {0: [Q(0)] * n}
        shift = 0
    for j, p in enumerate(piv):
        k = j + shift
        out[k] = [x + y for x, y in zip(out.get(k, [Q(0)] * n), piv[p])]
    return out, piv


def threshold(forms: list[Vector], s: Series) -> Q:
    eta = Q(1)
    for c in forms:
        f = linear_series(c, s)
        if not f:
            continue
        k = min(f)
        tail = sum((abs(v) for j, v in f.items() if j > k), Q(0))
        if tail:
            eta = min(eta, abs(f[k]) / (2 * tail))
    return eta


def lower_cells(a: Matrix, s: Series) -> list[list[int]]:
    cells = set()
    for b in affine_bases(a):
        signs = [series_sign(slack_form(a, b, i), s) for i in range(len(a))]
        if min(signs) >= 0:
            cells.add(tuple(i + 1 for i, sig in enumerate(signs) if sig == 0))
    return [list(c) for c in sorted(cells)]


def serial(s: Series) -> dict[str, list[str]]:
    return {str(p): [str(x) for x in v] for p, v in sorted(s.items())}


def check_case(a: Matrix, s: Series, rng: random.Random,
               preserve_shadow: bool = True) -> dict:
    n, d = len(a), len(a[0])
    bases = affine_bases(a)
    if not bases:
        raise ValueError('Base configuration must affinely span')
    b = bases[0]
    g = gauge(a, s, b)
    model, piv = polynomial_model(a, s, b, preserve_shadow)
    forms = [slack_form(a, bb, i) for bb in bases for i in range(n)]
    minors = minor_forms(a)
    forms += minors
    u = augmented(a)
    for c in forms:
        assert all(sum((c[i] * u[i][j] for i in range(n)), Q(0)) == 0
                   for j in range(d + 1))
    assert len(piv) == rank(list(g.values())) <= n - d - 1
    for c in forms:
        assert lead(linear_series(c, s)) == lead(linear_series(c, piv))
        assert series_sign(c, s) == series_sign(c, model)
    for _ in range(60):
        c = [Q(0)] * n
        for i in range(n):
            k = Q(rng.randint(-4, 4), rng.randint(1, 5))
            f = slack_form(a, b, i)
            c = [x + k * y for x, y in zip(c, f)]
        assert lead(linear_series(c, s)) == lead(linear_series(c, piv))
        assert series_sign(c, s) == series_sign(c, model)
    eta = threshold(forms, model)
    t0 = eta / 2
    w = evaluate(model, t0)
    for c in forms:
        assert sign(dot(c, w)) == series_sign(c, s)
    assert lower_cells(a, s) == lower_cells(a, model) == lower_cells(a, {0: w})
    if preserve_shadow:
        h0 = s.get(0, [Q(0)] * n)
        assert model[0] == h0
        for lam in (Q(1, 1000), Q(1, 7), Q(1, 2), Q(1)):
            v = [(1 - lam) * x + lam * y for x, y in zip(h0, w)]
            assert all(sign(dot(c, v)) == series_sign(c, s) for c in forms)
    return {
        'base': [[str(x) for x in p] for p in a],
        'affine_basis_labels': [i + 1 for i in b],
        'input_series': serial(s), 'pivot_powers': list(piv),
        'compressed_series': serial(piv), 'polynomial_model': serial(model),
        'm': len(piv), 'q': n - d - 1,
        'number_of_slack_and_minor_tests': len(forms),
        'extra_dependence_tests': 60,
        'eta': str(eta), 'sample_t': str(t0),
        'real_heights': [str(x) for x in w],
        'lower_maximal_cells': lower_cells(a, s),
        'augmented_minor_signs': [series_sign(c, s) for c in minors]
    }


def main() -> None:
    rng = random.Random(20260930)
    named = {}
    square = [[Q(0), Q(0)], [Q(1), Q(0)], [Q(0), Q(1)], [Q(1), Q(1)]]
    for eps_sign in (1, -1):
        s = {0: [Q(1)] * 4, 1: [Q(0), Q(0), Q(0), Q(eps_sign)]}
        named['square_plus' if eps_sign == 1 else 'square_minus'] = check_case(square, s, rng)
    triangle = square[:3]
    named['zero_dependence_dimension'] = check_case(
        triangle, {0: list(map(Q, [2, -1, 3])),
                   1: list(map(Q, [1, 4, 2]))}, rng)
    named['affine_heights_with_infinitesimal_tilt'] = check_case(
        square, {0: list(map(Q, [1, 2, 3, 4])),
                 1: list(map(Q, [0, 1, 2, 3]))}, rng)
    named['rank_one_nonzero_shadow'] = check_case(
        square, {0: list(map(Q, [0, 0, 0, 1])),
                 1: list(map(Q, [0, 0, 0, 2]))}, rng)
    assert named['zero_dependence_dimension']['m'] == 0
    assert named['affine_heights_with_infinitesimal_tilt']['m'] == 0
    assert named['rank_one_nonzero_shadow']['m'] == 1
    line = [[Q(i)] for i in range(5)]
    coeffs = {1: [1, 1, 0], 2: [2, 2, 0], 5: [0, 1, 1],
              6: [1, -2, -3], 9: [1, 0, 1]}
    s = {p: list(map(Q, [0, 0] + row)) for p, row in coeffs.items()}
    named['three_scale_cancellation'] = check_case(line, s, rng)
    sharp = []
    for q in range(1, 7):
        a = [[Q(i)] for i in range(q + 2)]
        s = {i + 1: [Q(int(j == i + 2)) for j in range(q + 2)] for i in range(q)}
        info = check_case(a, s, rng)
        assert info['m'] == q
        assert max(map(int, info['polynomial_model'])) == q
        sharp.append({'q': q, 'm': info['m'], 'shadow_preserving_degree': q})
    random_results = []
    for k in range(40):
        pts = {(0, 0), (1, 0), (0, 1)}
        while len(pts) < 6:
            pts.add((rng.randint(-3, 3), rng.randint(-3, 3)))
        a = [list(map(Q, p)) for p in sorted(pts)]
        s = {p: [Q(rng.randint(-3, 3), rng.randint(1, 4)) for _ in a]
             for p in (0, 1, 2, 4, 7)}
        info = check_case(a, s, rng)
        random_results.append({k: info[k] for k in
                               ('m', 'q', 'number_of_slack_and_minor_tests', 'eta')})
    unbounded = {p - 20: row for p, row in s.items()}
    named['unbounded_gauge'] = check_case(a, unbounded, rng, False)
    # Prior-draft validity-set counterexample: 1 - 3t + 2t^2.
    validity = {str(t): sign(1 - 3 * t + 2 * t * t)
                for t in (Q(1, 4), Q(1, 2), Q(3, 4), Q(1), Q(2))}
    assert list(validity.values()) == [1, 0, -1, 0, 1]
    data = {'seed': 20260930, 'named_cases': named, 'sharpness_family': sharp,
            'random_cases': random_results, 'validity_counterexample': validity,
            'status': 'all exact checks passed',
            'scope': 'finite rational-coefficient Laurent polynomials; not a Lean proof'}
    out = Path(__file__).resolve().parents[1] / 'data'
    out.mkdir(exist_ok=True)
    (out / 'certificates.json').write_text(json.dumps(data, indent=2) + '\n', encoding='utf-8')
    report = ['ALL EXACT CHECKS PASSED',
              '7 named examples, 6 sharpness examples, 40 randomized examples.',
              '60 additional rational dependence vectors per example.',
              'All affine-basis slacks and all augmented maximal minors checked.',
              'Leading terms, signs, zero tests, lower maximal cells, rational',
              'specializations, and bounded-case linear homotopies agree.',
              'Validity-set counterexample signs: ' + str(validity),
              'Three-scale pivot powers: ' + str(named['three_scale_cancellation']['pivot_powers']),
              'This is finite exact testing, not formal verification of universal claims.']
    text = '\n'.join(report) + '\n'
    (out / 'verification_report.txt').write_text(text, encoding='utf-8')
    print(text, end='')


if __name__ == '__main__':
    main()
