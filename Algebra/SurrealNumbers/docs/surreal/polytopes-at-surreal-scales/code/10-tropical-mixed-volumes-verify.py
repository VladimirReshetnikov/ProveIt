#!/usr/bin/env python3
"""Exact checks accompanying article.tex; these do not replace its general proofs.

Requires Python 3.10+ and SymPy 1.12+. Run from any directory:
    python verify.py
Outputs verification.json and fano_coefficients.csv beside this script.
No network access, floating-point tests, or random choices are used.
"""
from __future__ import annotations

import csv
import json
from collections import Counter
from itertools import combinations
from pathlib import Path
from typing import Iterator

import sympy as sp


def compositions(total: int, parts: int) -> Iterator[tuple[int, ...]]:
    if parts == 1:
        yield (total,)
    else:
        for head in range(total + 1):
            for tail in compositions(total - head, parts - 1):
                yield (head,) + tail


def gf2_rank(vectors: list[int]) -> int:
    pivots: dict[int, int] = {}
    for v in vectors:
        while v:
            p = v.bit_length() - 1
            if p not in pivots:
                pivots[p] = v
                break
            v ^= pivots[p]
    return len(pivots)


def shifted(alpha: tuple[int, ...], i: int, j: int) -> tuple[int, ...]:
    result = list(alpha)
    result[i] -= 1
    result[j] += 1
    return tuple(result)


def main() -> None:
    folder = Path(__file__).resolve().parent
    t, z = sp.symbols('t z')
    x = sp.symbols('x1:8')
    # Labels: e1,e2,e3,e1+e2,e1+e3,e2+e3,e1+e2+e3.
    binary = [1, 2, 4, 3, 5, 6, 7]
    triples = list(combinations(range(7), 3))
    lines = {B for B in triples if gf2_rank([binary[i] for i in B]) == 2}
    expected_lines = {tuple(i - 1 for i in B) for B in
                      [(1, 2, 4), (1, 3, 5), (2, 3, 6), (1, 6, 7),
                       (2, 5, 7), (3, 4, 7), (4, 5, 6)]}
    assert lines == expected_lines
    bases = [B for B in triples if B not in lines]
    assert len(bases) == 28
    H = sum(sp.prod(x[i] for i in B) for B in bases)
    S = sum(x)
    e2 = sum(x[i] * x[j] for i, j in combinations(range(7), 2))
    F = sp.expand(H.xreplace({xi: xi + t * S for xi in x}))
    assert sp.expand(F - H - 4 * t * S * e2 - (12 * t**2 + 28 * t**3) * S**3) == 0
    poly = sp.Poly(F, *x)
    alphas = list(compositions(3, 7))
    assert len(alphas) == 84
    q: dict[tuple[int, ...], int] = {}
    rows = []
    types = Counter()
    for alpha in alphas:
        support = [i for i, a in enumerate(alpha) if a]
        if len(support) == 3 and tuple(support) not in lines:
            kind, expected = 'basis triple', 1 + 12*t + 72*t**2 + 168*t**3
        elif len(support) == 3:
            kind, expected = 'Fano line triple', 12*t + 72*t**2 + 168*t**3
        elif len(support) == 2:
            kind, expected = 'repeated pair', 4*t + 36*t**2 + 84*t**3
        else:
            kind, expected = 'pure cube', 12*t**2 + 28*t**3
        coeff = poly.coeff_monomial(alpha)
        assert sp.expand(coeff - expected) == 0
        coeff_t = sp.Poly(coeff, t)
        assert all(c > 0 for c in coeff_t.coeffs())
        valuation = min(monomial[0] for monomial, c in coeff_t.terms() if c)
        expected_q = 3 - gf2_rank([binary[i] for i in support])
        assert valuation == expected_q
        q[alpha] = valuation
        types[kind] += 1
        rows.append([*alpha, kind, str(coeff), valuation])
    with (folder / 'fano_coefficients.csv').open('w', newline='', encoding='utf-8') as f:
        writer = csv.writer(f)
        writer.writerow([*(f'alpha{i}' for i in range(1, 8)), 'type', 'coefficient', 't_order'])
        writer.writerows(rows)

    # The M-convex exchange condition, with the min-plus sign convention.
    exchange_obligations = 0
    for alpha in alphas:
        for beta in alphas:
            for i in range(7):
                if alpha[i] > beta[i]:
                    exchange_obligations += 1
                    candidates = [j for j in range(7) if alpha[j] < beta[j]]
                    assert any(q[alpha] + q[beta] >=
                               q[shifted(alpha, i, j)] + q[shifted(beta, j, i)]
                               for j in candidates), (alpha, beta, i)

    # All 7 * C(7,2) tropical Alexandrov--Fenchel comparisons for a cubic.
    af_checks = 0
    for k in range(7):
        for i, j in combinations(range(7), 2):
            a, b, c = [0]*7, [0]*7, [0]*7
            for v in (a, b, c):
                v[k] += 1
            a[i] += 1; a[j] += 1
            b[i] += 2; c[j] += 2
            assert 2*q[tuple(a)] <= q[tuple(b)] + q[tuple(c)]
            af_checks += 1

    # Canonical polarization: 3 copies of each of the 7 colors.
    E = list(range(21))
    polarized = {}
    for B in combinations(E, 3):
        alpha = [0] * 7
        for a in B:
            alpha[a // 3] += 1
        polarized[B] = q[tuple(alpha)]
    assert len(polarized) == 1330
    plucker_checks = 0
    for common in E:
        for a, b, c, d in combinations([e for e in E if e != common], 4):
            def p(i: int, j: int) -> int:
                return polarized[tuple(sorted((common, i, j)))]
            values = [p(a,b)+p(c,d), p(a,c)+p(b,d), p(a,d)+p(b,c)]
            assert values.count(min(values)) >= 2
            plucker_checks += 1
    assert plucker_checks == 101745

    # Symbolic Hessian identities and the exact inertia certificate.
    J, I = sp.ones(7), sp.eye(7)
    L = I + t*J
    M = [sp.hessian(sp.diff(H, x[k]), x) for k in range(7)]
    assert sum(M, sp.zeros(7)) == 4*(J-I)
    for k in range(7):
        lhs = sp.hessian(sp.diff(F, x[k]), x)
        rhs = L.T*(M[k]+4*t*(J-I))*L
        assert all(sp.expand(v) == 0 for v in lhs-rhs)
        pairs = [tuple(i for i in line if i != k) for line in lines if k in line]
        assert len(pairs) == 3
        N = M[k] + 4*t*(J-I)
        for a, b in pairs:
            v = sp.eye(7)[:,a] - sp.eye(7)[:,b]
            assert N*v == -4*t*v
        pair_vectors = [sp.eye(7)[:,a] + sp.eye(7)[:,b] for a,b in pairs]
        for j in (1,2):
            v = pair_vectors[0]-pair_vectors[j]
            assert N*v == (-2-4*t)*v
    charpoly = sp.factor((M[0]+4*t*(J-I)).charpoly(z).as_expr())
    expected_charpoly = (z+4*t)**3*(z+2+4*t)**2*(z**2-(4+20*t)*z-96*t**2)
    assert sp.expand(charpoly - expected_charpoly) == 0
    assert sp.factor(L.det()) == 1+7*t
    fano_final_det = sp.Matrix([[1,1,0],[1,0,1],[0,1,1]]).det()
    assert fano_final_det == -2

    # Coefficient-sensitive rank-two example.
    y = sp.symbols('y1:5')
    sy = sum(y)
    E2 = sum(y[i]*y[j] for i,j in combinations(range(4),2))
    G = sp.expand(E2.xreplace({yi: yi+t*sy for yi in y}))
    assert sp.expand(G - E2 - (3*t+6*t**2)*sy**2) == 0
    U = sp.Matrix([[1,0,1,1],[0,1,1,2]])
    dets = {''.join(str(i+1) for i in pair): int(U[:,list(pair)].det())
            for pair in combinations(range(4),2)}
    assert all(dets.values())

    # Rank-two reconstruction from the polarized U_{2,4} order function.
    n = 8
    p2 = {(i,j): int(i//2 == j//2) for i,j in combinations(range(n),2)}
    def pv(i: int, j: int) -> int:
        return p2[tuple(sorted((i,j)))]
    lam = {(i,j): pv(i,j)-pv(0,i)-pv(0,j)
           for i,j in combinations(range(1,n),2)}
    levels = sorted(set(lam.values()))
    heights = {i: sp.Integer(0) for i in range(1,n)}
    for level in levels:
        remaining = set(range(1,n))
        classes = []
        while remaining:
            i = min(remaining)
            block = {j for j in remaining if j == i or
                     lam[tuple(sorted((i,j)))] > level}
            # Explicit transitivity check of the ultrametric partition.
            assert all(lam[tuple(sorted((a,b)))] > level
                       for a,b in combinations(sorted(block),2))
            classes.append(block)
            remaining -= block
        for digit, block in enumerate(classes):
            for i in block:
                heights[i] += digit*t**level
    C2 = sp.Matrix.hstack(sp.Matrix([0,1]), *[
        sp.Matrix([t**pv(0,i), t**pv(0,i)*heights[i]]) for i in range(1,n)])
    rank_two_checks = 0
    for i,j in combinations(range(n),2):
        expr = sp.cancel(C2[:,[i,j]].det())
        numerator, denominator = sp.fraction(expr)
        assert numerator != 0
        order = (min(k[0] for k,c in sp.Poly(numerator,t).terms()) -
                 min(k[0] for k,c in sp.Poly(denominator,t).terms()))
        assert order == pv(i,j)
        rank_two_checks += 1
    (folder / 'rank_two_example.txt').write_text(
        'Columns are paired by color. All 28 determinant orders were checked.\n'
        + str(C2) + '\n', encoding='utf-8')

    report = {
        'status': 'all exact checks passed',
        'scope': 'Finite identities and inequalities only; general results are proved in article.tex.',
        'sympy_version': sp.__version__,
        'fano_lines': [[i+1 for i in B] for B in sorted(lines)],
        'number_of_bases': len(bases),
        'number_of_degree_3_monomials': len(alphas),
        'coefficient_types': dict(types),
        'valuation_counts': {str(k): v for k,v in sorted(Counter(q.values()).items())},
        'm_convex_exchange_obligations': exchange_obligations,
        'tropical_alexandrov_fenchel_checks': af_checks,
        'polarized_maximal_minors': len(polarized),
        'short_tropical_plucker_checks': plucker_checks,
        'hessian_identities_checked': 7,
        'rank_two_reconstruction_minors_checked': rank_two_checks,
        'hessian_characteristic_polynomial': str(charpoly),
        'fano_contradiction_determinant': int(fano_final_det),
        'u24_real_representation_minors': dets,
        'lean_compilation': 'not performed; no new Lean formalization is supplied',
    }
    (folder / 'verification.json').write_text(json.dumps(report, indent=2)+'\n', encoding='utf-8')
    print(json.dumps(report, indent=2))


if __name__ == '__main__':
    main()
