#!/usr/bin/env python3
"""Reproducible checks for Natural Boundaries of Quadratic Exponential Feedback.

Exact checks use only Python's standard library. Numerical diagnostics require
mpmath. They are NOT outward-rounded interval certificates. Run:
    python verify.py
Outputs are written beside this script (or to --output-dir).
"""
from __future__ import annotations

import argparse
import json
import math
from fractions import Fraction as F
from pathlib import Path
from typing import Iterable


def multiply(a: list[F], b: list[F], n: int) -> list[F]:
    out = [F(0) for _ in range(n + 1)]
    for i, ai in enumerate(a[:n + 1]):
        if ai:
            for j, bj in enumerate(b[:n + 1 - i]):
                if bj:
                    out[i + j] += ai * bj
    return out


def exponential(a: list[F], n: int) -> list[F]:
    if a[0] != 0:
        raise ValueError('exponential requires zero constant term')
    out = [F(1)] + [F(0) for _ in range(n)]
    for k in range(1, n + 1):
        out[k] = sum((j * a[j] * out[k - j] for j in range(1, k + 1)), F(0)) / k
    return out


def compose(a: list[F], b: list[F], n: int) -> list[F]:
    if b[0] != 0:
        raise ValueError('inner series must have zero constant term')
    out = [F(0) for _ in range(n + 1)]
    power = [F(1)] + [F(0) for _ in range(n)]
    for k in range(n + 1):
        if k < len(a) and a[k]:
            out = [x + a[k] * y for x, y in zip(out, power)]
        power = multiply(power, b, n)
    return out


def forward_coefficients(n: int, actions: int | None = None) -> list[F]:
    actions = n if actions is None else min(actions, n)
    u = [F(0) for _ in range(n + 1)]
    for _ in range(n):
        v = [F(0) for _ in range(n + 1)]
        for j in range(1, actions + 1):
            e = exponential([j * j * x for x in u], n - j)
            for k, ek in enumerate(e):
                v[k + j] += ek
        u = v
    return u


def revert(u: list[F], n: int) -> list[F]:
    if u[0] != 0 or u[1] != 1:
        raise ValueError('reversion requires a tangent-to-identity series')
    q = [F(0), F(1)] + [F(0) for _ in range(n - 1)]
    for k in range(2, n + 1):
        q[k] = -compose(u[:k + 1], q[:k + 1], k)[k]
    return q


def compositions(total: int) -> Iterable[tuple[int, ...]]:
    if total == 0:
        yield ()
    else:
        for first in range(1, total + 1):
            for tail in compositions(total - first):
                yield (first,) + tail


def inverse_blocks(n: int) -> tuple[list[F], list[F], dict[int, dict[int, F]]]:
    q = [F(0) for _ in range(n + 1)]
    masses = [F(0) for _ in range(n + 1)]
    blocks: dict[int, dict[int, F]] = {1: {-1: F(1)}}
    masses[1] = F(1)
    for k in range(2, n + 1):
        atoms: dict[int, F] = {}
        for comp in compositions(k - 1):
            ell = len(comp)
            weight = F((-1)**ell * math.comb(k + ell - 1, ell), k)
            freq = sum(m * m for m in comp) + k - 2
            assert 2 * k - 3 <= freq <= k * k - k - 1
            atoms[freq] = atoms.get(freq, F(0)) + weight
            masses[k] += abs(weight)
        blocks[k] = {b: w for b, w in atoms.items() if w}
        assert masses[k] <= F(6**k, 4)
    for k, atoms in blocks.items():
        for degree in range(k, n + 1):
            q[degree] += sum((weight * F(freq**(degree - k), math.factorial(degree - k))
                              for freq, weight in atoms.items()), F(0))
    return q, masses, blocks


def kernel_residual(q: list[F], n: int, actions: int | None = None) -> list[F]:
    actions = n if actions is None else min(actions, n)
    out = [F(0) for _ in range(n + 1)]
    power = [F(1)] + [F(0) for _ in range(n)]
    for j in range(1, actions + 1):
        power = multiply(power, q, n)
        e = [F((j*j)**k, math.factorial(k)) for k in range(n + 1)]
        term = multiply(power, e, n)
        out = [a + b for a, b in zip(out, term)]
    out[1] -= 1
    return out


def moments(q: F, max_degree: int) -> list[F]:
    """Exact sums sum_{j>=1} j^m q^j, using Stirling numbers."""
    if abs(q) >= 1:
        raise ValueError('|q| must be less than one')
    weights = [F(math.factorial(k)) * q**k / (1-q)**(k+1)
               for k in range(max_degree + 1)]
    ans = [q / (1-q)]
    row = [1]
    for m in range(1, max_degree + 1):
        new = [0] * (m + 1)
        for k in range(1, m + 1):
            new[k] = (row[k-1] if k-1 < len(row) else 0) + (k*row[k] if k < len(row) else 0)
        row = new
        ans.append(sum((row[k] * weights[k] for k in range(1, m + 1)), F(0)))
    return ans


def curved_heat_coefficient(n: int, moment: list[F], b: F, c: F) -> F:
    """[t^n] sum q^j exp(t*j^2 - j*(b*t+c*t^2)), exactly."""
    value = F(0)
    for v in range(n//2 + 1):
        d = n - 2*v
        inner = sum((math.comb(d, h) * (-b)**h * moment[2*n - 3*v - h]
                     for h in range(d + 1)), F(0))
        value += (-c)**v * inner / (math.factorial(v) * math.factorial(d))
    return value


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--max-order', type=int, default=16)
    # Editorial amendment (ProveIt, 2026-09-29): the default output directory is now
    # rerun/ beside this script, so a default run no longer rewrites the recorded
    # JSON files or the two tables the article inputs; pass --output-dir . to
    # regenerate them in place. Every writer emits LF line endings.
    parser.add_argument('--output-dir', type=Path, default=Path(__file__).resolve().parent / 'rerun')
    args = parser.parse_args()
    if not 8 <= args.max_order <= 20:
        parser.error('--max-order must lie between 8 and 20 (block enumeration is exponential)')
    args.output_dir.mkdir(parents=True, exist_ok=True)
    try:
        import mpmath as mp
    except ImportError as exc:
        raise SystemExit('Install mpmath for the numerical diagnostics: python -m pip install mpmath') from exc
    mp.mp.dps = 120
    n = args.max_order
    u = forward_coefficients(n)
    q = revert(u, n)
    qb, masses, blocks = inverse_blocks(n)
    ident = [F(0), F(1)] + [F(0) for _ in range(n-1)]
    # Independently re-evaluate the formal forward right-hand side once.
    rhs = [F(0) for _ in range(n + 1)]
    for j in range(1, n + 1):
        ej = exponential([j*j*x for x in u], n-j)
        for h, value in enumerate(ej):
            rhs[j+h] += value
    assert rhs == u
    # Verify 2*S(t)^2-(1+t)*S(t)+t = 0 for the block-mass series.
    square_mass = multiply(masses, masses, n)
    for k in range(n + 1):
        assert (2*square_mass[k] - masses[k]
                - (masses[k-1] if k else 0) + (1 if k == 1 else 0)) == 0
    assert q == qb
    assert compose(u, q, n) == ident
    assert compose(q, u, n) == ident
    assert kernel_residual(q, n) == [F(0)]*(n+1)
    assert masses[1:8] == list(map(F, [1, 1, 3, 11, 45, 197, 903]))
    for j in range(1, min(8, n)+1):
        uj = forward_coefficients(n, j)
        qj = revert(uj, n)
        assert qj[:j+1] == q[:j+1]
    contraction = F(32, 225)
    image_radius = F(17, 465)
    d = F(1, 31) + F(31, 225)
    e = F(272, 3375)
    derivative_bound = (d+e)/(1-d)
    assert contraction < 1 and image_radius < F(1,16)
    assert derivative_bound < F(1,3)
    truncation_constant = F(32,31)/(1-contraction)/(1-F(1,16))
    assert truncation_constant == F(7680,5983)

    def mpf(x: F):
        return mp.mpf(x.numerator)/x.denominator

    indices = [10, 20, 40, 80]
    b, c = F(3,10), F(1,7)
    mplus = moments(F(1,2), 2*max(indices))
    mminus = moments(F(-1,2), 2*max(indices))
    a = mp.log(2)
    predicted = mp.exp(-mpf(b)*a/2)
    heat_rows = []
    oscillation_rows = []
    for order in indices:
        dn = F(math.factorial(2*order), math.factorial(order))
        gp = curved_heat_coefficient(order, mplus, b, c)
        scaled = mpf(gp/dn)*a**(2*order+1)
        heat_rows.append({'n': order, 'scaled': mp.nstr(scaled, 22),
                          'limit': mp.nstr(predicted, 22),
                          'ratio_to_limit': mp.nstr(scaled/predicted, 22)})
        gm = curved_heat_coefficient(order, mminus, b, c)
        radius = mp.sqrt(a*a + mp.pi*mp.pi)
        scaled_m = mpf(gm/dn)*radius**(2*order)
        model = sum(mp.exp(-mpf(b)*s/2)/s*(radius/s)**(2*order)
                    for s in [a-1j*mp.pi, a+1j*mp.pi])
        assert abs(mp.im(model)) < mp.mpf('1e-110')
        oscillation_rows.append({'n': order, 'scaled': mp.nstr(scaled_m, 22),
                                 'nearest_pole_model': mp.nstr(mp.re(model), 22),
                                 'difference': mp.nstr(scaled_m-mp.re(model), 22)})

    action_cut = 96
    def fixed_inverse(z):
        value = z*mp.exp(-z)
        for step in range(500):
            tail = mp.fsum(value**j * mp.exp(j*j*z) for j in range(2, action_cut+1))
            new = mp.exp(-z)*(z-tail)
            if abs(new-value) < mp.mpf('1e-113'):
                value = new
                break
            value = new
        else:
            raise RuntimeError('fixed-point iteration did not converge')
        kq = mp.fsum(j*value**(j-1)*mp.exp(j*j*z) for j in range(1,action_cut+1))
        ku = mp.fsum(j*j*value**j*mp.exp(j*j*z) for j in range(1,action_cut+1))
        qp = (1-ku)/kq
        residual = mp.fsum(value**j*mp.exp(j*j*z) for j in range(1,action_cut+1))-z
        return value, qp, residual, step+1

    boundary_rows = []
    for label, z in [('negative real', mp.mpf('-0.02')),
                     ('imaginary boundary', mp.mpc(0,'0.02')),
                     ('rational phase', 2j*mp.pi/257)]:
        value, qp, residual, steps = fixed_inverse(z)
        assert abs(qp-1) < mp.mpf(1)/3
        assert abs(residual) < mp.mpf('1e-110')
        boundary_rows.append({'point': label, 'u': mp.nstr(z, 24),
                              'Q_J(u)': mp.nstr(value, 30),
                              'abs_Qprime_minus_1': mp.nstr(abs(qp-1), 16),
                              'residual': mp.nstr(abs(residual), 8), 'iterations': steps})

    exact = {'checked_degree': n,
             'U_coefficients': [str(x) for x in u],
             'Q_coefficients': [str(x) for x in q],
             'block_uncancelled_masses': [str(x) for x in masses],
             'contraction_constant': str(contraction), 'image_radius': str(image_radius),
             'Qprime_bound': str(derivative_bound),
             'action_truncation_constant': str(truncation_constant),
             'checks': ['formal fixed point', 'two-sided formal reversion',
                        'independent signed-block expansion', 'literal kernel residual',
                        'finite-action Taylor prefixes', 'frequency range, mass bounds, and Schroeder generating equation',
                        'rational contraction and derivative inequalities']}
    numerical = {'precision_decimal_digits': mp.mp.dps,
                 'warning': 'High-precision diagnostics; not outward-rounded interval certificates.',
                 'curved_heat_positive': heat_rows, 'curved_heat_two_poles': oscillation_rows,
                 'boundary_inverse': boundary_rows, 'action_cut': action_cut,
                 'analytic_truncation_bound': mp.nstr(mpf(truncation_constant)*mp.mpf(16)**(-action_cut-1), 16)}
    (args.output_dir/'exact_checks.json').write_text(json.dumps(exact, indent=2)+'\n', newline='\n')
    (args.output_dir/'numerical_checks.json').write_text(json.dumps(numerical, indent=2)+'\n', newline='\n')
    table = ['% Generated by verify.py. Floating values are diagnostics, not interval certificates.',
             r'\begin{tabular}{rcc}', r'\toprule',
             r'$n$ & $g_n(\log 2)^{2n+1}/D_{1,n}$ & ratio to $2^{-3/20}$ \\',r'\midrule']
    for row in heat_rows:
        table.append(f"{row['n']} & {mp.nstr(mp.mpf(row['scaled']),12)} & {mp.nstr(mp.mpf(row['ratio_to_limit']),12)} " + r'\\')
    table.extend([r'\bottomrule',r'\end{tabular}'])
    (args.output_dir/'heat_table.tex').write_text('\n'.join(table)+'\n', newline='\n')
    table2 = [r'\begin{tabular}{rrrr}',r'\toprule',
              r'$n$ & normalized coefficient & nearest-pole model & difference \\',r'\midrule']
    for row in oscillation_rows:
        table2.append(f"{row['n']} & {mp.nstr(mp.mpf(row['scaled']),10)} & {mp.nstr(mp.mpf(row['nearest_pole_model']),10)} & {mp.nstr(mp.mpf(row['difference']),8)} " + r'\\')
    table2.extend([r'\bottomrule',r'\end{tabular}'])
    (args.output_dir/'oscillation_table.tex').write_text('\n'.join(table2)+'\n', newline='\n')
    print(f'All exact checks passed through degree {n}.')
    print(f'Q first coefficients: {[str(x) for x in q[1:9]]}')
    print(f'Analytic action-truncation bound (J={action_cut}): {numerical["analytic_truncation_bound"]}')
    print('Curved-heat diagnostics:')
    for row in heat_rows:
        print(row)
    print('Two-pole diagnostics:')
    for row in oscillation_rows:
        print(row)
    print('Boundary diagnostics:')
    for row in boundary_rows:
        print(row)
    print('No numerical result is used as a proof of a natural boundary.')


if __name__ == '__main__':
    main()
