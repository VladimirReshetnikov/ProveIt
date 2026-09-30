#!/usr/bin/env python3
"""Reproducible checks for The Endpoint Geometry of Common-Digit Fabius Laws.

Standard library only. Exact Fraction assertions check envelope identities and
one finite probability certificate. Floating-point asymptotic tables are
illustrations, not interval-certified evaluations or substitutes for proofs.
Run: python3 verify.py
"""
from __future__ import annotations

import argparse
import csv
import json
import math
from fractions import Fraction as F
from pathlib import Path
from random import Random
from typing import Sequence

ROOT = Path(__file__).resolve().parent
# ed. (2026-09-29): outputs go under --output-root (default recomputed/), laid
# out like the package (verification.txt, generated/), so that a rerun cannot
# replace the recorded files or the two tables article.tex inputs; LF endings.
OUT_ROOT = ROOT / 'recomputed'
OUT = OUT_ROOT / 'generated'


def envelope(a: Sequence[F], lam: Sequence[F]):
    """Exact integration by all nonnegative pairwise intersection abscissae."""
    if len(a) != len(lam) or not a or any(x <= 0 for x in (*a, *lam)):
        raise ValueError('Positive intercepts and slopes of equal nonzero length required.')
    if len(set(lam)) != len(lam):
        raise ValueError('Slopes must be distinct.')
    stop = max(x/y for x, y in zip(a, lam))
    cuts = {F(0), stop}
    for i in range(len(a)):
        cuts.add(a[i]/lam[i])
        for j in range(i):
            x = (a[i]-a[j])/(lam[i]-lam[j])
            if 0 < x < stop:
                cuts.add(x)
    cuts = sorted(x for x in cuts if 0 <= x <= stop)
    area, lengths, intervals = F(0), [F(0)]*len(a), []
    for left, right in zip(cuts, cuts[1:]):
        mid = (left+right)/2
        i = max(range(len(a)), key=lambda k: a[k]-lam[k]*mid)
        if a[i]-lam[i]*mid <= 0:
            continue
        area += a[i]*(right-left)-lam[i]*(right*right-left*left)/2
        lengths[i] += right-left
        if intervals and intervals[-1][0] == i:
            intervals[-1] = (i, intervals[-1][1], right)
        else:
            intervals.append((i, left, right))
    return area, lengths, intervals


def check_envelopes() -> int:
    rng = Random(20260929)
    for _ in range(350):
        d = rng.randint(1, 6)
        lam = [F(v, 7) for v in rng.sample(range(1, 60), d)]
        a = [F(rng.randint(1, 40), 9) for _ in range(d)]
        area, ell, intervals = envelope(a, lam)
        assert sum(ell) == max(x/y for x, y in zip(a, lam))
        assert sum(x*y for x, y in zip(lam, ell)) == max(a)
        assert sum(x*y for x, y in zip(a, ell)) == 2*area
        last = intervals[-1][0]
        formula = a[last]**2/(2*lam[last])
        for left, right in zip(intervals, intervals[1:]):
            i, j = left[0], right[0]
            assert lam[i] > lam[j]
            formula += (a[i]-a[j])**2/(2*(lam[i]-lam[j]))
        assert formula == area
        scaled, _, _ = envelope([3*x for x in a], lam)
        assert scaled == 9*area
    # Bivariate phase formulas, including both transition boundaries.
    for a1 in range(1, 31):
        for a2 in range(1, 16):
            a, b, A, B = F(a1, 5), F(a2, 7), F(4), F(1)
            if a <= b:
                expected = b*b/(2*B)
            elif a >= A*b/B:
                expected = a*a/(2*A)
            else:
                expected = b*b/(2*B)+(a-b)**2/(2*(A-B))
            assert envelope([a, b], [A, B])[0] == expected
    # Equal-margin d-variate formula: choose intercepts sqrt(lambda), then I=K/2.
    for ys in ([3, 2, 1], [10, 7, 3, 1], [5, 4], [9, 8, 7, 6, 5, 4]):
        a, lam = [F(y) for y in ys], [F(y*y) for y in ys]
        kappa = 1+sum(F(x-y, x+y) for x, y in zip(ys, ys[1:]))
        assert 2*envelope(a, lam)[0] == kappa
    return 350+30*15+4


def log_fraction(x: F) -> float:
    if x <= 0:
        raise ValueError('Logarithm requires a positive fraction.')
    return math.log(x.numerator)-math.log(x.denominator)


def exact_certificate():
    """Finite independent-simplex/box lower bound; every budget checked exactly."""
    q, thresholds = [F(1, 2), F(3, 4)], [F(1, 2**20), F(1, 2**15)]
    d, R = 2, F(16)
    N = 1
    while any(qi**N/xi > 1/R for qi, xi in zip(q, thresholds)):
        N += 1
    coeff = [[(1-qi)*qi**n/xi for n in range(N)] for qi, xi in zip(q, thresholds)]
    cores, residual = [[] for _ in range(d)], []
    for n in range(N):
        winner = max(range(d), key=lambda j: coeff[j][n])
        if coeff[winner][n] >= R and all(
                j == winner or coeff[winner][n] >= R*coeff[j][n] for j in range(d)):
            cores[winner].append(n)
        else:
            residual.append(n)
    budget = 1-F(d+2)/R
    caps = {n: min(F(1), 1/(R*max(1, len(residual))*max(coeff[j][n] for j in range(d))))
            for n in residual}
    totals = []
    for i in range(d):
        total = q[i]**N/thresholds[i]
        total += sum(coeff[i][n]*caps[n] for n in residual)
        for j, core in enumerate(cores):
            if core:
                ratio = max(coeff[i][n]/coeff[j][n] for n in core)
                total += ratio*budget
                assert budget <= min(coeff[j][n] for n in core)
        assert total <= 1
        totals.append(total)
    lower = F(1)
    for j, core in enumerate(cores):
        lower *= budget**len(core)/math.factorial(len(core))
        for n in core:
            lower /= coeff[j][n]
    for cap in caps.values():
        lower *= cap
    upper = F(1)
    upper_counts = []
    for j in range(d):
        block = [n for n in range(N)
                 if max(coeff[i][n] for i in range(d)) > 1
                 and max(range(d), key=lambda i: coeff[i][n]) == j]
        upper_counts.append(len(block))
        upper /= math.factorial(len(block))
        for n in block:
            upper /= coeff[j][n]
    assert 0 < lower <= upper <= 1
    output = {
        'q': list(map(str, q)), 'thresholds': list(map(str, thresholds)),
        'N': N, 'R': str(R), 'simplex_budget': str(budget),
        'core_sizes': list(map(len, cores)), 'residual_size': len(residual),
        'upper_block_sizes': upper_counts,
        'exact_budget_totals': list(map(str, totals)),
        'log_lower_float': log_fraction(lower), 'log_upper_float': log_fraction(upper),
        'lower_numerator_bits': lower.numerator.bit_length(),
        'lower_denominator_bits': lower.denominator.bit_length(),
        'status': 'All feasibility and rational probability inequalities checked using Fraction.'}
    (OUT/'exact_certificate.json').write_text(json.dumps(output, indent=2)+'\n',
                                              encoding='utf-8', newline='\n')
    return output


def finite_log_bounds(lam, intercept, t, beta=1.0, K=2.0):
    """Log simplex bounds for Beta(beta,1) digits, evaluated in floating point."""
    d = len(lam)
    if t <= 1 or beta <= 0:
        raise ValueError('Need t>1 and beta>0.')
    cutoff = K*math.log(t)
    eps = t**(-K)
    budget = 1-(d+2)*eps
    if budget <= 0:
        raise ValueError('t too small for this certificate.')
    s = [ai*t for ai in intercept]
    lw = [math.log(-math.expm1(-li)) for li in lam]
    N = math.ceil(max((si+cutoff)/li for si, li in zip(s, lam)))
    cores = [[] for _ in lam]
    residual = []
    upper_sums, upper_counts = [0.0]*d, [0]*d
    values = []
    for n in range(N):
        b = [si+wi-li*n for si, wi, li in zip(s, lw, lam)]
        winner = max(range(d), key=b.__getitem__)
        best = b[winner]
        values.append((winner, b))
        if best > 0:
            upper_sums[winner] += best
            upper_counts[winner] += 1
        if best >= cutoff and all(j == winner or best-b[j] >= cutoff for j in range(d)):
            cores[winner].append(n)
        else:
            residual.append(n)
    log_cgamma = math.lgamma(beta+1)  # c=beta for a Beta(beta,1) density
    upper = sum(n*log_cgamma-math.lgamma(beta*n+1)-beta*ss
                for n, ss in zip(upper_counts, upper_sums))
    lower = 0.0
    for j, core in enumerate(cores):
        n = len(core)
        lower += n*log_cgamma+beta*n*math.log(budget)-math.lgamma(beta*n+1)
        lower -= beta*sum(values[k][1][j] for k in core)
    strip_penalty = cutoff+math.log(max(1, len(residual)))
    lower -= beta*sum(max(0.0, max(values[k][1])+strip_penalty) for k in residual)
    assert lower <= upper+1e-7*max(1, abs(upper))
    return lower, upper, [len(c) for c in cores], len(residual)


def asymptotic_tables():
    lam, a = [4.0, 1.0], [2.0, 1.0]
    area, ell, _ = envelope(list(map(F, a)), list(map(F, lam)))
    ell = list(map(float, ell))
    T = sum(ell)
    w = [-math.expm1(-x) for x in lam]
    A = T-max(a)/2-sum(e*math.log(wi*e) for e, wi in zip(ell, w))
    rows = []
    for t in [100, 500, 2000, 10000, 50000]:
        lo, hi, counts, ns = finite_log_bounds(lam, a, t)
        main = float(area)*t*t+T*t*math.log(t)
        rows.append({'t': t, 'normalized_lower': (lo+main)/t,
                     'predicted_coefficient': A, 'normalized_upper': (hi+main)/t,
                     'core_1': counts[0], 'core_2': counts[1], 'residual': ns})
    with (OUT/'small_ball_bounds.csv').open('w', newline='', encoding='utf-8') as f:
        writer = csv.DictWriter(f, fieldnames=rows[0].keys(), lineterminator='\n')
        writer.writeheader(); writer.writerows(rows)
    lines = [r'\begin{tabular}{r r r r}',r'\toprule',
             r'$t$ & Lower certificate & $A(a)$ & Upper certificate\\',r'\midrule']
    lines += [f"{r['t']:,} & {r['normalized_lower']:.6f} & {A:.6f} & {r['normalized_upper']:.6f}\\\\"
              for r in rows]
    lines += [r'\bottomrule',r'\end{tabular}']
    (OUT/'bounds_table.tex').write_text('\n'.join(lines)+'\n', encoding='utf-8', newline='\n')
    D = math.log(16)
    mesh = []
    for d in [2, 3, 5, 9, 17, 33]:
        kd = 1+(d-1)*math.tanh(D/(4*(d-1)))
        ki = 1+D/4
        mesh.append((d, kd, ki, (ki-kd)*(d-1)**2))
    lines = [r'\begin{tabular}{r r r r}',r'\toprule',
             r'$d$ & $\kappa_d^{\max}$ & $\kappa_\infty$ & $(d-1)^2(\kappa_\infty-\kappa_d^{\max})$\\',r'\midrule']
    lines += [f'{d} & {kd:.9f} & {ki:.9f} & {gap:.9f}\\\\' for d,kd,ki,gap in mesh]
    lines += [r'\bottomrule',r'\end{tabular}']
    (OUT/'mesh_table.tex').write_text('\n'.join(lines)+'\n', encoding='utf-8', newline='\n')
    return rows, mesh


def further_checks():
    # Quantile-to-copula second-order cancellation, including non-unit beta,c.
    rng = Random(1789)
    for _ in range(100):
        lam = [9.0, 4.0, 1.0]
        b = [3.0, 2.0, 1.0]  # Any strict-chamber intercepts are sufficient.
        _, ell_exact, _ = envelope(list(map(F,b)), list(map(F,lam)))
        ell = list(map(float, ell_exact))
        beta, c = math.exp(rng.uniform(-1,1)), math.exp(rng.uniform(-1,1))
        bt, et = [v/math.sqrt(beta) for v in b], [v/math.sqrt(beta) for v in ell]
        w = [-math.expm1(-v) for v in lam]
        TT = sum(et)
        A = beta*TT-beta*max(bt)/2-beta*sum(e*math.log(beta*wi*e) for e,wi in zip(et,w))
        A += TT*(math.log(c)+math.lgamma(beta))
        dd = [1-math.log(wi*beta*bi/li)+(math.log(c)+math.lgamma(beta))/beta-li/2
              for wi,bi,li in zip(w,bt,lam)]
        reduced = A-beta*sum(e*v for e,v in zip(et,dd))
        target = math.sqrt(beta)*sum(e*math.log((bi/li)/e) for e,bi,li in zip(ell,b,lam))
        assert math.isclose(reduced,target,rel_tol=2e-12,abs_tol=2e-12)
    return 100


def main():
    global OUT_ROOT, OUT
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output-root', type=Path, default=OUT_ROOT,
                        help='directory receiving verification.txt and generated/ '
                             '(default: recomputed/)')
    OUT_ROOT = parser.parse_args().output_root.resolve()
    OUT = OUT_ROOT / 'generated'
    OUT.mkdir(parents=True, exist_ok=True)
    output = []
    def say(s=''):
        print(s); output.append(s)
    count = check_envelopes()
    say(f'PASS: {count} exact envelope/phase/diagonal tests (Fraction arithmetic).')
    cert = exact_certificate()
    say('PASS: finite lower/upper probability certificate and all row budgets (exact rational arithmetic).')
    say(f"  N={cert['N']}; cores={cert['core_sizes']}; residual={cert['residual_size']}")
    say(f"  log lower={cert['log_lower_float']:.9f}; log upper={cert['log_upper_float']:.9f}")
    say(f'PASS: {further_checks()} floating-point second-order cancellation checks.')
    rows, mesh = asymptotic_tables()
    say('\nAsymptotic certificate table: [log bound + I*t^2 + T*t*log(t)]/t')
    for r in rows:
        say(f"  t={r['t']:6d}: {r['normalized_lower']:.9f}  A={r['predicted_coefficient']:.9f}  {r['normalized_upper']:.9f}")
    say('\nOptimal mesh: A/B=16')
    for d,kd,ki,gap in mesh:
        say(f'  d={d:2d}: kappa={kd:.9f}; limit={ki:.9f}; scaled gap={gap:.9f}')
    H=math.sqrt(8/math.log(2))*math.log(1.5)
    say(f'\nFabius q=1/2, r=2^(-1/4): kappa=4/3, eta=3/4, H={H:.12f}')
    delta=math.log(2)
    say(f'Noncommuting-limit example delta=log(2): exact-tail limit={2/(1+math.exp(-delta)):.12f}; Gaussian-tail limit={2/(1+1/math.cosh(delta)):.12f}')
    say('\nScope: rational assertions are exact finite checks. Decimal tables use ordinary')
    say('floating point, are not interval enclosures, and are not proofs of limit theorems.')
    (OUT_ROOT/'verification.txt').write_text('\n'.join(output)+'\n',
                                            encoding='utf-8', newline='\n')

if __name__ == '__main__':
    main()
