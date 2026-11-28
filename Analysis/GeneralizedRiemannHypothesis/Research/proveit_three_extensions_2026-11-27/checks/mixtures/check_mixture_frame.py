#!/usr/bin/env python3
"""Exact rational checks of finite identities in mixture_frames.tex.

These synthetic checks do not test the analytic zero-count limit theorem.
They verify the estimator algebra and the information loss under merging.
"""
from fractions import Fraction as F
from itertools import combinations
from random import Random
from pathlib import Path
import json
import math


def zero(d):
    return [[F(0) for _ in range(d)] for _ in range(d)]


def transpose(a):
    return list(map(list, zip(*a)))


def mul(a, b):
    return [[sum((x*y for x, y in zip(row, col)), F(0))
             for col in zip(*b)] for row in a]


def sub(a, b):
    return [[x-y for x, y in zip(r, s)] for r, s in zip(a, b)]


def scale(a, c):
    return [[c*x for x in r] for r in a]


def det(a):
    if not a:
        return F(1)
    a = [r[:] for r in a]
    ans = F(1)
    for i in range(len(a)):
        pivot = next((j for j in range(i, len(a)) if a[j][i]), None)
        if pivot is None:
            return F(0)
        if pivot != i:
            a[i], a[pivot] = a[pivot], a[i]
            ans = -ans
        pivot = a[i][i]
        ans *= pivot
        for j in range(i+1, len(a)):
            q = a[j][i]/pivot
            a[j] = [x-q*y for x, y in zip(a[j], a[i])]
    return ans


def inv(a):
    d = len(a)
    a = [r[:] + [F(i == j) for j in range(d)] for i, r in enumerate(a)]
    for i in range(d):
        k = next(j for j in range(i, d) if a[j][i])
        a[i], a[k] = a[k], a[i]
        q = a[i][i]
        a[i] = [x/q for x in a[i]]
        for j in range(d):
            if j != i:
                q = a[j][i]
                a[j] = [x-q*y for x, y in zip(a[j], a[i])]
    return [r[d:] for r in a]


def is_psd(a):
    d = len(a)
    return all(det([[a[i][j] for j in inds] for i in inds]) >= 0
               for k in range(1, d+1) for inds in combinations(range(d), k))


def frame(rows):
    d = len(rows[0])
    g = zero(d)
    for v in rows:
        s = sum(v)
        if s:
            for i in range(d):
                for j in range(d):
                    g[i][j] += F(v[i]*v[j], s)
    return g


def main():
    rng = Random(20261127)
    cases = 0
    compression_cases = 0
    for d in range(1, 5):
        for repetition in range(100):
            rows = [[int(i == j) for j in range(d)] for i in range(d)]
            rows += [[rng.randrange(7) for _ in range(d)]
                     for _ in range(rng.randrange(2, 16))]
            rows = [v for v in rows if sum(v)]
            g = frame(rows)
            gi = inv(g)
            identity = [[F(i == j) for j in range(d)] for i in range(d)]
            assert mul(gi, g) == identity
            theta = [F(rng.randrange(1, 16), 5) for _ in range(d)]
            bound = F(3)
            # Exact unbiasedness is gi*g*theta = theta.
            col = [[x] for x in theta]
            assert mul(mul(gi, g), col) == col
            mid = zero(d)
            fisher = zero(d)
            for v in rows:
                s = sum(v)
                rate = sum((x*y for x, y in zip(theta, v)), F(0))
                for i in range(d):
                    for j in range(d):
                        mid[i][j] += rate*F(v[i]*v[j], s*s)
                        fisher[i][j] += F(v[i]*v[j])/rate
            covariance_times_t = mul(mul(gi, mid), gi)
            assert is_psd(sub(scale(gi, bound), covariance_times_t))
            assert is_psd(sub(fisher, scale(g, F(1)/max(theta))))
            assert is_psd(sub(scale(g, F(1)/min(theta)), fisher))
            # Merging rows is a deterministic coarsening and decreases the frame.
            merged = [[x+y for x, y in zip(rows[0], rows[1])]] + rows[2:]
            assert is_psd(sub(g, frame(merged)))
            diagonal_totals = zero(d)
            for j in range(d):
                diagonal_totals[j][j] = sum(v[j] for v in rows)
            assert is_psd(sub(diagonal_totals, g))
            if d <= 3 and repetition < 20:
                # A rigorous rational lower eigenvalue bound for this matrix.
                trace = sum(g[j][j] for j in range(d))
                c = det(g)/trace**(d-1)
                total = sum(map(sum, rows))
                ngrid = 1
                while F(d, ngrid*ngrid)*total > c/4:
                    ngrid *= 2
                groups = {}
                for v in rows:
                    s = sum(v)
                    key = tuple(ngrid*x//s for x in v)
                    w = groups.setdefault(key, [0]*d)
                    for j in range(d):
                        w[j] += v[j]
                grouped_rows = list(groups.values())
                gcell = frame(grouped_rows)
                assert is_psd(sub(g, gcell))
                assert is_psd(sub(gcell, scale(identity, 3*c/4)))
                jcells = len(grouped_rows)
                eta = c/(4*jcells)
                heavy = [v for v in grouped_rows if sum(v) >= eta]
                gh = frame(heavy)
                assert is_psd(sub(gh, scale(identity, c/2)))
                normalized = [[F(x, sum(v)) for x in v] for v in heavy]
                choices = list(combinations(range(len(heavy)), d))
                best = max(choices, key=lambda inds: det([normalized[j] for j in inds])**2)
                p = [normalized[j] for j in best]
                kappa_squared = (c/(2*total))**d/F(math.comb(jcells, d))
                assert det(p)**2 >= kappa_squared
                pi = inv(p)
                assert mul(pi, p) == identity
                # Each selected group is one independent Poisson count.
                channel_cov = zero(d)
                for j, row_index in enumerate(best):
                    s = sum(heavy[row_index])
                    channel_cov[j][j] = sum(x*y for x, y in zip(p[j], theta))/s
                cov = mul(mul(pi, channel_cov), transpose(pi))
                bound_matrix = scale(mul(pi, transpose(pi)), bound/eta)
                assert is_psd(sub(bound_matrix, cov))
                compression_cases += 1
            cases += 1
    result = {
        'cases': cases,
        'dimensions': [1, 2, 3, 4],
        'arithmetic': 'fractions.Fraction; every principal minor checked exactly',
        'checks': ['unbiasedness', 'covariance upper bound',
                   'Fisher comparison on interior box',
                   'information monotonicity under merging',
                   'diagonal total upper bound'],
        'counter_compression_cases': compression_cases,
        'counter_compression_checks': ['simplex cell covariance loss',
                'heavy-cell frame lower bound', 'Cauchy-Binet determinant bound',
                'd-channel unbiased inverse', 'd-channel covariance bound'],
        'status': 'all passed',
        'scope': 'finite synthetic matrices only; not validation of analytic asymptotics'
    }
    out = Path(__file__).with_name('mixture_frame_checks.json')
    out.write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
