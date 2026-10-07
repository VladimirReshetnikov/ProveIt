#!/usr/bin/env python3
"""Exact, reproducible checks for Gowers arrangement degeneracy.

Default: Python standard library only. Reconstructs the rational certificate,
checks its modular stability, coefficient-class counts, and Boolean identities.
--subset: also performs an independent exhaustive prime-field subset-sum test
          (requires NumPy). No floating-point arithmetic is used for claims.

This is a finite computation, not a proof-assistant formalization. The general
bounds in the article have conventional proofs independent of the enumeration.
"""
from __future__ import annotations

import argparse
import json
import random
from fractions import Fraction
from itertools import combinations, product
from math import comb
from pathlib import Path
from typing import Iterable, Sequence

F = Fraction
ROOT = Path(__file__).resolve().parents[1]


def rref(rows: Sequence[Sequence[int | Fraction]]):
    """Exact reduced row echelon form, including an augmented column if present."""
    if not rows:
        return (), ()
    a = [[F(x) for x in row] for row in rows]
    pivots = []
    i = 0
    for j in range(len(a[0])):
        z = next((z for z in range(i, len(a)) if a[z][j]), None)
        if z is None:
            continue
        a[i], a[z] = a[z], a[i]
        v = a[i][j]
        a[i] = [x / v for x in a[i]]
        for z in range(len(a)):
            if z != i and a[z][j]:
                v = a[z][j]
                a[z] = [x - v*y for x, y in zip(a[z], a[i])]
        pivots.append(j)
        i += 1
        if i == len(a):
            break
    return tuple(tuple(row) for row in a if any(row)), tuple(pivots)


def determinant(rows):
    a = [[F(x) for x in row] for row in rows]
    result = F(1)
    for i in range(len(a)):
        j = next((j for j in range(i, len(a)) if a[j][i]), None)
        if j is None:
            return F(0)
        if j != i:
            a[i], a[j] = a[j], a[i]
            result = -result
        v = a[i][i]
        result *= v
        for j in range(i+1, len(a)):
            c = a[j][i] / v
            for z in range(i+1, len(a)):
                a[j][z] -= c*a[i][z]
    return result


def prime_factors(n: int) -> set[int]:
    n = abs(n)
    result = set()
    d = 2
    while d*d <= n:
        if n % d == 0:
            result.add(d)
            while n % d == 0:
                n //= d
        d += 1
    if n > 1:
        result.add(n)
    return result


def affine_key(t):
    v = [F(x-t[0]) for x in t]
    a = next((x for x in v if x), None)
    return None if a is None else tuple(x/a for x in v)


def trinomial(n: int) -> int:
    return sum(comb(n, 2*j)*comb(2*j, j) for j in range(n//2+1))


def class_count(length: int, p: int) -> int:
    """Balanced ternary profile classes over the prime field."""
    if length < 2 or length % 2:
        raise ValueError('length must be positive and even')
    if p in (2, 3):
        return (p**(length-2)-1)//(p-1)
    dp = {0: 1}
    for _ in range(length):
        nxt = {}
        for a, count in dp.items():
            for b in (-1, 0, 1):
                nxt[a+b] = nxt.get(a+b, 0) + count
        dp = nxt
    t = sum(count for a, count in dp.items() if a % p == 0)
    b = sum(comb(length, j) for j in range(length+1)
            if (j-length//2) % p == 0)
    return (t-2*b+1)//2


def enumerate_profile_count(length: int, p: int) -> int:
    signs = [1]*(length//2) + [-1]*(length//2)
    alphabet = sorted({0, 1, p-1})
    seen = set()
    for t in product(alphabet, repeat=length):
        if sum(s*x for s, x in zip(signs, t)) % p:
            continue
        v = [(x-t[0]) % p for x in t]
        a = next((x for x in v if x), None)
        if a is not None:
            inv = pow(a, -1, p)
            seen.add(tuple(x*inv % p for x in v))
    return len(seen)


def coefficient_classes():
    signs = (1, 1, -1, -1)
    intrinsic = [s*a for s in signs for a in (1, -1)]
    classes = {}
    for eta in product((-1, 0, 1), repeat=8):
        if sum(eta):
            continue
        key = affine_key([x*y for x, y in zip(eta, intrinsic)])
        if key is not None:
            classes.setdefault(key, eta)
    nonparity = {key: eta for key, eta in classes.items()
                 if any(eta[2*j]+eta[2*j+1] for j in range(4))}
    core, roots = [], {}
    for eta in nonparity.values():
        c = [eta[2*j]+eta[2*j+1] for j in range(4)]
        a, b = c[0]+c[3], c[1]+c[3]
        if a == b == 0:
            core.append(eta)
        elif a:
            ratio = F(-b, a)
            if ratio not in (0, 1, -1):
                roots.setdefault(ratio, []).append(eta)
    assert (len(classes), len(nonparity), len(core)) == (484, 459, 15)
    return core, roots


def line_equations(eta, ratio):
    c = [eta[2*j]+eta[2*j+1] for j in range(4)]
    b = [eta[2*j+1] for j in range(4)]
    rows = [[c[0], c[1], c[2], -sum(b)],
            [c[0]*ratio, c[1], 0, -(b[0]+b[3])*ratio-b[1]-b[3]]]
    rr, pivots = rref(rows)
    assert len(rr) == 2 and all(i < 3 for i in pivots)
    return rr


def construct_certificate():
    core, roots = coefficient_classes()
    cert = {}
    for ratio in sorted(roots):
        lines = sorted(set(line_equations(eta, ratio)
                           for eta in core+roots[ratio]))
        points = {}
        for i, j in combinations(range(len(lines)), 2):
            rr, pivots = rref(lines[i]+lines[j])
            if len(rr) == 3 and pivots == (0, 1, 2):
                point = tuple(row[-1] for row in rr)
                points.setdefault(point, set()).update((i, j))
        for point, incidence in points.items():
            actual = {i for i, line in enumerate(lines)
                      if all(sum(row[j]*point[j] for j in range(3)) == row[3]
                             for row in line)}
            assert actual == incidence
        loss = sum(len(v)-1 for v in points.values())
        cert[str(ratio)] = {
            'lines': [[[str(x) for x in row] for row in line] for line in lines],
            'points': [{'point': list(map(str, point)), 'lines': sorted(v)}
                       for point, v in sorted(points.items())],
            'loss': loss,
        }
    return cert


def certify_characteristics(cert):
    """Preserve ranks by one maximal nonzero minor; preserve distinct points.

Higher minors are rationally zero, so cannot become nonzero after reduction.
This checks BOTH coefficient and augmented ranks for every line pair.
"""
    bad = {2, 3, 5, 7}  # p > 8 also stabilizes the ternary profile enumeration.
    matrix_count = 0
    minor_witnesses = []

    def include(x, reason):
        x = F(x)
        primes = prime_factors(x.numerator) | prime_factors(x.denominator)
        bad.update(primes)
        return sorted(primes)

    def certify_matrix(a, reason):
        nonlocal matrix_count
        matrix_count += 1
        rank = len(rref(a)[0])
        if not rank:
            return
        candidates = []
        for ri in combinations(range(len(a)), rank):
            for ci in combinations(range(len(a[0])), rank):
                v = determinant([[a[i][j] for j in ci] for i in ri])
                if v:
                    candidates.append((v, ri, ci))
        assert candidates
        val, rows, cols = min(candidates, key=lambda z: abs(z[0].numerator)*z[0].denominator)
        include(val, reason)
        minor_witnesses.append({'matrix': reason, 'rank': rank,
                                'rows': rows, 'columns': cols, 'minor': str(val)})

    for key, item in cert.items():
        include(F(key), 'ratio')
        lines = [tuple(tuple(F(x) for x in row) for row in line)
                 for line in item['lines']]
        for line in lines:
            for row in line:
                for x in row:
                    include(F(1, x.denominator), 'line denominator')
        for i, j in combinations(range(len(lines)), 2):
            rows = list(lines[i]+lines[j])
            certify_matrix([row[:3] for row in rows], f'{key}:{i},{j}:coeff')
            certify_matrix(rows, f'{key}:{i},{j}:augmented')
        points = [tuple(F(x) for x in pt['point']) for pt in item['points']]
        for point in points:
            for x in point:
                include(F(1, x.denominator), 'point denominator')
        for x, y in combinations(points, 2):
            diffs = [a-b for a, b in zip(x, y) if a != b]
            assert diffs
            include(min(diffs, key=lambda a: abs(a.numerator)*a.denominator),
                    'point distinction')
    ratios = list(map(F, cert)) + [F(0), F(1), F(-1)]
    for a, b in combinations(ratios, 2):
        include(a-b, 'ratio distinction')
    assert bad == {2, 3, 5, 7}
    assert matrix_count == 7296
    return sorted(bad), matrix_count, minor_witnesses


def all_moments(k, q, eta, bases, side, u):
    n = len(u)
    vertices = list(product((0, 1), repeat=k))
    result = []
    for mask in range(1 << (k+1)):
        value = 0
        for j in range(n):
            for eps in vertices:
                term = eta[j, eps]
                for i in range(k):
                    if mask >> i & 1:
                        term *= bases[j][i]+eps[i]*side[i]
                if mask >> k & 1:
                    term *= u[j]
                value += term
        result.append(value % q)
    return result


def core_identity_checks():
    rng = random.Random(20261006)
    checked = 0
    for k, q in ((1, 11), (2, 19), (3, 37), (4, 67)):
        n = 4
        signs = (1, 1, -1, -1)
        u = (2, 1, 0, 3)
        profiles = []
        for i in range(k):
            for mask in range((1 << n)-1):
                slopes = [0]*k
                slopes[i] = 1
                profiles.append(([-1+((mask >> j) & 1) for j in range(n)], slopes))
        for i, ell in combinations(range(k), 2):
            for sign in (-1, 1):
                slopes = [0]*k
                slopes[i], slopes[ell] = 1, sign
                profiles.append(([-1 if sign == 1 else 0]*n, slopes))
        assert len(profiles) == k*15+k*(k-1)
        for offsets, slopes in profiles:
            side = [rng.randrange(1, q) for _ in range(k)]
            z = [[rng.randrange(q) for _ in range(k)] for _ in range(n)]
            i = next(i for i, b in enumerate(slopes) if b)
            z[0][i] = z[1][i] = 0
            a = sum(signs[j]*(offsets[j]+sum(slopes[t]*z[j][t] for t in range(k)))
                    for j in range(n)) % q
            b = sum(signs[j]*u[j]*(offsets[j]+sum(slopes[t]*z[j][t] for t in range(k)))
                    for j in range(n)) % q
            # Active slope is 1; s_0=s_1=1. Solve x+y=-a, 2x+y=-b.
            z[0][i], z[1][i] = (a-b) % q, (b-2*a) % q
            bases = [[z[j][i]*side[i] % q for i in range(k)] for j in range(n)]
            eta = {}
            for j in range(n):
                for eps in product((0, 1), repeat=k):
                    value = offsets[j]+sum(slopes[i]*eps[i] for i in range(k))
                    assert value in (-1, 0, 1)
                    eta[j, eps] = signs[j]*(-1)**sum(eps)*value
            assert not any(all_moments(k, q, eta, bases, side, u))
            checked += 1
    return checked


def subset_sum_check(q: int):
    """Independent exhaustive enumeration, using no line certificate."""
    try:
        import numpy as np
    except ImportError as exc:
        raise RuntimeError('--subset requires NumPy') from exc
    xs = np.array(list(product(range(q), repeat=3)), dtype=np.int64)
    by_ratio = {}
    for ratio in range(2, q-1):
        u = np.array([ratio, 1, 0, ratio+1], dtype=np.int64) % q
        count = 0
        for start in range(0, len(xs), 128):
            batch = xs[start:start+128]
            x = np.column_stack((batch, np.zeros(len(batch), dtype=np.int64)))
            sums = np.zeros((len(x), 1, 4), dtype=np.int64)
            for j in range(4):
                for eps in (0, 1):
                    y = (x[:, j]+eps) % q
                    col = np.column_stack((np.ones(len(x), dtype=np.int64), y,
                                           np.full(len(x), u[j]), y*u[j] % q))
                    sums = np.concatenate((sums, (sums+col[:, None, :]) % q), axis=1)
            keys = np.sum(sums*np.array([1, q, q*q, q**3]), axis=2)
            keys.sort(axis=1)
            distinct = 1+np.count_nonzero(np.diff(keys, axis=1), axis=1)
            assert np.all(distinct <= 255)
            count += int(np.count_nonzero(distinct < 255))
        by_ratio[str(ratio)] = count
    total = sum(by_ratio.values())
    prediction = 15*q*q+67*q-248
    if q >= 11:
        assert total == prediction
    else:
        assert total != prediction  # Deliberate small-characteristic negative controls.
    return {'by_ratio': by_ratio, 'count': total, 'prediction': prediction,
            'match': total == prediction, 'base_tuples_checked': (q-3)*q**3}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--subset', action='store_true', help='run independent NumPy exhaustive checks')
    parser.add_argument('--write', action='store_true', help='write reconstructed certificate and report')
    parser.add_argument('--minors', action='store_true', help='also write the optional 7296 minor witnesses')
    args = parser.parse_args()
    cert = construct_certificate()
    cert_path = ROOT/'code'/'exact_certificate.json'
    if cert_path.exists():
        assert cert == json.loads(cert_path.read_text()), 'Stored certificate does not match reconstruction'
    bad, matrix_count, minors = certify_characteristics(cert)
    profiles = []
    for length in (4, 6, 8):
        for p in (2, 3, 5, 7, 11):
            predicted = class_count(length, p)
            observed = enumerate_profile_count(length, p)
            assert observed == predicted
            profiles.append({'length': length, 'p': p, 'count': observed})
    table = [{'ratio': r, 'lines': len(v['lines']), 'points': len(v['points']),
              'loss': v['loss']} for r, v in cert.items()]
    assert sum(row['lines']-15 for row in table) == 112
    assert sum(row['loss'] for row in table) == 248
    core_checks = core_identity_checks()
    report = {'status': 'all checks passed', 'balanced_classes_m8': 484,
              'nonparity_classes': 459, 'core_classes_k1d2': 15,
              'line_table': table, 'extra_lines': 112, 'intersection_loss': 248,
              'excluded_primes': bad, 'rank_matrices_checked': matrix_count,
              'profile_checks': profiles, 'core_identity_checks': core_checks}
    if args.subset:
        report['independent_subset_checks'] = {str(q): subset_sum_check(q)
                                               for q in (5, 7, 11, 13, 17, 19)}
    if args.write:
        cert_path.write_text(json.dumps(cert, indent=2)+'\n')
        (ROOT/'verification.json').write_text(json.dumps(report, indent=2)+'\n')
        if args.minors:
            (ROOT/'code'/'minor_witnesses.json').write_text(json.dumps(minors, indent=2)+'\n')
    print(json.dumps(report, indent=2))


if __name__ == '__main__':
    main()
