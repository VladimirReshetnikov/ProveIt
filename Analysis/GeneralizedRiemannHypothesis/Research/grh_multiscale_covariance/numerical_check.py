#!/usr/bin/env python3
"""Illustrative prime-side numerical experiment; not a proof or certified bound.
Requires numpy and mpmath. No zero data are used. Python 3.10+.
"""
import argparse
import csv
import json
import math
from pathlib import Path
import numpy as np
import mpmath as mp


def prime_powers(limit):
    sieve = np.ones(limit + 1, dtype=bool)
    sieve[:2] = False
    for p in range(2, math.isqrt(limit) + 1):
        if sieve[p]:
            sieve[p*p::p] = False
    powers, weights = [], []
    for p0 in np.flatnonzero(sieve):
        p = int(p0)
        k = p
        while k <= limit:
            powers.append(k)
            weights.append(math.log(p))
            k *= p
    order = np.argsort(powers)
    return np.asarray(powers, dtype=np.int64)[order], np.asarray(weights)[order]


def evaluate(a, xs, ns, ws, constant):
    mask = ns % 3 == a
    n, w = ns[mask], ws[mask]
    ps = np.concatenate(([0.], np.cumsum(w/n)))
    pw = np.concatenate(([0.], np.cumsum(w)))
    k = np.searchsorted(n, xs, side='right')
    return np.sqrt(xs) * (ps[k] - pw[k]/xs - np.log(xs)/2 - constant)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--end', type=float, default=13.0)
    parser.add_argument('--step', type=float, default=0.002)
    parser.add_argument('--out', type=Path, default=Path(__file__).resolve().parent)
    args = parser.parse_args()
    if args.end <= 8 or args.step <= 0:
        parser.error('end must exceed 8 and step must be positive')
    args.out.mkdir(parents=True, exist_ok=True)
    mp.mp.dps = 55
    # Character mod 3: principal (excluding powers of 3), and real nonprincipal.
    b0 = -mp.euler - 1 - mp.log(3)/2
    chi = [0, 1, -1]
    b1 = -mp.diff(lambda s: mp.dirichlet(s, chi), 1)/mp.dirichlet(1, chi)
    constants = {1: float((b0+b1)/2), 2: float((b0-b1)/2)}
    # No central zeros here: the eta series and the paired mod-3 series
    # are strictly positive at s=1/2 (zeta differs by a nonzero factor).
    lags = [0., math.log(2), math.log(3/2)]
    count = int(math.ceil((args.end-4)/args.step))
    ts = np.linspace(4, args.end, count, endpoint=False) + (args.end-4)/(2*count)
    limit = math.ceil(math.exp(args.end + max(lags)))
    ns, ws = prime_powers(limit)
    labels = [f'scale={math.exp(h):g}, a={a}' for h in lags for a in (1, 2)]
    z = np.column_stack([evaluate(a, np.exp(ts+h), ns, ws, constants[a]) for h in lags for a in (1,2)])
    stats = []
    for lo in [4., 6., 8.]:
        zz = z[ts >= lo]
        avg = zz.mean(axis=0)
        gram = zz.T @ zz / len(zz)
        cov = gram - np.outer(avg, avg)
        stats.append({'log_window': [lo, args.end], 'samples': len(zz),
                      'sample_mean': avg.tolist(), 'second_moment_eigenvalues': np.linalg.eigvalsh(gram).tolist(),
                      'empirical_covariance_eigenvalues': np.linalg.eigvalsh(cov).tolist(),
                      'second_moment': gram.tolist(), 'empirical_covariance': cov.tolist()})
    # Exact-integer check of the isolated-prime argument for these scales.
    # Ratios are rational: 1, 2, 3/2. Prime p>3 cannot collide with any
    # positive power of a prime at a different shifted location.
    from fractions import Fraction
    ratios = [Fraction(1), Fraction(2), Fraction(3,2)]
    pp = set(map(int, ns))
    # p=7 (class 1), p=5 (class 2), for each scale.
    witnesses = []
    for j, r in enumerate(ratios):
        for a, p in [(1,7),(2,5)]:
            assert p >= 2 and all(p % k != 0 for k in range(2, math.isqrt(p)+1)) and p % 3 == a
            other = [p*s/r for k,s in enumerate(ratios) if k != j]
            assert all(n.denominator != 1 or (int(n) <= limit and int(n) not in pp) for n in other)
            witnesses.append({'scale': str(r), 'class': a, 'prime': p,
                              'other_scale_arguments': [str(n) for n in other]})
    result = {'warning': 'Floating-point finite-window illustration; not a certified estimate of the limiting covariance.',
              'q':3, 'scales': [1,2,1.5], 'column_order': labels,
              'b_principal': str(b0), 'b_nonprincipal': str(b1),
              'class_constants': constants, 'sieve_limit':limit,
              'prime_power_count':len(ns), 'windows': stats, 'atom_witnesses':witnesses}
    (args.out/'numerical_results.json').write_text(json.dumps(result, indent=2)+'\n')
    with (args.out/'covariance_example.csv').open('w',newline='') as f:
        writer = csv.writer(f)
        writer.writerow(['empirical covariance, t in [4, '+str(args.end)+']']+labels)
        for label,row in zip(labels,stats[0]['empirical_covariance']):
            writer.writerow([label]+row)
    print(f'q=3; sieve limit={limit}; prime powers={len(ns)}')
    for item in stats:
        print('window',item['log_window'], 'n=',item['samples'],
              'covariance eigenvalues=', np.array(item['empirical_covariance_eigenvalues']))
    print('Six exact rational-shift prime-atom witnesses passed.')


if __name__ == '__main__':
    main()
