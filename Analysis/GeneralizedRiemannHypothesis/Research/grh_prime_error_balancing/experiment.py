#!/usr/bin/env python3
"""Illustrative q=4 convex balancing and zero-annihilating kernels.

Requires numpy, scipy, mpmath. Floating-point, NOT interval-certified.
Run from any directory; results written next to this script.
"""
import csv
import itertools
import json
import math
from pathlib import Path
import mpmath as mp
import numpy as np
from scipy.spatial import ConvexHull

ROOT = Path(__file__).resolve().parent


def mangoldt_sieve(n):
    isprime = np.ones(n + 1, dtype=bool)
    isprime[:2] = False
    for p in range(2, math.isqrt(n) + 1):
        if isprime[p]:
            isprime[p*p::p] = False
    lam = np.zeros(n + 1)
    for p in np.flatnonzero(isprime):
        p = int(p)
        k = p
        while k <= n:
            lam[k] = math.log(p)
            k *= p
    return lam


def q4_values(xs):
    """Ramps using two prefix sums; B from the regular Dirichlet-series part."""
    n = int(np.max(xs))
    lam = mangoldt_sieve(n)
    ints = np.arange(n + 1)
    safe = np.maximum(ints, 1)
    mp.mp.dps = 45
    beta = lambda s: mp.dirichlet(s, [0, 1, 0, -1])
    # -L'/L of the principal char modulo 4 has regular part -gamma-log 2.
    b0 = -mp.euler - mp.log(2)
    beta1 = mp.pi/4
    beta_prime = (mp.stieltjes(1, mp.mpf('0.75')) - mp.stieltjes(1, mp.mpf('0.25')))/4 - mp.log(4)*beta1
    b1 = -beta_prime / beta1
    constants = [(b0 + b1)/2, (b0 - b1)/2]
    result = []
    for a, B in zip((1, 3), constants):
        coeff = lam * (ints % 4 == a)
        p1 = np.cumsum(coeff / safe)
        p2 = np.cumsum(coeff)
        idx = xs.astype(int)
        R = p1[idx] - p2[idx]/xs - np.log(xs)/2 - float(B) + 0.5
        result.append(np.sqrt(xs)*R)
    return np.stack(result, axis=1), [mp.nstr(c, 35) for c in constants]


def best_triangle(points):
    hull = ConvexHull(points)
    # Each facet equation is n*x + offset <= 0. For an interior origin,
    # the minimum distance to the boundary is the negative maximum offset.
    margin = float(-np.max(hull.equations[:, -1]))
    best = None
    for tri in itertools.combinations(hull.vertices.tolist(), 3):
        mat = np.vstack([points[list(tri)].T, np.ones(3)])
        try:
            w = np.linalg.solve(mat, np.array([0., 0., 1.]))
        except np.linalg.LinAlgError:
            continue
        if min(w) > 0 and (best is None or min(w) > min(best[1])):
            best = (tri, w)
    if best is None:
        return None, None, margin
    assert margin > 0
    return *best, margin


def run_balance():
    samples = []
    summary = []
    for X in (1000, 10000, 100000, 1000000):
        H = 1.5
        xs = X*np.exp(np.linspace(-H, H, 601))
        points, Bs = q4_values(xs)
        tri, w, margin = best_triangle(points)
        residual = w @ points[list(tri)] if tri is not None else None
        if residual is not None:
            assert np.max(np.abs(residual)) < 1e-12
        summary.append({"X": X, "H": H, "sample_count": len(xs),
                        "B1_B3": Bs, "signed_sampled_hull_margin_at_zero": margin,
                        "origin_in_sampled_hull": margin > 0,
                        "nodes": [{"x": float(xs[i]), "F1": float(points[i,0]),
                                   "F3": float(points[i,1]), "weight": float(weight)}
                                  for i, weight in zip(tri, w)] if tri is not None else [],
                        "weighted_vector": residual.tolist() if residual is not None else None})
        samples.extend((X, float(x), float(f[0]), float(f[1])) for x,f in zip(xs,points))
    with (ROOT/'q4_samples.csv').open('w',newline='') as f:
        writer=csv.writer(f)
        writer.writerow(['window_center_X','x','sqrt_x_R_1','sqrt_x_R_3'])
        writer.writerows(samples)
    return summary


def run_kernel():
    # Numerical illustrations only; no assertion that these are certified zeros.
    mp.mp.dps = 40
    gammas = [mp.im(mp.zetazero(i)) for i in range(1, 13)]
    H = mp.pi*sum(1/g for g in gammas)
    def hat(omega):
        return mp.fprod(mp.sin(mp.pi*omega/g)/(mp.pi*omega/g) for g in gammas)
    low_max = max(abs(hat(g)) for g in gammas)
    B = gammas[-1]
    high = [(str(mp.nstr(mult*B, 20)), str(mp.nstr(abs(hat(mult*B)), 12)))
            for mult in [mp.mpf('1.01'),mp.mpf('1.1'),mp.mpf('1.5'),mp.mpf(2)]]
    bound = mp.pi**(-len(gammas))
    assert low_max < mp.mpf('1e-35')
    assert all(mp.mpf(val) <= bound for _, val in high)
    return {"positive_zeta_ordinates": [mp.nstr(g,25) for g in gammas],
            "support_half_width": mp.nstr(H,20), "cutoff": mp.nstr(B,20),
            "maximum_low_frequency_residual": mp.nstr(low_max,10),
            "uniform_high_frequency_bound": mp.nstr(bound,15),
            "sample_high_frequency_values": high,
            "note": "One factor per positive ordinate, without duplicate negative ordinates; the proof permits this too."}


if __name__ == '__main__':
    data = {"status": "floating-point illustration only", "q4": run_balance(),
            "kernel": run_kernel()}
    (ROOT/'experiment_results.json').write_text(json.dumps(data,indent=2)+'\n')
    for row in data['q4']:
        print(f"X={row['X']}: signed margin={row['signed_sampled_hull_margin_at_zero']:.8g}; "
              f"weights={[round(n['weight'],7) for n in row['nodes']]}; "
              f"residual={row['weighted_vector']}")
    print('Kernel:', data['kernel']['support_half_width'], data['kernel']['uniform_high_frequency_bound'])
