#!/usr/bin/env python3
"""Reproduce exact counts and numerical CDFs for nested-cycle assemblies.

Finite count checks use integers and fractions. Fourier integration uses
ordinary double precision and is numerical evidence, not a proof certificate.
The mathematical error estimates are proved separately in the article.
"""
from __future__ import annotations

import argparse
import csv
import json
import math
from fractions import Fraction
from pathlib import Path

import numpy as np
from numpy.polynomial.legendre import leggauss
from scipy.optimize import brentq
from scipy.special import exp1

C = math.exp(-float(np.euler_gamma))
KAPPA = (2 + math.sqrt(5)) * math.exp(-(3 + math.sqrt(5)) / 2)


def nested_weights(limit: int) -> np.ndarray:
    """Coefficients through limit of product (1+z**k/k), in float64."""
    p = np.zeros(limit + 1)
    p[0] = 1.0
    for k in range(1, limit + 1):
        # RHS is a fresh array: each factor is used once, not repeatedly.
        p[k:] += p[:-k] / k
    return p


def exact_counts(limit: int, max_component: int | None = None) -> list[int]:
    """Integer assembly counts from exact rational component coefficients."""
    p = [Fraction(0) for _ in range(limit + 1)]
    p[0] = Fraction(1)
    for k in range(1, limit + 1):
        for j in range(limit, k - 1, -1):
            p[j] += p[j - k] / k
    component = [int(p[k] * math.factorial(k)) for k in range(limit + 1)]
    assert all(p[k] * math.factorial(k) == component[k] for k in range(limit + 1))
    a = [1] + [0] * limit
    cap = limit if max_component is None else max_component
    for n in range(1, limit + 1):
        a[n] = sum(math.comb(n - 1, k - 1) * component[k] * a[n - k]
                   for k in range(1, min(n, cap) + 1))
    return a


def approximations(x: np.ndarray, tau: float, c: float = C) -> dict[str, np.ndarray]:
    """Gumbel, leading, smooth, lattice, and component-sensitive formulas."""
    L = math.log(c / tau)
    beta = np.exp(-x)
    G = np.exp(-beta)
    q = L + x
    eps = tau / (4 * c)
    delta = eps * L * L
    first = G + delta * G * beta * (1 - beta)
    h = x + eps * (q*q-q-1-beta*(q+1)**2)
    smooth = np.exp(-np.exp(-h))
    polynomial = eps * G * ((beta-beta*beta)*q*q
                            - (beta+2*beta*beta)*q-beta-beta*beta)
    phase = np.mod(q / tau, 1.0)
    # Avoid floating-point phases near a mathematically exact lattice point.
    phase = np.where(np.minimum(phase, 1-phase) < 1e-8, 0.0, phase)
    lattice = G + polynomial + tau * (0.5-phase) * G * beta
    sensitive = lattice - c * G * exp1(np.maximum(1.0, q))
    return dict(gumbel=G, leading=first, smooth=smooth,
                lattice=lattice, sensitive=sensitive)


def fourier_cdf(n: int, p: np.ndarray, m: np.ndarray, nodes: int = 256,
                radius: float | None = 14.0) -> tuple[float, np.ndarray, dict]:
    """Centered Fourier quadrature for P(M<=m | total=n).

    p has a finite tail cutoff. Its exponentially small omitted contribution
    is assessed numerically by the caller; it is not interval-certified.
    """
    k = np.arange(1, len(p), dtype=float)
    w = p[1:]
    t0 = math.sqrt(C / n)
    tau = brentq(lambda t: float(np.dot(k*w, np.exp(-t*k))) - n,
                 0.5*t0, 2*t0, xtol=1e-15, rtol=1e-14)
    a = w * np.exp(-tau*k)
    total0 = float(a.sum())
    total1 = float(np.dot(k, a))
    variance = float(np.dot(k*k, a))
    if radius is None:
        radius = math.pi*math.sqrt(variance)
    u, weight = leggauss(nodes)
    u *= radius
    weight *= radius
    theta = u / math.sqrt(variance)
    # A few million terms are evaluated in a vectorized stable form.
    mat = a[:, None] * (np.expm1(1j*k[:, None]*theta[None, :])
                        - 1j*k[:, None]*theta[None, :])
    np.cumsum(mat, axis=0, out=mat)
    partial0 = np.cumsum(a)
    partial1 = np.cumsum(k*a)
    denominator = float(np.dot(weight, np.exp(mat[-1]).real))
    out = np.empty(len(m), dtype=float)
    for j, cutoff in enumerate(m):
        cutoff = int(cutoff)
        if cutoff < 1:
            out[j] = 0.0
        elif cutoff >= n:
            out[j] = 1.0
        else:
            if cutoff >= len(p):
                raise ValueError('The coefficient cutoff is too short.')
            exponent = mat[cutoff-1] + 1j*(partial1[cutoff-1]-total1)*theta
            numerator = float(np.dot(weight, np.exp(exponent).real))
            out[j] = math.exp(-(total0-partial0[cutoff-1]))*numerator/denominator
    meta = dict(tau=tau, variance=variance, denominator=denominator,
                coefficient_cutoff=len(p)-1, quadrature_nodes=nodes,
                quadrature_radius=radius, final_weight=float(a[-1]))
    return tau, out, meta


def verify_exact() -> dict:
    expected = [1,1,2,9,44,270,2064,17682,171296,1867968,22470840,
                294493320,4195969392,64416698112,1059685905264,
                18609306423120,347179119075840,6855335163907200,
                142889687354283264,3133647091691585280,
                72124075333003155840,1738384773846440146560]
    got = exact_counts(len(expected)-1)
    assert got == expected
    n = 50
    p = nested_weights(1800)
    ms = np.array([8,12,16,20,25,30])
    _, cdf1, _ = fourier_cdf(n, p, ms, nodes=2048, radius=None)
    full = exact_counts(n)[n]
    rational_values = [Fraction(exact_counts(n, int(m))[n], full) for m in ms]
    err = float(np.max(np.abs(cdf1-np.array([float(v) for v in rational_values]))))
    assert err < 2e-10, err
    # A separate coefficient recurrence checks the truncated central
    # Fourier arc at a larger n.  The recurrence is evaluated in float64;
    # it is an independent numerical calculation, not an exact certificate.
    check_n = 1000
    check_ms = np.array([65,90,115,140,180,250])
    check_tau, integral_values, _ = fourier_cdf(check_n, p, check_ms)
    ak = p[1:check_n+1] * np.exp(-check_tau*np.arange(1,check_n+1))
    ka = np.arange(1,check_n+1)*ak

    def tilted_coefficient(cap: int) -> float:
        coefficient = np.zeros(check_n+1)
        coefficient[0] = 1.0
        for j in range(1,check_n+1):
            length = min(j,cap)
            coefficient[j] = np.dot(ka[:length],coefficient[j-length:j][::-1])/j
        return float(coefficient[-1])

    denominator = tilted_coefficient(check_n)
    recurrent_values = np.array([tilted_coefficient(int(m))/denominator for m in check_ms])
    recurrence_error = float(np.max(np.abs(recurrent_values-integral_values)))
    assert recurrence_error < 3e-9, recurrence_error
    return dict(oeis_initial_values_checked=len(expected),
                exact_cdf_size=n, exact_cdf_cutoffs=ms.tolist(),
                max_fourier_vs_exact_error=err,
                exact_cdf_fractions=[str(v) for v in rational_values],
                floating_recurrence_size=check_n,
                floating_recurrence_cutoffs=check_ms.tolist(),
                max_core_fourier_vs_recurrence_error=recurrence_error)


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument('--sizes', nargs='+', type=int, default=[1000,10000,100000])
    parser.add_argument('--out', type=Path, default=Path(__file__).resolve().parents[1]/'data')
    args = parser.parse_args()
    args.out.mkdir(parents=True, exist_ok=True)
    checks = verify_exact()
    cutoff = math.ceil(45/math.sqrt(C/max(args.sizes)))
    p = nested_weights(max(cutoff, 1800))
    rows = []
    details = []
    profile = None
    for n in args.sizes:
        t0 = math.sqrt(C/n)
        L0 = math.log(C/t0)
        # Every integer threshold in the relevant window is used.
        ms = np.arange(max(1, int((L0-3.3)/t0)), min(n, int((L0+9)/t0))+1)
        tau, F, meta = fourier_cdf(n,p,ms,nodes=256)
        _, F2, _ = fourier_cdf(n,p,ms[::max(1,len(ms)//60)],nodes=384)
        qerr = float(np.max(np.abs(F[::max(1,len(ms)//60)]-F2)))
        x = tau*ms-math.log(C/tau)
        approx = approximations(x,tau)
        delta = tau*math.log(C/tau)**2/(4*C)
        next_approx = approximations(x+tau,tau)
        row = dict(n=n,tau=tau,L=math.log(C/tau),delta=delta,
                   raw_error=float(max(np.max(np.abs(F-approx['gumbel'])),
                                       np.max(np.abs(F-next_approx['gumbel'])))),
                   leading_error=float(np.max(np.abs(F-approx['leading']))),
                   smooth_error=float(max(np.max(np.abs(F-approx['smooth'])),
                                          np.max(np.abs(F-next_approx['smooth'])))),
                   lattice_error=float(np.max(np.abs(F-approx['lattice']))),
                   sensitive_error=float(np.max(np.abs(F-approx['sensitive']))),
                   quadrature_difference=qerr)
        row['raw_over_predicted'] = row['raw_error']/(delta*KAPPA)
        row['smooth_over_tau'] = row['smooth_error']/tau
        row['smooth_over_optimal'] = row['smooth_error']/(tau/(2*math.e))
        rows.append(row)
        details.append(meta)
        if n == max(args.sizes):
            stride = max(1,len(ms)//2000)
            profile = [dict(m=int(ms[j]),x=float(x[j]),cdf=float(F[j]),
                            **{key:float(value[j]) for key,value in approx.items()})
                       for j in range(0,len(ms),stride)]
    with (args.out/'nested_errors.csv').open('w',newline='') as f:
        writer=csv.DictWriter(f,fieldnames=list(rows[0]));writer.writeheader();writer.writerows(rows)
    with (args.out/'nested_profile.csv').open('w',newline='') as f:
        writer=csv.DictWriter(f,fieldnames=list(profile[0]));writer.writeheader();writer.writerows(profile)
    checks.update(numerical_runs=details,roundoff_not_certified=True,
                  model='nested cycle assemblies; numerical finite-product coefficients in float64')
    (args.out/'verification.json').write_text(json.dumps(checks,indent=2)+'\n')
    print(json.dumps(dict(checks=checks,results=rows),indent=2))


if __name__ == '__main__':
    main()
