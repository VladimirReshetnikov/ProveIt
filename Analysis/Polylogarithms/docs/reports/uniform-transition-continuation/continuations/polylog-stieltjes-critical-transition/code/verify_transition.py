#!/usr/bin/env python3
"""Numerical diagnostics for the proved near-critical Euler transition.

The integral is the exact compensated comparison kernel, not its
large-order asymptotic. Every reported number is a floating-point
diagnostic, not a certified interval and not a premise of the proof.
The inner integral uses expm1 so division by tiny epsilon is stable.
"""
from __future__ import annotations
import argparse
import csv
import json
import math
from pathlib import Path
import warnings

from scipy.integrate import IntegrationWarning, quad
from scipy.optimize import brentq
from scipy.special import digamma, gamma, gammaln, lambertw, spence, zeta


def h_seed(T: float, b: int) -> float:
    """Exact h_b for b=1 or b=2 (Li_1 and Li_2 representations)."""
    q = math.exp(-T)
    h1 = -math.log1p(-q)
    if b == 1:
        return h1
    if b != 2:
        raise ValueError("This independent evaluator implements b=1,2 only.")
    if q < 0.2:
        li2 = 0.0
        qn = q
        n = 1
        while True:
            term = qn/(n*n)
            li2 += term
            if term <= abs(li2)*1e-17:
                break
            n += 1
            qn *= q
    else:
        li2 = float(spence(1-q))
    return li2 + T*h1


def constants(b: float, r: int = 0) -> tuple[float, float, float]:
    p = b+1
    K = (b*zeta(b+1, 1)*gamma(b+1)*
         math.exp(gammaln(r+0.5)-gammaln(r+1)))
    delta = (b-b*digamma(r+1)/2-digamma(r+0.5)/2-
             p*zeta(b+2, 1)/(2*zeta(b+1, 1)))
    return p, K, delta


def density_over_epsilon(T: float, eps: float, b: int,
                         tol: float = 1e-9) -> float:
    """Exact D_{1-eps,b}(T)/eps by a stable positive-integral formula."""
    a = 1-eps
    def fun(v: float) -> float:
        if v == 0:
            return 1/T if b == 1 else 0.0
        if v == T:
            # quad uses interior nodes; this branch guards roundoff only.
            v = math.nextafter(T, 0)
        u = -math.log1p(-v/T)
        return v**(b-1)/math.expm1(v)*math.expm1(eps*u)/eps
    # The cancellation-free integrand is positive. The endpoint is an
    # integrable power of exponent -eps; subdivisions expose that endpoint.
    split = min(T/2, 4.0)
    q0 = quad(fun, 0, split, epsabs=tol/T, epsrel=tol, limit=160)[0]
    q1 = quad(fun, split, T, epsabs=tol/T, epsrel=tol, limit=240)[0]
    seed = T**(-eps)/gamma(a)*(h_seed(T, b)/eps-(q0+q1)/gamma(b))
    bose = T**(b-eps)/(gamma(b+1-eps)*math.expm1(T)*eps)
    return seed+bose


def comparison_scaled(L: float, eps: float, b: int,
                      r: int = 0, tol: float = 1e-9) -> float:
    """(-1)^r s^(r+1/2) L Delta^(r)(s)/eps, s=exp(2L).

    Integration is cut at t=12, where the Gaussian tail is below 1e-60.
    This cutoff is a diagnostic choice, not an interval certificate.
    """
    s = math.exp(2*L)
    def fun(t: float) -> float:
        if t == 0:
            return 0.0
        T = L-math.log(t)
        if T <= 0:
            return 0.0
        x = t*t/s
        lp = -math.log1p(-x)
        weight = math.exp(-s*lp)/(1+x)*(s*lp)**r
        return -L*density_over_epsilon(T, eps, b, tol)*weight
    return sum(quad(fun, x, y, epsabs=tol, epsrel=tol,
                    limit=160)[0]
               for x,y in [(0,0.5),(0.5,1),(1,2),(2,4),(4,8),(8,12)])


def locate(eps: float, b: int, r: int = 0, tol: float = 1e-9) -> dict:
    lam = math.log(1/eps)
    p,K,delta = constants(b,r)
    base = lam+p*math.log(lam)-math.log(K)
    refined = base+(p*p*math.log(lam)-p*math.log(K)+delta)/lam
    lambert = -p*float(lambertw(-math.exp((math.log(K)-lam)/p)/p,-1).real)
    lambert_refined = lambert+delta/(lambert-p)
    lo,hi = base-2,refined+2
    flo=comparison_scaled(lo,eps,b,r,tol)
    fhi=comparison_scaled(hi,eps,b,r,tol)
    while flo*fhi > 0:
        lo-=2
        hi+=2
        flo=comparison_scaled(lo,eps,b,r,tol)
        fhi=comparison_scaled(hi,eps,b,r,tol)
    root=brentq(lambda L: comparison_scaled(L,eps,b,r,tol),lo,hi,
                xtol=tol,rtol=tol)
    lead_ratio=math.exp(2*(root-base))
    expected_first=2*(p*p*math.log(lam)-p*math.log(K)+delta)/lam
    return dict(b=b,r=r,epsilon=eps,lambda_=lam,L_root=root,
                log10_nu=2*root/math.log(10),L_leading=base,
                L_refined=refined,L_refined_error=root-refined,
                L_lambert=lambert,L_lambert_refined=lambert_refined,
                L_lambert_refined_error=root-lambert_refined,
                nu_over_leading=lead_ratio,
                first_relative_correction=expected_first,
                nu_over_first_order=lead_ratio/(1+expected_first),
                scaled_second_L_error=(root-refined)*lam*lam/(math.log(lam)**2),
                K=K,delta=delta,tolerance=tol)


def main() -> None:
    parser=argparse.ArgumentParser()
    parser.add_argument('--quick', action='store_true')
    parser.add_argument('--output',default=str(Path(__file__).resolve().parents[1]/'verification'/'transition_diagnostics.json'))
    args=parser.parse_args()
    samples=[(1,0,1e-4),(1,0,1e-8)] if args.quick else [
        (1,0,1e-3),(1,0,1e-6),(1,0,1e-12),(1,0,1e-24),
        (2,0,1e-6),(2,0,1e-12),(2,0,1e-24),
        (1,1,1e-12),(1,2,1e-12)]
    rows=[]
    warnings.simplefilter('error', IntegrationWarning)
    for b,r,eps in samples:
        row=locate(eps,b,r)
        rows.append(row)
        print(json.dumps(row),flush=True)
    # Recompute one root with a tighter quadrature target: an independent
    # numerical stability check of the evaluator, not interval arithmetic.
    check=locate(samples[0][2],samples[0][0],samples[0][1],2e-11)
    replay_difference=abs(check['L_root']-rows[0]['L_root'])
    out={'status':'floating-point diagnostics; not certified intervals',
         'exact_kernel':'D=(I^(1-eps)h_b)\u2032+T^(b-eps)/(Gamma(b+1-eps)(exp(T)-1))',
         'rows':rows,'tighter_replay':check,
         'tighter_replay_L_difference':replay_difference}
    path=Path(args.output)
    path.write_text(json.dumps(out,indent=2)+'\n')
    with path.with_suffix('.csv').open('w',newline='') as f:
        writer=csv.DictWriter(f,fieldnames=list(rows[0]))
        writer.writeheader(); writer.writerows(rows)


if __name__=='__main__':
    main()
