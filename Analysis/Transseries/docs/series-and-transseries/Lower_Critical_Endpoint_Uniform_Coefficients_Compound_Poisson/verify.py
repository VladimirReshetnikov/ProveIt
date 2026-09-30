#!/usr/bin/env python3
"""Reproducible checks for The Lower Critical Endpoint of Feedback Transseries.

Exact checks use fractions. Numerical checks use log-space recurrences and an
independent mpmath recurrence. They are diagnostics, not interval certificates.
Run: python verify.py --output verification_results.json
No network access is required.
"""
from __future__ import annotations
import argparse
import json
import math
import platform
from fractions import Fraction as F
from pathlib import Path
from typing import Iterator
import numpy as np
import scipy
from scipy.special import logsumexp
from scipy.integrate import quad
from scipy.optimize import brentq
import mpmath as mp


def exp_coeffs(a: list[F], multiplier: F, degree: int) -> list[F]:
    out = [F(1)] + [F(0)] * degree
    for k in range(1, degree + 1):
        out[k] = multiplier / k * sum(
            (j * a[j] * out[k-j] for j in range(1, min(k, len(a)-1)+1)), F(0))
    return out


def feedback_coeffs(a: list[F], degree: int) -> list[F]:
    u = [F(0)] * (degree + 1)
    for n in range(1, degree + 1):
        total = F(0)
        for j in range(1, min(n, len(a)-1)+1):
            ex = exp_coeffs(u, F(j), n-j)
            total += a[j] * ex[n-j]
        u[n] = total
    return u


def partitions(n: int, least: int = 1) -> Iterator[tuple[int, ...]]:
    if n == 0:
        yield ()
    else:
        for j in range(least, n+1):
            for rest in partitions(n-j, j):
                yield (j,) + rest


def exact_checks() -> dict:
    assertions = 0
    samples = []
    for family in range(3):
        N = 12
        a = [F(0)] + [F(1, j**(family+2)) for j in range(1, N+1)]
        if family == 1:
            a[1] += F(1, 2)
            a[2] -= F(1, 16)
        if family == 2:
            a[1] = F(2, 3)
            a[3] = F(0)
        u = feedback_coeffs(a, N)
        for n in range(1, N+1):
            coeff = exp_coeffs(a, F(n), n)[n] / n
            assert u[n] == coeff
            assertions += 1
        for n in range(1, 9):
            ex = exp_coeffs(a, F(n), n)
            total = F(0)
            counts = [F(0)] * (n+1)
            maximum_weights = [F(0)] * (n+1)
            for part in partitions(n):
                mult = {j: part.count(j) for j in set(part)}
                weight = F(1)
                for j, count in mult.items():
                    weight *= (n*a[j])**count / math.factorial(count)
                total += weight
                maximum_weights[max(part)] += weight
                for j, count in mult.items():
                    counts[j] += count*weight
            assert total == ex[n]
            assertions += 1
            for j in range(1, n+1):
                assert counts[j] == n*a[j]*ex[n-j]
                assertions += 1
            for M in range(1, n+1):
                trunc = a[:M+1]
                trunc_coefficient = exp_coeffs(trunc, F(n), n)[n]
                assert sum(maximum_weights[:M+1], F(0)) == trunc_coefficient
                assert 0 <= trunc_coefficient <= ex[n]
                assertions += 2
        samples.append({'family': family, 'u_1_to_5': [str(v) for v in u[1:6]]})
    # The endpoint first correction has J_2/J_0 -> 6 and zeta(0)=-1/2.
    assert F(-1, 2) * F(1, 2) * math.factorial(3) == F(-3, 2)
    assertions += 1
    return {'assertions_passed': assertions, 'samples': samples}


def params(eps: float, prefix: bool = False, dps: int = 70) -> dict:
    with mp.workdps(dps):
        e = mp.mpf(str(eps))
        alpha = 1 + e
        kappa = mp.mpf(3)/8 if prefix else mp.mpf(0)
        P1 = mp.mpf(7)/16 if prefix else mp.mpf(0)
        P2 = mp.mpf(1)/4 if prefix else mp.mpf(0)
        c = 1/(mp.zeta(alpha)+kappa)
        K = c*mp.gamma(-alpha)
        A1 = c*(mp.zeta(alpha+1)+P1)
        beta = 1/alpha
        J0 = beta/mp.gamma(1-beta)
        J2 = mp.gamma(3*beta)/(mp.pi*alpha)*mp.sin(3*mp.pi*e*beta)
        return dict(eps=float(e), alpha=float(alpha), c=float(c), K=float(K),
                    A1=float(A1), beta=float(beta), J0=float(J0), J2=float(J2),
                    D2=float(mp.zeta(e)+P2), prefix=prefix)


def log_probability_vector(n: int, eps: float, prefix: bool = False,
                           cutoff: int | None = None) -> tuple[np.ndarray, dict]:
    """Return log P(S=k, all jumps <= cutoff), k=0,...,n.

    The zero coefficient ALWAYS uses the full total intensity n*A(1),
    including when a cutoff is present. This is essential for cutoff ratios.
    """
    if n < 1 or eps <= 0:
        raise ValueError('n and eps must be positive')
    p = params(eps, prefix)
    M = n if cutoff is None else max(0, min(n, cutoff))
    j = np.arange(1, M+1, dtype=float)
    a = p['c'] * j**(-1-p['alpha'])
    if prefix and M >= 1:
        a[0] += p['c']/2
    if prefix and M >= 2:
        a[1] -= p['c']/16
    if np.any(a <= 0):
        raise ValueError('Numerical model contains nonpositive weights')
    log_ja = np.log(j*a)
    lp = np.full(n+1, -np.inf, dtype=float)
    lp[0] = -n*p['A1']
    for k in range(1, n+1):
        m = min(k, M)
        if m:
            lp[k] = math.log(n/k) + logsumexp(log_ja[:m] + lp[k-m:k][::-1])
    return lp, p


def coefficient_diagnostic(n: int, eps: float, prefix: bool = False) -> dict:
    lp, p = log_probability_vector(n, eps, prefix)
    B = (n*p['K'])**p['beta']
    lead = p['J0']/B
    correction = n*p['c']*p['D2']/(2*B*B)*p['J2']/p['J0']
    ratio = math.exp(lp[n]-math.log(lead))
    return {'n':n, 'eps':eps, 'prefix':prefix, 'B':B, 'n_eps':n*eps,
            'eps_log_n':eps*math.log(n), 'P_S_eq_n':math.exp(lp[n]),
            'leading_ratio':ratio, 'first_relative_correction':correction,
            'corrected_ratio':ratio/(1+correction),
            'observed_correction_over_predicted':(ratio-1)/correction}


def independent_mp_check(n: int = 100, eps: str = '0.05') -> dict:
    with mp.workdps(80):
        e = mp.mpf(eps)
        c = 1/mp.zeta(1+e)
        A1 = c*mp.zeta(2+e)
        a = [mp.mpf(0)] + [c/mp.mpf(j)**(2+e) for j in range(1,n+1)]
        prob = [mp.exp(-n*A1)] + [mp.mpf(0)]*n
        for k in range(1,n+1):
            prob[k] = mp.mpf(n)/k*mp.fsum(j*a[j]*prob[k-j] for j in range(1,k+1))
        lp, _ = log_probability_vector(n, float(e))
        relative = abs(mp.exp(float(lp[n]))/prob[n]-1)
        assert relative < mp.mpf('1e-11')
        return {'n':n, 'eps':eps, 'mp_dps':80, 'probability':mp.nstr(prob[n],65),
                'relative_difference_logspace':float(relative)}


def landau_cdf(x: float) -> float:
    # Characteristic function exp(-pi |t|/2 - i t log |t|).
    def integrand(t: float) -> float:
        if t == 0:
            return 0.0  # Only a measure-zero endpoint; quad does not evaluate it.
        return math.exp(-math.pi*t/2)*math.sin(t*(x+math.log(t)))/t
    val = quad(integrand, 0, 1, epsabs=2e-11, limit=300)[0]
    val += quad(integrand, 1, 35, epsabs=2e-11, limit=500)[0]
    return .5+val/math.pi


def reflected_landau_cdf(z: float) -> float:
    return 1-landau_cdf(-z)


def landau_cutoff_checks() -> dict:
    quantiles = {str(eta): brentq(lambda z: reflected_landau_cdf(z)-eta,
                                -100, 30, xtol=1e-10)
                 for eta in [0.1, 0.5, 0.9]}
    rows = []
    # Finite epsilon corrections can be substantial; no convergence rate is asserted.
    for n, eps in [(1024,.08),(4096,.04),(8192,.02)]:
        lp, p = log_probability_vector(n, eps)
        B = (n*p['K'])**p['beta']
        for z in [-2., 0., 2.]:
            M = math.floor(B+eps*B*(z-math.log(eps)))
            lpt, _ = log_probability_vector(n, eps, cutoff=M)
            ratio = math.exp(lpt[n]-lp[n])
            rows.append({'n':n,'eps':eps,'z':z,'M':M,
                         'retained_fraction':ratio,
                         'limiting_G':reflected_landau_cdf(z)})
    return {'quantiles_G':quantiles, 'cutoff_diagnostics':rows,
            'warning':'Quadrature and recurrences use floating point, not directed rounding.'}


def poisson_cloud_checks() -> list[dict]:
    rows = []
    for prefix in [False, True]:
        for lam in [.5, 2.]:
            Kmax = 15
            H1 = math.pi**2/6 + (7/16 if prefix else 0)
            b = np.array([0.] + [1/j**2 for j in range(1,Kmax+1)])
            if prefix:
                b[1] += .5; b[2] -= 1/16
            cloud = np.zeros(Kmax+1)
            cloud[0] = math.exp(-lam*H1)
            for k in range(1,Kmax+1):
                cloud[k] = lam/k*sum(j*b[j]*cloud[k-j] for j in range(1,k+1))
            for n in [512,2048]:
                eps = lam/n
                lp, p = log_probability_vector(n,eps,prefix)
                observed = np.array([math.exp(math.log(n*p['c'])-(2+eps)*math.log(n-k)
                                              + lp[k]-lp[n]) for k in range(Kmax+1)])
                rows.append({'n':n,'eps':eps,'lambda':lam,'prefix':prefix,
                             'max_abs_error_k_0_to_15':float(np.max(abs(observed-cloud))),
                             'P_deficit_0_observed':float(observed[0]),
                             'P_cloud_0_limit':float(cloud[0])})
    return rows


def contour_moment_checks() -> list[dict]:
    rows=[]
    with mp.workdps(55):
        for e_text in ['0.2','0.05','0.001']:
            e=mp.mpf(e_text); alpha=1+e
            for r in [0,2,3,4]:
                exact=mp.gamma((r+1)/alpha)/(mp.pi*alpha)*mp.sin(mp.pi*e*(r+1)/alpha)
                # Scale y=s^alpha to avoid poor integration of a tiny oscillation.
                f=lambda y: y**((r+1)/alpha-1)*mp.exp(-mp.cos(mp.pi*e)*y)*mp.sin(mp.sin(mp.pi*e)*y)/(mp.pi*alpha)
                integral=mp.quad(f,[0,1,4,16,64,mp.inf])
                err=abs(integral-exact)
                assert err < mp.mpf('1e-38')
                rows.append({'eps':e_text,'r':r,'absolute_error':float(err)})
    return rows


def main() -> None:
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',default='verification_results.json')
    parser.add_argument('--quick',action='store_true',help='Omit the larger cutoff diagnostics')
    args=parser.parse_args()
    result={'title':'Lower critical endpoint verification',
            'versions':{'python':platform.python_version(),'numpy':np.__version__,
                        'scipy':scipy.__version__,'mpmath':mp.__version__},
            'status':'exact finite checks plus numerical diagnostics; no formal or interval certification'}
    result['exact']=exact_checks()
    result['independent_multiprecision']=independent_mp_check()
    result['contour_moments']=contour_moment_checks()
    result['coefficients']=[coefficient_diagnostic(n,e,prefix)
                            for prefix in [False,True]
                            for e in [.2,.05,.005]
                            for n in [128,512,2048]]
    result['poisson_cloud']=poisson_cloud_checks()
    if not args.quick:
        result['landau']=landau_cutoff_checks()
    output=Path(args.output)
    output.write_text(json.dumps(result,indent=2,allow_nan=False)+'\n',encoding='utf-8')
    print(f"Exact assertions passed: {result['exact']['assertions_passed']}")
    print(f"Independent high-precision relative difference: {result['independent_multiprecision']['relative_difference_logspace']:.3g}")
    print(f"Wrote {output}")

if __name__=='__main__':
    main()
