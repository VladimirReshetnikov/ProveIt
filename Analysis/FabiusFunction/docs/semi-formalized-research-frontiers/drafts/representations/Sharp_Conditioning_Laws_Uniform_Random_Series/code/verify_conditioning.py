#!/usr/bin/env python3
"""Reproducible checks for Sharp Conditioning Laws for Uniform Random Series.

The finite-simplex formulas are exact mathematical identities evaluated in
floating point.  Geometric-series simulations are finite, floating-point
experiments, NOT a certified implementation of the article's lazy exact sampler.
No external data or network access is needed.
"""
from __future__ import annotations

import argparse
import csv
import json
import math
import platform
from pathlib import Path
from typing import Any

import numpy as np
import scipy
from scipy import integrate, optimize, special, stats
import sympy as sp

ROOT = Path(__file__).resolve().parents[1]


def mean_variance(a: np.ndarray | float) -> tuple[np.ndarray, np.ndarray]:
    """Stable mean and variance of Exp(1) truncated to [0,a], a>0."""
    a = np.asarray(a, dtype=float)
    if np.any(a <= 0) or np.any(~np.isfinite(a)):
        raise ValueError("Every truncation width must be positive and finite.")
    mu, var = np.empty_like(a), np.empty_like(a)
    small, large = a < 0.03, a > 50.0
    middle = ~(small | large)
    x = a[small]
    # Terms through a^8; the omitted terms are negligible at this cutoff.
    mu[small] = x / 2 - x**2 / 12 + x**4 / 720 - x**6 / 30240 + x**8 / 1209600
    var[small] = x**2 / 12 - x**4 / 240 + x**6 / 6048 - x**8 / 172800
    x = a[middle]
    denominator = np.expm1(x)
    mu[middle] = 1 - x / denominator
    var[middle] = 1 - x*x * np.exp(x) / denominator**2
    x = a[large]
    z = np.exp(-x)
    mu[large] = 1 - x*z / (1-z)
    var[large] = 1 - x*x*z / (1-z)**2
    return mu, var


def limiting_tv(alpha: float) -> float:
    if not 0 <= alpha <= 1:
        raise ValueError("alpha must lie in [0,1].")
    if alpha == 0:
        return 0.0
    if alpha == 1:
        return 1.0
    d = math.sqrt(-math.log1p(-alpha) / alpha)
    return float(2 * (special.ndtr(d) - special.ndtr(math.sqrt(1-alpha)*d)))


def limiting_kl(alpha: float) -> float:
    if not 0 <= alpha <= 1:
        raise ValueError("alpha must lie in [0,1].")
    return math.inf if alpha == 1 else (-math.log1p(-alpha)-alpha)/2


def simplex_values(n: int, k: int) -> dict[str, float | int]:
    """Exact-formula TV and KL: uniform n-simplex vs k independent exponentials."""
    if not 1 <= k < n:
        raise ValueError("Require 1 <= k < n.")
    constant = float(special.gammaln(n+1)-special.gammaln(n-k+1)-k*math.log(n))

    def log_ratio(s: float) -> float:
        if s >= n:
            return -math.inf
        return constant + s + (n-k)*math.log1p(-s/n)

    lower = 0.0 if k == 1 else optimize.brentq(log_ratio, 0.0, float(k), xtol=1e-12)
    upper = optimize.brentq(log_ratio, float(k), np.nextafter(float(n), 0.0), xtol=1e-12)
    p_interval = stats.beta.cdf(upper/n, k, n+1-k)-stats.beta.cdf(lower/n, k, n+1-k)
    q_interval = stats.gamma.cdf(upper, k)-stats.gamma.cdf(lower, k)
    tv = float(p_interval-q_interval)
    kl = float(constant+n*k/(n+1)+(n-k)*(special.digamma(n-k+1)-special.digamma(n+1)))
    return dict(n=n, k=k, alpha=k/n, tv=tv, tv_limit=limiting_tv(k/n),
                kl=kl, kl_limit=limiting_kl(k/n), lower_root=lower, upper_root=upper)


def write_csv(path: Path, rows: list[dict[str, Any]]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    if not rows:
        raise ValueError("Refusing to write a table without rows.")
    with path.open("w", newline="", encoding="utf-8") as out:
        writer = csv.DictWriter(out, fieldnames=list(rows[0]), lineterminator="\n")
        writer.writeheader()
        writer.writerows(rows)


def exact_checks() -> dict[str, Any]:
    a = sp.symbols("a", positive=True)
    mu = 1-a/(sp.exp(a)-1)
    var = 1-a*a*sp.exp(a)/(sp.exp(a)-1)**2
    assert sp.simplify(mu-a*sp.diff(mu,a)-var) == 0
    assert sp.series(mu, a, 0, 8).removeO() == a/2-a**2/12+a**4/720-a**6/30240
    assert sp.series(var, a, 0, 8).removeO() == a**2/12-a**4/240+a**6/6048
    y = sp.symbols("y", nonnegative=True)
    assert sp.simplify(sp.integrate(sp.exp(-y), (y,0,a))/(1-sp.exp(-a))) == 1
    assert sp.simplify(sp.integrate(y*sp.exp(-y), (y,0,a))/(1-sp.exp(-a))-mu) == 0
    # Polynomial marginal densities of the uniform simplex normalize exactly.
    simplex_checks = 0
    s = sp.symbols("s", nonnegative=True)
    for n in range(2,10):
        for k in range(1,n):
            density = sp.factorial(n) * s**(k-1) * (n-s)**(n-k) / (
                sp.factorial(k-1)*sp.factorial(n-k)*n**n)
            assert sp.integrate(density,(s,0,n)) == 1
            assert sp.integrate(s*density,(s,0,n)) == sp.Rational(n*k,n+1)
            simplex_checks += 2
    # Compare the special-function formulas to direct one-dimensional quadrature.
    max_tv_error = max_kl_error = 0.0
    for n,k in [(4,1),(8,3),(16,8),(32,24)]:
        values = simplex_values(n,k)
        c = float(special.gammaln(n+1)-special.gammaln(n-k+1)-k*math.log(n))
        def p_density(s: float) -> float:
            return float(stats.beta.pdf(s/n,k,n+1-k)/n) if 0<s<n else 0.0
        def integrand_kl(s: float) -> float:
            if s<=0 or s>=n:
                return 0.0
            return p_density(s)*(c+s+(n-k)*math.log1p(-s/n))
        kl_quad = integrate.quad(integrand_kl,0,n,epsabs=2e-11)[0]
        lo,hi = float(values['lower_root']),float(values['upper_root'])
        tv_quad = integrate.quad(lambda s:p_density(s)-stats.gamma.pdf(s,k),lo,hi,
                                 epsabs=2e-11)[0]
        max_tv_error = max(max_tv_error,abs(tv_quad-float(values['tv'])))
        max_kl_error = max(max_kl_error,abs(kl_quad-float(values['kl'])))
    assert max_tv_error < 2e-10
    assert max_kl_error < 2e-9
    # Check moment computation on small, moderate, and large widths.
    max_moment_error = 0.0
    for width in [1e-5,0.01,0.029,0.031,0.2,1.0,5.0,40.0,60.0]:
        m,v = mean_variance(width)
        # Integrate on u in [0,1], avoiding a tiny integration interval.
        denominator = -math.expm1(-width)
        mean_quad = integrate.quad(lambda u: width*u*width*math.exp(-width*u)/denominator,0,1,
                                   epsabs=2e-12)[0]
        var_quad = integrate.quad(lambda u: (width*u-float(m))**2*width*math.exp(-width*u)/denominator,
                                  0,1,epsabs=2e-12)[0]
        max_moment_error = max(max_moment_error,abs(float(m)-mean_quad),abs(float(v)-var_quad))
    assert max_moment_error < 1e-10
    result = {
        "symbolic_identities_passed":5,
        "exact_simplex_integrals_passed":simplex_checks,
        "max_tv_quadrature_error":max_tv_error,
        "max_kl_quadrature_error":max_kl_error,
        "max_moment_quadrature_error":max_moment_error,
        "status":"PASS",
        "scope":"Exact algebra and floating-point diagnostics, not formal proof verification."
    }
    (ROOT/'data'/'verification.json').write_text(json.dumps(result,indent=2)+'\n')
    return result


def simplex_table() -> list[dict[str,Any]]:
    rows = [simplex_values(n,max(1,int(round(alpha*n))))
            for n in [32,128,512,2048] for alpha in [0.1,0.25,0.5,0.75,0.9]]
    write_csv(ROOT/'data'/'simplex_comparison.csv',rows)
    return rows


def geometric_experiment(n: int, proposals: int=160000, seed: int=280926,
                         q: float=0.5, rho: float=1.25, batch_size: int=1000) -> dict[str,Any]:
    if n<4 or proposals<100 or not 0<q<1 or not 1<=rho<1/q:
        raise ValueError("Invalid experiment parameters.")
    # a_k = rho*q^(k-n); residual sum of widths after cutoff is below 2e-13.
    extra = max(1,math.ceil(math.log(2e-13*(1-q)/rho)/math.log(q)))
    indices = np.arange(1,n+extra+1)
    widths = rho*np.exp((indices-n)*math.log(q))
    mu,var = mean_variance(widths)
    m, V = float(mu.sum()),float(var.sum())
    residual_bound = float(rho*q**(extra+1)/(1-q))
    rng = np.random.default_rng(seed+n)
    centered_paths: list[np.ndarray] = []
    slacks: list[np.ndarray] = []
    boundary: list[np.ndarray] = []
    accepted = 0
    grid = [n//4,n//2,3*n//4]
    prefix_means = np.array([mu[:k].sum() for k in grid])
    mass = -np.expm1(-widths)
    for start in range(0,proposals,batch_size):
        count = min(batch_size,proposals-start)
        y = -np.log1p(-rng.random((count,len(widths)))*mass)
        total = y.sum(axis=1)
        z = total-m
        ok = (z<=0) & (np.log(rng.random(count))<=z)
        count_ok = int(ok.sum())
        accepted += count_ok
        if count_ok:
            yy=y[ok]
            slacks.append(-z[ok])
            centered_paths.append((np.column_stack([yy[:,:k].sum(axis=1) for k in grid])-prefix_means)/math.sqrt(n))
            boundary.append(yy[:,n-1]/rho)
    if accepted < 30:
        raise RuntimeError("Too few accepted samples; increase proposals.")
    d=np.concatenate(slacks); b=np.concatenate(centered_paths); u=np.concatenate(boundary)
    acceptance=accepted/proposals
    cov=np.cov(b,rowvar=False,ddof=1)
    boundary_mean=float(mean_variance(rho)[0]/rho)
    result={"n":n,"q":q,"rho":rho,"proposals":proposals,"accepted":accepted,
            "tilted_mean":m,"tilted_variance":V,"acceptance":acceptance,
            "acceptance_se":math.sqrt(acceptance*(1-acceptance)/proposals),
            "acceptance_asymptotic":1/math.sqrt(2*math.pi*V),
            "slack_mean":float(d.mean()),"slack_mean_se":float(d.std(ddof=1)/math.sqrt(accepted)),
            "slack_variance":float(d.var(ddof=1)),
            "bridge_variance_quarter":float(cov[0,0]),
            "bridge_variance_half":float(cov[1,1]),
            "bridge_variance_three_quarters":float(cov[2,2]),
            "bridge_covariance_quarter_half":float(cov[0,1]),
            "bridge_covariance_quarter_three_quarters":float(cov[0,2]),
            "boundary_mean":float(u.mean()),"boundary_mean_se":float(u.std(ddof=1)/math.sqrt(accepted)),
            "boundary_mean_limit":boundary_mean,"scaled_tail_width_bound":residual_bound,
            "seed":seed+n}
    return result


def experiments(proposals: int=160000) -> list[dict[str,Any]]:
    rows=[]
    for n in [32,128,512]:
        rows.append(geometric_experiment(n,proposals=proposals))
    write_csv(ROOT/'data'/'geometric_experiments.csv',rows)
    versions={"python":platform.python_version(),"numpy":np.__version__,
              "scipy":scipy.__version__,"sympy":sp.__version__,
              "proposals_per_n":proposals,"seed_base":280926}
    (ROOT/'data'/'environment.json').write_text(json.dumps(versions,indent=2)+'\n')
    return rows


def make_figures() -> None:
    """One plot per figure; no color or style overrides."""
    import matplotlib
    matplotlib.use('Agg')
    matplotlib.rcParams['pdf.fonttype'] = 42
    import matplotlib.pyplot as plt
    with (ROOT/'data'/'simplex_comparison.csv').open() as handle:
        rows=list(csv.DictReader(handle))
    alphas=np.linspace(0,0.99,300)
    for field,label,title in [('tv','Total variation distance','Exact variance-fraction profile'),
                              ('kl','Relative entropy (nats)','Information cost of conditioning')]:
        fig,ax=plt.subplots(figsize=(6.8,4.4))
        fun=limiting_tv if field=='tv' else limiting_kl
        ax.plot(alphas,[fun(float(x)) for x in alphas],label='Limiting profile')
        for n,marker in [(32,'o'),(128,'s'),(512,'^'),(2048,'x')]:
            rr=[row for row in rows if int(row['n'])==n]
            ax.plot([float(row['alpha']) for row in rr],[float(row[field]) for row in rr],
                    linestyle='none',marker=marker,markersize=4,label=f'Simplex n={n}')
        ax.set_xlabel('Variance fraction / simplex coordinate fraction')
        ax.set_ylabel(label);ax.set_title(title);ax.legend(fontsize=8)
        fig.tight_layout();fig.savefig(ROOT/'figures'/f'{field}_profile.pdf');plt.close(fig)
    with (ROOT/'data'/'geometric_experiments.csv').open() as handle:
        rr=list(csv.DictReader(handle))
    fig,ax=plt.subplots(figsize=(6.8,4.2))
    n=np.array([float(r['n']) for r in rr]);v=np.array([float(r['tilted_variance']) for r in rr])
    norm=np.sqrt(2*np.pi*v)
    estimates=np.array([float(r['acceptance']) for r in rr])*norm
    errors=np.array([float(r['acceptance_se']) for r in rr])*norm
    ax.errorbar(n,estimates,yerr=1.96*errors,fmt='o',capsize=4,label='Monte Carlo, 95% normal intervals')
    ax.axhline(1,linestyle='--',label='Asymptotic limit')
    ax.set_xscale('log',base=2);ax.set_xlabel('Effective dimension n')
    ax.set_ylabel(r'$\sqrt{2\pi V}\,\Pr(\mathrm{accept})$');ax.legend(fontsize=8)
    fig.tight_layout();fig.savefig(ROOT/'figures'/'acceptance.pdf');plt.close(fig)
    fig,ax=plt.subplots(figsize=(6.8,4.2))
    u=np.linspace(0,1,400)
    for rho in [1.0,1.25,1.75]:
        ax.plot(u,rho*np.exp(-rho*u)/(-math.expm1(-rho)),label=fr'$\rho={rho:g}$')
    ax.set_xlabel('Boundary coordinate u');ax.set_ylabel('Limiting density')
    ax.set_title('A phase-dependent boundary, q = 1/2');ax.legend()
    fig.tight_layout();fig.savefig(ROOT/'figures'/'boundary_phase.pdf');plt.close(fig)


def main() -> None:
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--proposals',type=int,default=160000)
    parser.add_argument('--skip-monte-carlo',action='store_true')
    parser.add_argument('--skip-figures',action='store_true')
    args=parser.parse_args()
    for directory in ['data','figures']:
        (ROOT/directory).mkdir(exist_ok=True)
    print(json.dumps(exact_checks(),indent=2))
    simplex_table()
    if not args.skip_monte_carlo:
        for row in experiments(args.proposals):
            print(f"n={row['n']}: accepted {row['accepted']}/{row['proposals']}; "
                  f"slack mean {row['slack_mean']:.6f}; boundary mean {row['boundary_mean']:.6f}")
    if not args.skip_figures:
        make_figures()

if __name__=='__main__':
    main()
