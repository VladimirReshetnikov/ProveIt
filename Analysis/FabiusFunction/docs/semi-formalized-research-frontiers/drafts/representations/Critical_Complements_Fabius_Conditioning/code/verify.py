#!/usr/bin/env python3
"""Reproducible diagnostics for Critical Complements.

Exact algebra tests are separate from floating-point asymptotic diagnostics.
The latter use a dyadic midpoint convolution for the boundary distribution
and a finite signed-gamma mixture for the bulk. They are not interval proofs.
Run from any directory: python code/verify.py
"""
from __future__ import annotations
import argparse
import csv
import json
import math
import platform
from pathlib import Path

import mpmath as mp
import numpy as np
import scipy
from scipy.integrate import cumulative_trapezoid, quad
from scipy.optimize import brentq
from scipy.special import gammaln, gammainc, log_ndtr, digamma
import sympy as sp

ROOT = Path(__file__).resolve().parents[1]
# ed. (2026-09-30): outputs went to the recorded data/ and figures/ on every run;
# they now go to <output-dir>/data and <output-dir>/figures, set in main()
# (default <package>/rerun; pass --output-dir . from the package directory to
# regenerate the recorded files).
DATA = ROOT / 'rerun' / 'data'
FIG = ROOT / 'rerun' / 'figures'


def rational_moments(q: sp.Rational, rho: sp.Rational, degree: int) -> list:
    """Moments of rho * sum_{j>=1} q**j U_j by the affine fixed point."""
    m = [sp.Integer(1)]
    for k in range(1, degree + 1):
        val = sum(sp.binomial(k,j)*(rho*q)**(k-j)*q**j*m[j]/(k-j+1)
                  for j in range(k)) / (1-q**k)
        m.append(sp.factor(val))
    return m


def exact_checks() -> dict:
    count = 0
    x = sp.Symbol('x')
    records = []
    for q in [sp.Rational(1,2), sp.Rational(1,3), sp.Rational(2,3)]:
        for rho in [sp.Integer(1), sp.Rational(5,4)]:
            m = rational_moments(q, rho, 12)
            cumul = [sp.Integer(0), rho*q/(2*(1-q))]
            for j in range(2,13):
                cumul.append(sp.bernoulli(j)/j*(rho*q)**j/(1-q**j))
            independent = [sp.Integer(1)]
            for k in range(1,13):
                independent.append(sp.factor(sum(sp.binomial(k-1,j-1)*cumul[j]*
                                                independent[k-j] for j in range(1,k+1))))
                assert m[k] == independent[k]
                count += 1
            polynomials = [sp.Integer(1)]
            for r in range(1,13):
                pol = sp.expand(sum(sp.binomial(r,j)*(-1)**j*m[j]*x**(r-j)
                                    for j in range(r+1))/sp.factorial(r))
                assert sp.expand(sp.diff(pol,x)-polynomials[-1]) == 0
                polynomials.append(pol)
                count += 1
            records.append({'q':str(q),'rho':str(rho),
                            'moments':[str(z) for z in m],
                            'tail_polynomials':[str(z) for z in polynomials]})
    # Independent finite-simplex normalization identities, exactly rational.
    for N in range(1,13):
        for r in range(7):
            mu = sp.Integer(N+r)
            integral = sum((-1)**j*sp.binomial(r,j)*mu**(r-j)*mu**(N+j)/(N+j)
                           for j in range(r+1))
            target = mu**(N+r)*sp.factorial(N-1)*sp.factorial(r)/sp.factorial(N+r)
            assert sp.factor(integral-target) == 0
            count += 1
    # ed. (2026-09-30): newline='\n' here and below, so text outputs are LF on every platform.
    (DATA/'exact_algebra.json').write_text(json.dumps(records, indent=2)+'\n', newline='\n')
    return {'passed':count, 'failed':0,
            'categories': {'moment_vs_cumulant':72,'kernel_differential_identity':72,
                           'simplex_polynomial_integral':84}}


def mean_te(a: float) -> float:
    if a < 1e-3:
        return a/2-a*a/12+a**4/720-a**6/30240
    if a > 700:
        return 1.0
    return 1-a/math.expm1(a)


def log_K(q: float=.5, rho: float=1.0) -> float:
    with mp.workdps(70):
        qq, rr = mp.mpf(q), mp.mpf(rho)
        return float(mp.fsum(mp.log((rr*qq**j)/(-mp.expm1(-rr*qq**j)))
                             for j in range(1,220)))


class BoundaryKernel:
    """Dyadic boundary law. Only q=1/2, rho=1 is numerically implemented."""
    def __init__(self, bits: int=16, max_r: int=3):
        if not 10 <= bits <= 20:
            raise ValueError('bits must lie between 10 and 20')
        self.bits, self.step = bits, 2.0**(-bits)
        p = np.ones(1)
        for j in range(1,bits+1):
            width = 2**(bits-j)
            ix = np.arange(len(p)+width-1)
            cs = np.r_[0.0,np.cumsum(p)]
            p = (cs[np.minimum(ix+1,len(p))]-cs[np.maximum(ix-width+1,0)])/width
            p = np.maximum(p,0)
            p /= p.sum()
        # Each discrete uniform uses interval midpoints. The unresolved tail
        # is replaced by its exact mean, preserving the total mean 1/2.
        offset = bits*self.step/2+self.step/2
        loc = offset+self.step*np.arange(len(p))
        cdf_nodes = np.cumsum(p)-p/2
        self.grid = np.linspace(0,1,2**bits+1)
        self.integrals = [np.interp(self.grid,loc,cdf_nodes,left=0,right=1)]
        for r in range(1,max_r+1):
            self.integrals.append(cumulative_trapezoid(self.integrals[-1],self.grid,initial=0))
        self.lk = log_K()
        self.K = math.exp(self.lk)
        self.moments = np.array([float(z) for z in rational_moments(sp.Rational(1,2),
                                                                  sp.Integer(1),max_r)])
        self.polynomials = []
        for r in range(max_r+1):
            self.polynomials.append(np.array([math.comb(r,j)*(-1)**j*self.moments[j]/
                                              math.factorial(r) for j in range(r+1)]))
        self.mu_R = sum(mean_te(.5**j) for j in range(1,100))
        self.deficit = sum((2.0**j)/math.expm1(2.0**j) for j in range(10))
        self.kappa = self.mu_R-self.deficit

    def h(self, w: float, r: int=0) -> float:
        if w <= 0:
            return 0.0
        p = (float(np.interp(w,self.grid,self.integrals[r])) if w < 1
             else float(np.polyval(self.polynomials[r],w)))
        return max(0.0,self.K*math.exp(-w)*p)

    def entropy(self, r: int, order: float=1.0) -> float:
        if order == 1:
            def fun(w):
                h = self.h(w,r)
                return -h*math.log(h) if h else 0.0
            return quad(fun,0,1,epsabs=2e-10,limit=120)[0]+quad(fun,1,100,epsabs=2e-10)[0]
        val = (quad(lambda w:self.h(w,r)**order,0,1,epsabs=2e-10,limit=120)[0]+
               quad(lambda w:self.h(w,r)**order,1,200,epsabs=2e-10)[0])
        return math.log(val)/(1-order)


class BulkDensity:
    """Surrogate: upper caps >=64 removed, all smaller caps kept exactly.

    The omitted cap probability under independent exponentials is <2e-28.
    The formula is an inclusion-exclusion sum of shifted gamma densities.
    """
    def __init__(self, n: int, r: int):
        if n-r < 10:
            raise ValueError('n-r must be at least 10')
        self.shape = n-r
        caps = 2.0**np.arange(6)
        shifts, coefs = np.zeros(1), np.ones(1)
        for a in caps:
            shifts, coefs = np.r_[shifts,shifts+a],np.r_[coefs,-math.exp(-a)*coefs]
        self.shifts = shifts
        self.coefs = coefs/np.prod(-np.expm1(-caps))
        self.lg = gammaln(self.shape)

    def pdf(self, x: float) -> float:
        y = x-self.shifts
        mask = y > 0
        yy = y[mask]
        val = np.dot(self.coefs[mask],np.exp((self.shape-1)*np.log(yy)-yy-self.lg))
        return max(0.,float(val))

    def cdf(self, x: float) -> float:
        y = np.maximum(0.,x-self.shifts)
        return float(np.dot(self.coefs,gammainc(self.shape,y)))


def finite_diagnostic(kernel: BoundaryKernel,n: int,r: int) -> dict:
    bulk = BulkDensity(n,r)
    mu = n+kernel.kappa
    limit = min(mu,100.)
    integrand = lambda w:bulk.pdf(mu-w)*kernel.h(w,r)
    Z = quad(integrand,0,1,epsabs=3e-12,limit=120)[0]+quad(integrand,1,limit,epsabs=3e-12)[0]
    # All kernels are unimodal here; locate two likelihood-level crossings.
    probes = np.linspace(1e-5,max(3.,r+2.),500)
    mode = probes[np.argmax([kernel.h(float(w),r) for w in probes])]
    lo = brentq(lambda w:kernel.h(w,r)-Z,0.,float(mode),xtol=1e-13)
    hi = brentq(lambda w:kernel.h(w,r)-Z,float(mode),max(40.,r+10.),xtol=1e-13)
    lower = quad(integrand,0,lo,epsabs=2e-12)[0]/Z
    middle = bulk.cdf(mu-lo)-bulk.cdf(mu-hi)
    upper = quad(integrand,hi,limit,epsabs=2e-12)[0]/Z
    overlap = lower+middle+upper
    def ent(w):
        h = kernel.h(w,r)
        return bulk.pdf(mu-w)*h*math.log(h) if h else 0.0
    kl = -math.log(Z)+(quad(ent,0,1,epsabs=3e-12,limit=120)[0]+
                      quad(ent,1,limit,epsabs=3e-12)[0])/Z
    L = .5*math.log(2*math.pi*n)
    predicted = L+r*math.log(L)+kernel.lk-math.lgamma(r+1)+1
    c = math.exp(-L)
    cutoff = float(r+2)
    lower_c = brentq(lambda w:kernel.h(w,r)-c,0.,cutoff,xtol=1e-13)
    delta = quad(lambda w:max(0.,1-kernel.h(w,r)/c),0,cutoff,
                 points=[lower_c],epsabs=2e-11,limit=120)[0]
    upper_c = brentq(lambda w:kernel.h(w,r)-c,cutoff,50.,xtol=1e-13)
    pol = kernel.polynomials[r]
    tail_ratio = sum(float(np.polyval(np.polyder(pol,j),upper_c))
                     for j in range(r+1))/float(np.polyval(pol,upper_c))
    fixed_kernel_J = upper_c+tail_ratio-delta
    return {'n':n,'r':r,'normalizer':Z,'overlap':overlap,'scaled_overlap':overlap/c,
            'overlap_prediction':predicted,'scaled_residual':overlap/c-predicted,
            'KL':kl,'KL_prediction':L-kernel.entropy(r),
            'boundary_defect':delta,'fixed_kernel_J':fixed_kernel_J,
            'reduction_error':overlap/c-fixed_kernel_J,
            'likelihood_lower':lo,'likelihood_upper':hi}


def simplex_renyi(n: int,r: int,alpha: float) -> float:
    """Exact one-dimensional integral for a finite simplex benchmark.
    Observed gamma shape n-r; the simplex bound is n. Integration is in
    w/sqrt(n), avoiding the moving scale in the order-zero transition.
    """
    N = n-r
    if not 0 <= alpha < 1:
        raise ValueError('this diagnostic routine expects 0 <= alpha < 1')
    if alpha == 0:
        return -math.log(float(gammainc(N,n)))
    logZ = n*math.log(n)-n-gammaln(n+1)
    sn = math.sqrt(n)
    def fun(z):
        w = sn*z
        v = n-w
        if v <= 0 or w <= 0:
            return 0.
        lg = (N-1)*math.log(v)-v-gammaln(N)
        lh = r*math.log(w)-w-gammaln(r+1)
        return math.exp(math.log(sn)+lg+alpha*lh-alpha*logZ)
    integral = quad(fun,0,min(sn,18),epsabs=2e-11,limit=180)[0]
    return math.log(integral)/(alpha-1)


def write_csv(name: str, rows: list[dict]) -> None:
    with (DATA/name).open('w',newline='') as f:
        # ed. (2026-09-30): LF rows (the csv default is CRLF).
        writer=csv.DictWriter(f,fieldnames=rows[0].keys(),lineterminator='\n')
        writer.writeheader();writer.writerows(rows)


def make_figures(rows: list[dict],cross: list[dict]) -> None:
    import matplotlib.pyplot as plt
    # No explicit colors or styles: Matplotlib's defaults are retained.
    fig,ax=plt.subplots(figsize=(7.2,4.2))
    for r in range(4):
        rr=[z for z in rows if z['r']==r]
        nn=np.array([z['n'] for z in rr])
        yy=np.array([z['scaled_residual'] for z in rr])
        ax.semilogx(nn,yy,marker='o',label=f'r = {r}')
    ax.axhline(0,linewidth=.8,linestyle='--')
    ax.set_xlabel('Effective dimension n')
    ax.set_ylabel('Scaled overlap minus three-term prediction')
    ax.legend();fig.tight_layout();fig.savefig(FIG/'overlap_residual.png',dpi=240);plt.close(fig)
    fig,ax=plt.subplots(figsize=(7.2,4.2))
    rr=[z for z in rows if z['r']==0]
    nn=[z['n'] for z in rr]
    ax.semilogx(nn,[-z['scaled_residual'] for z in rr],marker='o',label='Actual residual')
    ax.semilogx(nn,[z['boundary_defect'] for z in rr],marker='s',linestyle='--',label='Endpoint defect')
    ax.set_xlabel('Effective dimension n');ax.set_ylabel('Positive deficit')
    ax.legend();fig.tight_layout();fig.savefig(FIG/'endpoint_defect.png',dpi=240);plt.close(fig)
    fig,ax=plt.subplots(figsize=(7.2,4.2))
    cc=np.linspace(0,4,200)
    ax.plot(cc,-cc*cc/2-log_ndtr(-cc),label='Limiting crossover',linewidth=2)
    for n in [64,512,4096]:
        rr=[z for z in cross if z['n']==n]
        ax.plot([z['c'] for z in rr],[z['D'] for z in rr],marker='o',linestyle='--',
                label=f'Simplex, n = {n}')
    ax.set_xlabel(r'Scaled order $c=\alpha\sqrt{n}$');ax.set_ylabel(r'$D_\alpha$')
    ax.legend();fig.tight_layout();fig.savefig(FIG/'renyi_crossover.png',dpi=240);plt.close(fig)


def make_tex_tables(rows: list[dict], kernels: list[dict], cross: list[dict]) -> None:
    lines=[r'\begin{tabular}{rrrrr}',r'\toprule',
           r'$n$ & $r$ & $\sqrt{2\pi n}\,\mathcal O_{n,r}$ & Prediction & Residual\\',r'\midrule']
    for z in rows:
        if z['n'] in [64,1024,65536]:
            lines.append(f"{z['n']:,} & {z['r']} & {z['scaled_overlap']:.6f} & "
                         f"{z['overlap_prediction']:.6f} & {z['scaled_residual']:+.6f} \\\\")
    lines += [r'\bottomrule',r'\end{tabular}']
    (DATA/'overlap_table.tex').write_text('\n'.join(lines)+'\n', newline='\n')
    lines=[r'\begin{tabular}{rrrr}',r'\toprule',r'$r$ & $h(H_r)$ & $h_{1/2}(H_r)$ & Normalization error\\',r'\midrule']
    for z in kernels:
        lines.append(f"{z['r']} & {z['entropy']:.8f} & {z['entropy_half']:.8f} & {z['normalization_error']:.2e} \\\\")
    lines += [r'\bottomrule',r'\end{tabular}']
    (DATA/'kernel_table.tex').write_text('\n'.join(lines)+'\n', newline='\n')


    lines=[r'\begin{tabular}{rrrrrr}',r'\toprule',
           r'$n$ & $r$ & Scaled overlap & $J_r(c_n)$ & $\delta_r(c_n)$ & Difference\\',r'\midrule']
    for z in rows:
        if z['n'] in [1024,65536]:
            lines.append(f"{z['n']:,} & {z['r']} & {z['scaled_overlap']:.6f} & "
                         f"{z['fixed_kernel_J']:.6f} & {z['boundary_defect']:.6f} & "
                         f"{z['reduction_error']:+.6f} " + r'\\')
    lines += [r'\bottomrule',r'\end{tabular}']
    (DATA/'reduction_table.tex').write_text('\n'.join(lines)+'\n', newline='\n')


def main() -> None:
    # ed. (2026-09-30): output directory option (see the note at ROOT).
    global DATA, FIG
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output-dir', type=Path, default=ROOT/'rerun',
                        help='directory receiving data/ and figures/ (default: <package>/rerun)')
    args = parser.parse_args()
    DATA = args.output_dir/'data'
    FIG = args.output_dir/'figures'
    DATA.mkdir(parents=True, exist_ok=True)
    FIG.mkdir(parents=True, exist_ok=True)
    exact=exact_checks()
    kernel=BoundaryKernel(16)
    finer=BoundaryKernel(17)
    grid=np.linspace(.02,1,300)
    refinement=max(abs(kernel.h(float(w),r)-finer.h(float(w),r))
                   for w in grid for r in range(4))
    assert refinement < 2e-7, refinement
    kernel_stats=[]
    for r in range(4):
        normalization=(quad(lambda w:kernel.h(w,r),0,1,epsabs=2e-10,limit=120)[0]+
                       quad(lambda w:kernel.h(w,r),1,100,epsabs=2e-10)[0])
        assert abs(normalization-1)<2e-7, (r,normalization)
        kernel_stats.append({'r':r,'entropy':kernel.entropy(r),
                             'entropy_half':kernel.entropy(r,.5),
                             'normalization_error':normalization-1})
    rows=[finite_diagnostic(kernel,n,r) for r in range(4)
          for n in [64,256,1024,4096,16384,65536]]
    for row in rows:
        assert 0<row['overlap']<1 and row['KL']>0
    cross=[]
    for n in [64,512,4096]:
        for c in [0,.25,.5,1,1.5,2,3,4]:
            D=simplex_renyi(n,0,c/math.sqrt(n))
            cross.append({'n':n,'c':c,'alpha':c/math.sqrt(n),'D':D,
                          'limit':-c*c/2-float(log_ndtr(-c))})
    write_csv('overlap_diagnostics.csv',rows)
    write_csv('kernel_entropies.csv',kernel_stats)
    write_csv('renyi_crossover.csv',cross)
    make_tex_tables(rows,kernel_stats,cross)
    make_figures(rows,cross)
    receipt={'exact_checks':exact,'floating_point_diagnostics':{
        'geometric_cases':len(rows),'simplex_crossover_cases':len(cross),
        'kernel_normalizations':4,'refinement_max_abs_difference':refinement,
        'logK_dyadic':kernel.lk,'K_dyadic':kernel.K,'tilted_boundary_mean':kernel.mu_R,
        'kappa_dyadic':kernel.kappa,
        'limitations':'No interval arithmetic. Infinite boundary approximated by dyadic midpoint convolution; caps >=64 removed in the bulk mixture.'},
        'environment':{'python':platform.python_version(),'numpy':np.__version__,
                       'scipy':scipy.__version__,'sympy':sp.__version__,'mpmath':mp.__version__}}
    (DATA/'verification.json').write_text(json.dumps(receipt,indent=2)+'\n', newline='\n')
    print(f"Exact checks passed: {exact['passed']} (0 failed).")
    print(f"Numerical cases: {len(rows)} geometric and {len(cross)} simplex crossover cases.")
    print(f"Boundary mesh-refinement difference: {refinement:.3e}.")
    print(f"Dyadic K = {kernel.K:.12f}; log K = {kernel.lk:.12f}.")
    print('Figures, tables, CSV data, and verification receipt saved.')

if __name__ == '__main__':
    main()
