#!/usr/bin/env python3
"""Exact polynomial checks and high-precision spectral diagnostics.

No numerical result is used as a substitute for a proof in the article.
Requires Python 3.10+, sympy, mpmath, matplotlib.
ed. (2026-09-29): outputs go to rerun/data and rerun/figures unless
--output-dir is given (pass --output-dir . to regenerate the recorded files);
all text output is LF; figure fonts are embedded as TrueType (no Type 3).
"""
from __future__ import annotations
from fractions import Fraction as F
from math import comb
from pathlib import Path
import csv
import json
import hashlib
import argparse
import sympy as sp
import mpmath as mp

ROOT = Path(__file__).resolve().parent

def moments(q: F, n: int, m: int | None = None) -> list[F]:
    """Moments of X_q, or its depth-m prefix, using exact cumulants."""
    if not 0 < q < 1 or n < 0 or (m is not None and m < 1):
        raise ValueError('Require 0<q<1, n>=0, and positive prefix depth.')
    kappa = [F(0) for _ in range(n + 1)]
    for k in range(2, n + 1, 2):
        b = sp.bernoulli(k)
        kappa[k] = F(int(b.p), int(b.q)) * F(2**k, k)
        kappa[k] *= (1-q)**k / (1-q**k)
        if m is not None:
            kappa[k] *= 1-q**(m*k)
    mu = [F(1)] + [F(0) for _ in range(n)]
    for k in range(1, n+1):
        mu[k] = sum((comb(k-1, j-1)*kappa[j]*mu[k-j]
                     for j in range(1, k+1)), F(0))
    return mu

def inner(a: list[F], b: list[F], mu: list[F]) -> F:
    return sum((ai*bj*mu[i+j] for i, ai in enumerate(a) if ai
                for j, bj in enumerate(b) if bj), F(0))

def monic_orthogonal(mu: list[F], n: int):
    polys, norms = [], []
    for j in range(n+1):
        p = [F(0)]*j + [F(1)]
        for v, h in zip(polys, norms):
            coef = inner(p, v, mu)/h
            for i in range(len(v)):
                p[i] -= coef*v[i]
        h = inner(p, p, mu)
        assert h > 0
        polys.append(p)
        norms.append(h)
    return polys, norms

def apply_conditional(p: list[F], tail_mu: list[F]) -> list[F]:
    return [sum((p[j]*comb(j, i)*tail_mu[j-i]
                 for j in range(i, len(p))), F(0))
            for i in range(len(p))]

def mpf(x: F):
    return mp.mpf(x.numerator)/x.denominator

def matrix(q: F, m: int, n: int):
    mx, ms = moments(q, 2*n), moments(q, 2*n, m)
    r = q**m
    mt = [r**j*x for j, x in enumerate(mx)]
    px, hx = monic_orthogonal(mx, n)
    ps, hs = monic_orthogonal(ms, n)
    cross = [[F(0) for _ in range(n+1)] for _ in range(n+1)]
    for j in range(n+1):
        image = apply_conditional(px[j], mt)
        for i in range(n+1):
            v = inner(ps[i], image, ms)
            cross[i][j] = v
            if i > j or (i+j) % 2:
                assert v == 0
        assert cross[j][j] == hs[j]
    A = mp.matrix(n+1)
    trace = F(0)
    for i in range(n+1):
        for j in range(n+1):
            A[i,j] = mpf(cross[i][j])/mp.sqrt(mpf(hs[i]*hx[j]))
            trace += cross[i][j]**2/(hs[i]*hx[j])
    assert A[0,0] == 1
    return A, hx, hs, cross, trace

def basic_checks() -> dict:
    q, t = sp.symbols('q t')
    lam = -sp.Rational(6,5)*(1-q*q)/(1+q*q)
    expected = (1-t)**2*(1-(4+q*q)/(1+4*q*q)*t)
    direct = (1-t)*(2*(1-t)**2+lam*(1-t*t))/(2+lam)
    assert sp.factor(direct-expected) == 0
    one = (1-q*q)**2*(1-q**4)/(1+4*q*q)
    assert sp.factor(expected.subs(t,q*q)-one) == 0
    # Classical Jacobi derivative-norm multiplier, exact integration.
    x = sp.symbols('x')
    for alpha in (0, 1, 2):
        for n in range(1, 7):
            P = sp.jacobi(n,alpha,alpha,x)
            norm = sp.integrate(P**2*(1-x*x)**alpha,(x,-1,1))
            for k in range(1,min(3,n)+1):
                dn = sp.integrate(sp.diff(P,x,k)**2*(1-x*x)**(alpha+k),(x,-1,1))
                target = sp.prod(n-j for j in range(k))*sp.prod(n+2*alpha+1+j for j in range(k))
                assert sp.simplify(dn/norm-target) == 0
    # Jordan ranks: rank((C-I)^k) = max(n+1-2k,0).
    mu = moments(F(1,2), 10)
    for n in range(1,9):
        B = sp.Matrix(n+1,n+1,lambda i,j:
                      sp.Rational(comb(j,i)*mu[j-i]*(F(1,2)**(j-i))) if j>=i else 0)
        D = B-sp.eye(n+1)
        for k in range(1,n+2):
            assert (D**k).rank() == max(n+1-2*k,0)
    # Convolution Appell intertwining, exactly on EGF coefficient arrays.
    for qq, m in [(F(1,3),1),(F(1,2),2),(F(2,3),3)]:
        n=8
        mx, ms = moments(qq,n), moments(qq,n,m)
        mt = [qq**(m*j)*mx[j] for j in range(n+1)]
        def inverse_egf(mu):
            out=[F(1)]
            for k in range(1,len(mu)):
                out.append(-sum((comb(k,j)*mu[j]*out[k-j] for j in range(1,k+1)),F(0)))
            return out
        ix, iss = inverse_egf(mx), inverse_egf(ms)
        for k in range(n+1):
            ax=[comb(k,j)*ix[k-j] for j in range(k+1)]
            ass=[comb(k,j)*iss[k-j] for j in range(k+1)]
            assert apply_conditional(ax,mt) == ass
    return {'symbolic_determinant_identity':'passed',
            'Jacobi_norm_identity':'passed (45 degree/order cases)',
            'Jordan_rank_checks':'passed (degrees 1--8)',
            'Appell_intertwining':'passed (3 parameter pairs, degrees 0--8)'}

def main() -> None:
    ap=argparse.ArgumentParser()
    ap.add_argument('--degree',type=int,default=18)
    ap.add_argument('--skip-symbolic',action='store_true')
    # ed. (2026-09-29): output directory option; the default leaves the
    # recorded data/ and figures/ (the figure the article includes) untouched.
    ap.add_argument('--output-dir',type=Path,default=ROOT/'rerun',
                    help='directory receiving data/ and figures/ (default: rerun/ '
                         'beside this script; pass . to overwrite the recorded files)')
    args=ap.parse_args()
    OUT=args.output_dir.resolve()
    if args.degree < 3 or args.degree > 32:
        raise ValueError('Diagnostic degree must lie between 3 and 32.')
    mp.mp.dps=100
    (OUT/'data').mkdir(parents=True,exist_ok=True)
    (OUT/'figures').mkdir(parents=True,exist_ok=True)
    report={} if args.skip_symbolic else basic_checks()
    rows, spectra=[],[]
    for qq,m in [(F(1,3),1),(F(1,2),1),(F(1,2),2),(F(1,2),3),(F(2,3),1)]:
        A,hx,hs,cross,trace=matrix(qq,m,args.degree)
        eigen=mp.eigsy(A.T*A,eigvals_only=True)
        assert min(eigen)>-mp.mpf('1e-75')
        sv=sorted([mp.sqrt(max(v,mp.mpf(0))) for v in eigen],reverse=True)
        assert abs(sv[0]-1)<mp.mpf('1e-75')
        # Exact diagonal determinant formula through degree 2.
        t=qq**(2*m)
        det2=(hs[0]*hs[1]*hs[2])/(hx[0]*hx[1]*hx[2])
        formula=(1-t)**2*(1-(4+qq*qq)/(1+4*qq*qq)*t)
        assert det2==formula
        V=moments(qq,6)[2]
        mx=moments(qq,6)
        k4=mx[4]-3*V*V
        h3=mx[6]-mx[4]**2/V
        target=k4*t*(1-t)
        assert cross[1][3]==target
        cubic=(1-t)*(1+(k4/V**2)**2*t*t/(h3/V**3))
        assert 1-t<cubic<1
        row={'q':str(qq),'m':m,'degree':args.degree,
             'linear_correlation':mp.nstr(mp.sqrt(mpf(1-t)),18),
             'cubic_witness_bound':mp.nstr(mp.sqrt(mpf(cubic)),18),
             'polynomial_max_correlation':mp.nstr(sv[1],18),
             'I2_trace_lower_bound':mp.nstr(mp.log(mpf(trace)),18),
             'I1_exact':mp.nstr(-m*mp.log(mpf(qq)),18),
             'trace_exact_numerator':str(trace.numerator),
             'trace_exact_denominator':str(trace.denominator)}
        rows.append(row)
        spectra.extend({'q':str(qq),'m':m,'index':i+1,'singular_value':mp.nstr(v,35)}
                       for i,v in enumerate(sv))
        print({k:v for k,v in row.items() if 'exact_numerator' not in k and 'exact_denominator' not in k},flush=True)
    for name,rr in [('polynomial_bounds.csv',rows),('singular_values.csv',spectra)]:
        # ed. (2026-09-29): lineterminator='\n' so the CSVs are LF on every OS.
        with (OUT/'data'/name).open('w',newline='') as f:
            w=csv.DictWriter(f,fieldnames=rr[0].keys(),lineterminator='\n');w.writeheader();w.writerows(rr)
    report.update({'finite_polynomial_checks':'passed for all 5 parameter pairs',
                   'precision_decimal_digits':mp.mp.dps,'maximum_degree':args.degree,
                   'status':'exact identities plus non-interval numerical diagnostics; no Lean certification'})
    # ed. (2026-09-29): newline='\n' so the JSON and the table fragment are LF on Windows too.
    (OUT/'data'/'verification_report.json').write_text(json.dumps(report,indent=2)+'\n',newline='\n')
    with (OUT/'data'/'bounds_table.tex').open('w',newline='\n') as f:
        for row in rows:
            qtex='\\tfrac{%s}{%s}'%tuple(row['q'].split('/'))
            f.write('$%s$ & %d & %.8f & %.8f & %.8f \\\\\n'%(qtex,row['m'],float(row['linear_correlation']),float(row['cubic_witness_bound']),float(row['polynomial_max_correlation'])))
    import matplotlib
    matplotlib.use('Agg')
    # ed. (2026-09-29): TrueType (Type 42) fonts instead of Type 3 in the figure PDF.
    matplotlib.rcParams['pdf.fonttype']=42
    matplotlib.rcParams['ps.fonttype']=42
    import matplotlib.pyplot as plt
    fig,ax=plt.subplots(figsize=(6.7,4.0))
    for m in (1,2,3):
        rr=[r for r in spectra if r['q']=='1/2' and r['m']==m]
        ax.semilogy([r['index'] for r in rr],[float(r['singular_value']) for r in rr],marker='o',markersize=3,label=f'm = {m}')
    ax.set_xlabel('Singular-value index (constant mode included)')
    ax.set_ylabel('Singular value of polynomial restriction')
    ax.legend()
    ax.grid(True,which='major',alpha=.3)
    fig.tight_layout()
    fig.savefig(OUT/'figures'/'polynomial_spectra.pdf')
    fig.savefig(OUT/'figures'/'polynomial_spectra.png',dpi=160)
    plt.close(fig)

if __name__=='__main__':
    main()
