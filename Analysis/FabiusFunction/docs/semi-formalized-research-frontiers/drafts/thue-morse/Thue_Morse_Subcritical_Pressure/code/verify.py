#!/usr/bin/env python3
"""Reproducible diagnostics, not proof certificates, for localized pressure.

Run from any directory.  --full adds fine meshes and smaller phases.
Only numpy, scipy, and mpmath are required.  No network access is used.
"""
from __future__ import annotations
import argparse
import json
import math
import platform
from pathlib import Path
from typing import Callable
import warnings
import numpy as np
import scipy
from scipy.integrate import quad, IntegrationWarning
import mpmath as mp

ROOT = Path(__file__).resolve().parents[1]


def coefficient(s: float) -> float:
    if not 0.0 < s < 1.0:
        raise ValueError('s must lie in (0,1)')
    return math.pi * s * math.tan(math.pi * s / 2.0)


def model_integral(s_text: str) -> dict:
    """Independent integral for J_s; remove the u=0 algebraic singularity."""
    with mp.workdps(65):
        s = mp.mpf(s_text)
        def small(t):
            u = t ** (1 / (1-s))
            return ((1+u)**s + (1-u)**s - 2*u**s)/(1-s)
        def tail(v):
            if abs(v) < mp.mpf('1e-22'):
                return s*(s-1)
            return ((1+v)**s + (1-v)**s - 2)/(v*v)
        val = mp.quad(small, [0, mp.mpf('.5'), 1]) + mp.quad(tail, [0, mp.mpf('.5'), 1])
        exact = mp.pi*s*mp.tan(mp.pi*s/2)
        err = abs(val-exact)
        assert err < mp.mpf('1e-30'), (s, err)
        return {'s': s_text, 'quadrature': str(val), 'formula': str(exact), 'absolute_error': str(err)}


def ratio_integral(b: int, s: float, shifts: np.ndarray,
                   test: Callable[[float], float] = lambda x: 1.0) -> tuple[float, float]:
    """Integral of (m_e/m_0)^s-1 against a smooth test; split all zeros."""
    shifts = np.asarray(shifts, dtype=float)
    if len(shifts) != b-1 or max(abs(shifts), default=0) >= 1/(4*b):
        raise ValueError('one sufficiently small shift is required for each zero')
    zeros = np.arange(1,b,dtype=float)/b
    def fun(x: float) -> float:
        a = np.abs(np.sin(np.pi*(x-zeros-shifts)))
        d = np.abs(np.sin(np.pi*(x-zeros)))
        if np.any(d == 0):
            return 0.0  # quadrature does not sample singular endpoints
        if np.any(a == 0):
            return -test(x)
        return math.expm1(s*float(np.sum(np.log(a)-np.log(d))))*test(x)
    cuts = sorted(set([0.0, 1.0, *zeros.tolist(), *(zeros+shifts).tolist()]))
    val, err = 0.0, 0.0
    for left,right in zip(cuts,cuts[1:]):
        if right <= left:
            continue
        v,e = quad(fun, left, right, epsabs=2e-12, epsrel=2e-10, limit=300)
        val += v
        err += e
    return val,err


class Collocation:
    """Periodic linear collocation of the unnormalized transfer operator."""
    def __init__(self, b: int, s: float, shifts: np.ndarray, grid: int):
        self.grid = grid
        self.b = b
        x = np.arange(grid,dtype=float)/grid
        zeros = np.arange(1,b,dtype=float)/b + np.asarray(shifts,dtype=float)
        self.branches = []
        for k in range(b):
            y = (x+k)/b
            pos = (np.arange(grid,dtype=np.int64)+k*grid)/b
            ix = np.floor(pos).astype(np.int64)
            frac = pos-ix
            mask = np.ones(grid,dtype=float)/b
            for z in zeros:
                mask *= 2*np.abs(np.sin(np.pi*(y-z)))
            self.branches.append((ix % grid, (ix+1) % grid, frac, mask**s))

    def apply(self, f: np.ndarray) -> np.ndarray:
        out = np.zeros_like(f)
        for i,j,t,w in self.branches:
            out += w*((1-t)*f[i]+t*f[j])
        return out

    def leading(self, tol: float = 3e-13, maxiter: int = 700) -> dict:
        f = np.ones(self.grid)
        scale = 1.0
        for iteration in range(1,maxiter+1):
            g = self.apply(f)
            newscale = float(np.max(g))
            if not np.isfinite(newscale) or newscale <= 0:
                raise ArithmeticError('nonpositive/nonfinite power iterate')
            g /= newscale
            err = float(np.max(abs(g-f)))
            f,scale = g,newscale
            if err < tol:
                residual = float(np.max(abs(self.apply(f)-scale*f)))
                return {'eigenvalue':scale, 'pressure':math.log(scale),
                        'iterations':iteration, 'matrix_residual_sup':residual}
        raise RuntimeError(f'power iteration did not converge; last change={err}')

    def finite_moment(self, s: float, n: int) -> float:
        """Return beta^{-n} mean(L^n 1) = b^{sn} M_n on the grid."""
        f = np.ones(self.grid)
        beta = self.b**(1-s)
        for _ in range(n):
            f = self.apply(f)/beta
        return float(np.mean(f))


def main() -> None:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--full', action='store_true')
    args = ap.parse_args()
    (ROOT/'data').mkdir(exist_ok=True)
    results = {'status':'Floating-point/high-precision diagnostics; no interval or spectral certification.',
               'versions':{'python':platform.python_version(),'numpy':np.__version__,
                           'scipy':scipy.__version__,'mpmath':mp.__version__},
               'full':args.full}
    results['model_integrals'] = [model_integral(s) for s in ('0.1','0.25','0.5','0.75','0.9')]
    print('Independent J_s integrals passed',flush=True)
    rows = []
    for s in (0.2,0.25,0.5,0.75):
        for h in (1e-2,1e-3,1e-4):
            for sign in (-1,1):
                val,err = ratio_integral(2,s,np.array([sign*h]),
                    lambda x: 1+.2*math.cos(2*math.pi*x)+.1*math.sin(2*math.pi*x))
                target=.8*coefficient(s)+sign*.1*math.pi*s
                rows.append({'s':s,'h':h,'sign':sign,'scaled':val/h,'target':target,
                             'quad_error_estimate_scaled':err/h})
    results['weak_distribution'] = rows
    print('Weak derivative diagnostics computed',flush=True)
    prows=[]
    grids = (2**18,2**19) if args.full else (2**16,2**17)
    for b,s,v in ((2,.2,[1.]),(2,.25,[1.]),(2,.5,[1.]),(3,.3,[1.,-1.])):
        for h in (1e-2,3e-3,1e-3):
            for grid in grids:
                op=Collocation(b,s,h*np.array(v),grid)
                row=op.leading()
                row.update({'b':b,'s':s,'h':h,'velocity':v,'grid':grid,
                            'scaled_increment':(row['pressure']-(1-s)*math.log(b))/h,
                            'target':coefficient(s)*sum(abs(x) for x in v)})
                prows.append(row)
                print('pressure',b,s,h,grid,row['scaled_increment'],row['target'],flush=True)
    results['pressure']=prows
    frows=[]
    s=.25; b=2; tau=.1
    for n in (25,50,100,200):
        h=tau/n
        op=Collocation(b,s,np.array([h]),grids[-1])
        observed=op.finite_moment(s,n)
        amp=2*math.tan(math.pi*s/2)/(math.pi*s)
        target=amp*math.exp(coefficient(s)*tau)
        frows.append({'s':s,'n':n,'h':h,'grid':grids[-1],
                      'rescaled_moment':observed,'target':target})
        print('finite size',n,observed,target,flush=True)
    results['finite_size']=frows
    # A normalization check independent of spectral computation.
    s=mp.mpf('.25')
    beta_amp=mp.gamma((1+s)/2)*mp.gamma((1-s)/2)/(mp.pi*mp.gamma(1+s/2)*mp.gamma(1-s/2))
    elementary_amp=2*mp.tan(mp.pi*s/2)/(mp.pi*s)
    assert abs(beta_amp-elementary_amp)<mp.mpf('1e-14')
    results['amplitude_identity_error']=float(abs(beta_amp-elementary_amp))
    (ROOT/'data'/'verification.json').write_text(json.dumps(results,indent=2)+'\n')
    with (ROOT/'data'/'pressure_table.tex').open('w') as f:
        f.write('\\begin{tabular}{@{}rrrrrr@{}}\n\\toprule\n'
                '$b$ & $s$ & $h$ & coarse grid & fine grid & predicted limit\\\\\n\\midrule\n')
        for i in range(0,len(prows),2):
            r,t=prows[i:i+2]
            f.write(f"{r['b']} & {r['s']:.2f} & {r['h']:.3g} & {r['scaled_increment']:.6f} & {t['scaled_increment']:.6f} & {r['target']:.6f}\\\\\n")
        f.write('\\bottomrule\n\\end{tabular}\n')
    with (ROOT/'data'/'finite_size_table.tex').open('w') as f:
        f.write('\\begin{tabular}{@{}rrrr@{}}\n\\toprule\n'
                '$n$ & $h$ & $b^{sn}M_n$ (grid) & limiting value\\\\\n\\midrule\n')
        for r in frows:
            f.write(f"{r['n']} & {r['h']:.5f} & {r['rescaled_moment']:.7f} & {r['target']:.7f}\\\\\n")
        f.write('\\bottomrule\n\\end{tabular}\n')
    print('Wrote data/verification.json and LaTeX tables',flush=True)

if __name__ == '__main__':
    main()
