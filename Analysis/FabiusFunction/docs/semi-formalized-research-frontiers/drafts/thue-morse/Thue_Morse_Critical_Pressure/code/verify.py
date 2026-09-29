#!/usr/bin/env python3
"""Reproducible checks for Critical Cusps in Digital-Product Pressure.

The analytic identities are checked at high precision; collocation is only a
numerical diagnostic, NOT a rigorous enclosure of the infinite operator.
Run from any directory: python code/verify.py [--full]
"""
from __future__ import annotations
import argparse
import json
import math
import platform
from pathlib import Path
import numpy as np
import scipy
import mpmath as mp
import sympy as sp
from scipy.sparse import coo_matrix, csr_matrix
from scipy.sparse.linalg import eigs, ArpackNoConvergence

ROOT = Path(__file__).resolve().parents[1]

def mask(b: int, x: np.ndarray) -> np.ndarray:
    if b < 2:
        raise ValueError("The integer base must be at least two.")
    z = (np.asarray(x, dtype=float) + 0.5) % 1.0 - 0.5
    return np.abs(np.sinc(b*z)/np.sinc(z))

def transfer(b: int, s: float, c: float, grid: int) -> csr_matrix:
    """Periodic piecewise-linear interpolation of the unnormalized operator."""
    if s <= 0 or grid < 16:
        raise ValueError("Require s > 0 and grid >= 16.")
    x = np.arange(grid, dtype=float)/grid
    rows, cols, values = [], [], []
    for k in range(b):
        y = (x+k)/b
        w = mask(b,y-c)**s
        pos = y*grid
        lo = np.floor(pos).astype(np.int64)
        fraction = pos-lo
        rows.extend((np.arange(grid), np.arange(grid)))
        cols.extend((lo % grid, (lo+1) % grid))
        values.extend((w*(1-fraction), w*fraction))
    return coo_matrix((np.concatenate(values),
                     (np.concatenate(rows),np.concatenate(cols))),
                     shape=(grid,grid)).tocsr()

def leading(b: int, s: float, c: float, grid: int, count: int=2) -> dict:
    A = transfer(b,s,c,grid)
    x = np.arange(grid)/grid
    initial = 0.3 + np.sin(np.pi*x) + 0.071*np.cos(2*np.pi*x)
    try:
        values, vectors = eigs(A,k=count,which="LR",v0=initial,
                              tol=2e-12,maxiter=6000)
    except ArpackNoConvergence as exc:
        raise RuntimeError(f"ARPACK did not converge: b={b},s={s},c={c}") from exc
    order = np.argsort(values.real)[::-1]
    values, vectors = values[order], vectors[:,order]
    if np.max(np.abs(values.imag)) > 1e-7:
        raise ArithmeticError(f"Unexpected complex leading pair: {values}")
    residuals = [float(np.max(np.abs(A@vectors[:,i]-values[i]*vectors[:,i]))
                       /np.max(np.abs(vectors[:,i]))) for i in range(count)]
    return {"base":b,"s":s,"phase":c,"grid":grid,
            "eigenvalues":values.real.tolist(),"residuals":residuals,
            "pressure":math.log(float(values[0].real))}

def analytic_checks() -> dict:
    mp.mp.dps = 70
    H = lambda x: abs(mp.sin(mp.pi*x))/mp.pi
    def G(s,x):
        if s == 1:
            return -H(x)*(mp.digamma(x)+mp.digamma(1-x))
        return H(x)**s*(mp.zeta(s,x)+mp.zeta(s,1-x)-2/(s-1))
    errors=[]; count=0
    for b in (2,3,5,10):
        for s in map(mp.mpf,('0.6','0.75','1','1.1','1.4')):
            a = 2*mp.log(b) if s == 1 else 2*(1-b**(1-s))/(s-1)
            for x in map(mp.mpf,('0.0003','0.07','0.219','0.5','0.81','0.9997')):
                lhs = sum((H(x)/(b*H((x+k)/b)))**s*G(s,(x+k)/b)
                          for k in range(b))
                rhs = G(s,x)+a*H(x)**s
                errors.append(abs(lhs-rhs));count+=1
    beta = mp.quad(lambda x: mp.pi/mp.sin(mp.pi*x)
                   +mp.digamma(x)+mp.digamma(1-x),
                   [mp.mpf('1e-15'),mp.mpf('.5'),1-mp.mpf('1e-15')])
    # Endpoint truncation has an O(epsilon) error; this is not an enclosure.
    beta_error=abs(beta-2*mp.log(2/mp.pi))
    singular=[]
    for s in map(mp.mpf,('0.6','0.75','0.9')):
        # A stable beta/digamma integral after integration by parts.
        f=lambda x: ((1-x)**(-s)-(1-x)**(s-1))/x
        k=mp.quad(f,[0,mp.mpf('.5'),1]) + mp.beta(s,1-s)
        computed=s*k; target=mp.pi*s*mp.tan(mp.pi*s/2)
        singular.append({"s":float(s),"computed":float(computed),
                         "target":float(target),"absolute_error":float(abs(computed-target))})
    L,u,a,d,z=sp.symbols('L u a d z')
    J=sp.Matrix([[-u*L,a],[d,0]])
    assert sp.expand(J.charpoly(z).as_expr()-(z*z+u*L*z-a*d)) == 0
    assert max(errors) < mp.mpf('1e-60')
    assert beta_error < mp.mpf('1e-12')
    # Integrable endpoint singularities make raw quadrature less accurate near s=1.
    assert max(v['absolute_error'] for v in singular) < 1e-5
    return {"generalized_eigenfunction_checks":count,
            "max_absolute_error":str(max(errors)),
            "ell_of_one_error_with_truncated_endpoints":str(beta_error),
            "singular_integral_checks":singular,
            "symbolic_matrix_characteristic_polynomial":"z^2+u*L*z-a*d"}

def main() -> None:
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--full',action='store_true',
                        help='Use larger grids and extra crossover/mesh tests.')
    args=parser.parse_args()
    out={"warning":"Floating-point diagnostics are not rigorous spectral enclosures.",
         "versions":{"python":platform.python_version(),"numpy":np.__version__,
                     "scipy":scipy.__version__,"mpmath":mp.__version__,"sympy":sp.__version__},
         "analytic":analytic_checks(),"critical":[],"subcritical":[],
         "crossover":[],"finite_size":[],"mesh_comparison":[]}
    grid=65536 if args.full else 16384
    phases=[1e-2,1e-3,1e-4,1e-5] if args.full else [1e-2,1e-3,1e-4]
    for b in (2,3,5):
        kap=math.sqrt(2*(b-1)*math.log(b))
        for c in phases:
            row=leading(b,1.0,c,grid)
            row['scaled_pressure']=row['pressure']/math.sqrt(c)
            row['limit']=kap;out['critical'].append(row)
            print('critical',b,c,row['scaled_pressure'],kap,flush=True)
    for s in (0.6,0.75,0.9):
        for c in (1e-3,1e-4,1e-5) if args.full else (1e-3,1e-4):
            row=leading(2,s,c,max(grid,262144) if c <= 1e-5 else grid,count=1)
            row['scaled_increment']=(row['pressure']-(1-s)*math.log(2))/c
            row['limit']=math.pi*s*math.tan(math.pi*s/2)
            out['subcritical'].append(row)
            print('subcritical',s,c,row['scaled_increment'],row['limit'],flush=True)
    for u in (-2.0,-1.0,0.0,1.0,2.0):
        for c in ([1e-4,1e-5] if args.full else [1e-4]):
            t=math.sqrt(c);s=1+u*t;L=math.log(2)
            row=leading(2,s,c,grid)
            row['u']=u;row['scaled_pressure']=row['pressure']/t
            row['limit']=-u*L/2+math.sqrt((u*L/2)**2+2*L)
            out['crossover'].append(row)
    # n*t=1: compare the scaled moment t*b^n*M_n with the theorem.
    for u in ([-1.0,0.0,1.0] if args.full else [0.0]):
        for n in ([50,100,200,400] if args.full else [50,100,200]):
            t=1/n;c=t*t;s=1+u*t;A=transfer(2,s,c,grid)
            v=np.ones(grid)
            for _ in range(n):v=A@v
            actual=t*float(np.mean(v));L=math.log(2)
            omega=math.sqrt((u*L/2)**2+2*L)
            target=4*L/math.pi**2*math.exp(-u*L/2)*math.sinh(omega)/omega
            out['finite_size'].append({"u":u,"n":n,"phase":c,"grid":grid,
                                       "scaled_moment":actual,"limit":target})
    if args.full:
        for s,c in [(1.0,1e-5),(0.75,1e-5),(1-2*math.sqrt(1e-5),1e-5)]:
            low=leading(2,s,c,65536,count=1);high=leading(2,s,c,131072,count=1)
            out['mesh_comparison'].append({"s":s,"phase":c,
                    "pressure_grid_65536":low['pressure'],
                    "pressure_grid_131072":high['pressure'],
                    "absolute_difference":abs(low['pressure']-high['pressure'])})
    (ROOT/'data').mkdir(exist_ok=True)
    (ROOT/'data'/'verification.json').write_text(json.dumps(out,indent=2)+'\n')
    # Tables are emitted from actual computed records, not hand-transcribed values.
    rows=['% Generated by code/verify.py; collocation is diagnostic only.',
          r'\begin{tabular}{@{}rrr r@{}}',r'\toprule',
          r'$b$ & $|c|$ & $P_{b,1}(c)/\sqrt{|c|}$ & Predicted limit\\',r'\midrule']
    for r in out['critical']:
        rows.append(f"{r['base']} & $10^{{{int(round(math.log10(r['phase'])))}}}$ & {r['scaled_pressure']:.8f} & {r['limit']:.8f}\\\\")
    rows += [r'\bottomrule',r'\end{tabular}']
    (ROOT/'data'/'critical_table.tex').write_text('\n'.join(rows)+'\n')
    rows=[r'\begin{tabular}{@{}rrr r@{}}',r'\toprule',
          r'$s$ & $|c|$ & $(P_{2,s}(c)-(1-s)\log2)/|c|$ & Predicted limit\\',r'\midrule']
    for r in out['subcritical']:
        rows.append(f"{r['s']:.2f} & $10^{{{int(round(math.log10(r['phase'])))}}}$ & {r['scaled_increment']:.7f} & {r['limit']:.7f}\\\\")
    rows += [r'\bottomrule',r'\end{tabular}']
    (ROOT/'data'/'subcritical_table.tex').write_text('\n'.join(rows)+'\n')
    print('Saved',ROOT/'data'/'verification.json')

if __name__=='__main__':
    main()
