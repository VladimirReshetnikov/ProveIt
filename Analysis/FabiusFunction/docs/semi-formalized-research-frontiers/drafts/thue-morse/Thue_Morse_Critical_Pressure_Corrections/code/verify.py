#!/usr/bin/env python3
"""Reproducible diagnostics for critical digital-product pressure.

No calculation below certifies the infinite-dimensional spectrum.  The paper
contains the proofs.  Use --identities-only for the small high-precision run.
Outputs go to --output-dir (default: ../data); existing outputs are replaced.
"""
from __future__ import annotations
import argparse
import json
import math
import platform
import time
from pathlib import Path
import mpmath as mp
import numpy as np
import scipy
from scipy.sparse import csr_matrix
from scipy.sparse.linalg import eigs


def H(x: mp.mpf) -> mp.mpf:
    return abs(mp.sin(mp.pi*x))/mp.pi


def G(x: mp.mpf) -> mp.mpf:
    x = mp.frac(x)
    if not x:
        return mp.mpf(1)
    return H(x)*(-mp.digamma(x)-mp.digamma(1-x)+2*mp.log(2/mp.pi))


def mask(b: int, x: mp.mpf) -> mp.mpf:
    x = x-mp.nint(x)
    if not x:
        return mp.mpf(1)
    return abs(mp.sin(mp.pi*b*x)/(b*mp.sin(mp.pi*x)))


def transfer_mp(b: int, c: mp.mpf, f, x: mp.mpf) -> mp.mpf:
    return mp.fsum(mask(b,(x+k)/b-c)*f((x+k)/b) for k in range(b))


def matrix(b: int, s: float, c: float, requested_mesh: int) -> csr_matrix:
    if b < 2 or s <= 0 or requested_mesh < 8:
        raise ValueError('Require base >= 2, exponent > 0, and mesh >= 8.')
    m = (requested_mesh+b-1)//b*b
    j = np.arange(m)
    rows, cols, values = [], [], []
    for k in range(b):
        y = (j/m+k)/b
        z = (y-c+0.5)%1-0.5
        weight = np.abs(np.sinc(b*z)/np.sinc(z))**s
        pos = (j+k*m)/b
        lo = np.floor(pos).astype(np.int64)
        fraction = pos-lo
        rows.extend((j,j))
        cols.extend((lo%m,(lo+1)%m))
        values.extend((weight*(1-fraction),weight*fraction))
    return csr_matrix((np.concatenate(values),
                       (np.concatenate(rows),np.concatenate(cols))),shape=(m,m))


def eigendata(b: int, s: float, c: float, mesh: int,
              measure: bool = False) -> dict:
    a = matrix(b,s,c,mesh)
    v0 = 1+0.1*np.cos(2*np.pi*np.arange(a.shape[0])/a.shape[0])
    vals, vecs = eigs(a,k=2,which='LR',tol=2e-12,maxiter=4000,v0=v0)
    idx = np.argsort(vals.real)[::-1]
    if max(abs(vals.imag)) > 1e-8:
        raise ArithmeticError('Unexpected nonreal leading numerical eigenvalue.')
    lp, lm = float(vals[idx[0]].real), float(vals[idx[1]].real)
    right = vecs[:,idx[0]].real
    if np.sum(right)<0:
        right = -right
    residual = np.linalg.norm(a@right-lp*right)/np.linalg.norm(right)
    result = dict(base=b,exponent=s,phase=c,mesh=a.shape[0],lambda_plus=lp,
                  lambda_minus=lm,pressure=math.log(lp),right_residual=float(residual))
    if measure:
        lv, lw = eigs(a.T,k=1,which='LR',tol=2e-12,maxiter=4000,v0=v0)
        left = lw[:,0].real
        if np.sum(left)<0:
            left = -left
        mu = left*right
        mu /= np.sum(mu)
        x = np.arange(a.shape[0])/a.shape[0]
        result.update(left_residual=float(np.linalg.norm(a.T@left-lp*left)/np.linalg.norm(left)),
                      cosine_moment=float(mu@np.cos(2*np.pi*x)),
                      sine_moment=float(mu@np.sin(2*np.pi*x)),
                      minimum_product_mass=float(np.min(mu)),
                      eigenvalue_left_discrepancy=float(abs(lv[0]-lp)))
    return result


def identities() -> dict:
    mp.mp.dps = 70
    rows = []
    for b in (2,3,5,7):
        aa = 2*mp.log(b)
        for x in (mp.mpf('0.0003'),mp.mpf('.07'),mp.mpf('.2'),mp.mpf('.5'),mp.mpf('.83')):
            rows.append(dict(base=b,x=str(x),
                H_residual=str(abs(transfer_mp(b,mp.mpf(0),H,x)-H(x))),
                G_residual=str(abs(transfer_mp(b,mp.mpf(0),G,x)-G(x)-aa*H(x)))))
    response = []
    for b in (2,3,5,7):
        d = b-1
        for c in (mp.mpf('0.002'),mp.mpf('0.00001')):
            atom = transfer_mp(b,c,H,mp.mpf(0))
            atom_target = mp.sin(mp.pi*d*c)/mp.pi
            x = (1+b*c)/2
            bulk = transfer_mp(b,c,H,x)
            bulk_target = mp.sin(mp.pi*(x-d*c))/mp.pi
            response.append(dict(base=b,phase=str(c),atom_residual=str(abs(atom-atom_target)),
                                 bulk_residual=str(abs(bulk-bulk_target))))
    trace = []
    for b in (2,3,5):
        d = b-1
        r = 2*d*(mp.euler+mp.log(2/mp.pi))+2*b*mp.log(b)
        kval = 2*d*(mp.log(mp.pi*b/2)-1)
        c = mp.mpf('0.0000001')
        atom = mp.sin(mp.pi*d*c)/mp.pi
        # The interior quotient has a removable limit -2(b-1)/b at x=0.
        def interior(t):
            if not t:
                return mp.mpf(-2)*d/b
            x = b*c*t
            return (transfer_mp(b,c,H,x)-H(x)-atom)/H(x)
        inside = b*c*mp.quad(interior,[0,mp.mpf('.25'),mp.mpf('.6'),1])
        outside = (1-b*c)*(mp.cos(mp.pi*d*c)-1)+2/mp.pi*mp.sin(mp.pi*d*c)*mp.log(mp.sin(mp.pi*b*c/2))
        a22 = inside+outside
        a11 = transfer_mp(b,c,G,mp.mpf(0))-1
        trace.append(dict(base=b,phase=str(c),a11_over_c=str(a11/c),a11_limit=str(r),
                          a22_renormalized=str(a22/c+2*d*mp.log(1/c)),a22_limit=str(kval)))
    # Exact binary finite-part identity, tested against high-precision quadrature.
    binary = []
    for c in (mp.mpf('.01'),mp.mpf('.001')):
        exact = -2*c+(1-2*c)*(mp.cos(mp.pi*c)-1)+2/mp.pi*mp.sin(mp.pi*c)*mp.log(mp.sin(mp.pi*c))
        f = lambda x: ((transfer_mp(2,c,H,x)-H(x)-mp.sin(mp.pi*c)/mp.pi)/H(x))
        eps=mp.mpf('1e-30')
        direct=mp.quad(f,[eps,2*c,mp.mpf('.2'),mp.mpf('.7'),1-eps])
        binary.append(dict(phase=str(c),truncated_integral_residual=str(abs(direct-exact)),cutoff=str(eps)))
    return dict(precision_digits=70,jordan=rows,response=response,finite_part=trace,binary_trace=binary)


def main() -> None:
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--identities-only',action='store_true')
    # ed. (2026-09-29): default recomputed/, so a plain run no longer
    # overwrites the recorded data/ (receipt and the two \input tables).
    parser.add_argument('--output-dir',type=Path,default=Path(__file__).resolve().parents[1]/'recomputed')
    args=parser.parse_args()
    args.output_dir.mkdir(parents=True,exist_ok=True)
    start=time.time()
    data=dict(status='Diagnostics only; not interval or proof-assistant certification.',
              versions=dict(python=platform.python_version(),numpy=np.__version__,scipy=scipy.__version__,mpmath=mp.__version__),
              identities=identities())
    if not args.identities_only:
        pressure=[]
        for b in (2,3):
            for c,mesh in ((1e-3,65536),(1e-4,262144),(1e-5,262144),(1e-6,1048576)):
                row=eigendata(b,1,c,mesh)
                d=b-1; k=math.sqrt(2*d*math.log(b)); const=b*math.log(b)+d*(float(mp.euler)-1)
                row.update(leading_ratio=row['pressure']/(k*math.sqrt(c)),
                           logarithm_corrected_coefficient=(row['pressure']-k*math.sqrt(c)+d*c*math.log(1/c))/c,
                           predicted_linear_coefficient=const,
                           predicted_three_term_pressure=k*math.sqrt(c)-d*c*math.log(1/c)+const*c)
                pressure.append(row)
                print('pressure',b,c,row['pressure'],row['logarithm_corrected_coefficient'],flush=True)
        data['pressure']=pressure
        data['mesh_comparisons']=[eigendata(2,1,1e-6,2097152)]
        selection=[]
        for u in (-2.,0.,2.):
            for c in (1e-4,1e-5):
                s=1+u*math.sqrt(c)
                row=eigendata(2,s,c,262144,measure=True)
                aa=u*math.log(2)
                row.update(detuning=u,predicted_cosine_moment=0.5*(1+aa/math.sqrt(aa*aa+8*math.log(2))))
                selection.append(row)
                print('selection',u,c,row['cosine_moment'],row['predicted_cosine_moment'],flush=True)
        data['selection']=selection
        tab=['\\begin{tabular}{@{}rrrrr@{}}','\\toprule',
             '$b$ & $c$ & $P_{b,1}(c)/\\sqrt{|c|}$ & $R_b(c)$ & $B_b$\\\\','\\midrule']
        for r in pressure:
            c_tex = f"10^{{{int(round(math.log10(r['phase'])))}}}"
            tab.append(f"{r['base']} & ${c_tex}$ & {r['pressure']/math.sqrt(r['phase']):.8f} & {r['logarithm_corrected_coefficient']:.6f} & {r['predicted_linear_coefficient']:.6f}\\\\")
        tab.extend(['\\bottomrule','\\end{tabular}'])
        (args.output_dir/'pressure_table.tex').write_text('\n'.join(tab)+'\n',newline='\n')  # ed. (2026-09-29): LF
        tab=['\\begin{tabular}{@{}rrrr@{}}','\\toprule',
             '$u$ & $c$ & numerical $\\int\\cos(2\\pi x)\\,d\\mu$ & predicted limit\\\\','\\midrule']
        for r in selection:
            c_tex = f"10^{{{int(round(math.log10(r['phase'])))}}}"
            tab.append(f"{r['detuning']:.0f} & ${c_tex}$ & {r['cosine_moment']:.8f} & {r['predicted_cosine_moment']:.8f}\\\\")
        tab.extend(['\\bottomrule','\\end{tabular}'])
        (args.output_dir/'selection_table.tex').write_text('\n'.join(tab)+'\n',newline='\n')  # ed. (2026-09-29): LF
    data['elapsed_seconds']=time.time()-start
    (args.output_dir/'verification.json').write_text(json.dumps(data,indent=2)+'\n',newline='\n')  # ed. (2026-09-29): LF
    print('Wrote diagnostics to',args.output_dir,'seconds',data['elapsed_seconds'],flush=True)

if __name__=='__main__':
    main()
