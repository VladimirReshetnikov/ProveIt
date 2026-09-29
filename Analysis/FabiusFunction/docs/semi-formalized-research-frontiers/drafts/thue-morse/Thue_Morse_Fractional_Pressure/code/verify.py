#!/usr/bin/env python3
"""Checks for Fractional Cusps at the Atomic Phase.

Collocation is a numerical diagnostic, not an interval certificate.
The paper's proofs do not depend on the numerical output.
Dependencies: numpy, sympy, mpmath. Run from the package root:
    python code/verify.py
"""
from __future__ import annotations
import argparse
import json
import math
from pathlib import Path
import numpy as np
import mpmath as mp
import sympy as sp


def h_atomic(s: mp.mpf, x: mp.mpf) -> mp.mpf:
    """Periodized absolute sinc power (Hurwitz-zeta representation), s > 1."""
    if s <= 1:
        raise ValueError("s must exceed 1")
    x = x % 1
    if x == 0:
        return mp.mpf(1)
    return (mp.sin(mp.pi*x)/mp.pi)**s * (mp.zeta(s,x)+mp.zeta(s,1-x))


def weight(b: int, s: float, x: np.ndarray) -> np.ndarray:
    """Stable periodic digital-mask power."""
    z = (x+0.5) % 1.0 - 0.5
    return np.abs(np.sinc(b*z)/np.sinc(z))**s


def pressure_collocation(b: int, s: float, c: float, grid: int = 65536,
                         tol: float = 3e-14, max_iter: int = 800) -> dict:
    """Positive piecewise-linear collocation, normalized at the atomic point."""
    if b < 2 or s <= 1 or grid < b*16:
        raise ValueError("Require b >= 2, s > 1 and a sufficiently large grid")
    grid = ((grid+b-1)//b)*b
    i = np.arange(grid, dtype=np.float64)
    x = i/grid
    data = []
    for j in range(b):
        y = (x+j)/b
        u = (i+j*grid)/b
        floor = np.floor(u)
        lo = floor.astype(np.int64) % grid
        t = u-floor
        data.append((lo, (lo+1)%grid, t, weight(b,s,y-c)))
    h = np.ones(grid)
    residual = math.inf
    for step in range(max_iter):
        out = np.zeros(grid)
        for lo,hi,t,w in data:
            out += w*((1-t)*h[lo]+t*h[hi])
        rho = float(out[0])
        if rho <= 0 or not np.isfinite(rho):
            raise ArithmeticError("Iteration lost a positive finite normalization")
        out /= rho
        residual = float(np.max(np.abs(out-h)))
        h = out
        if residual < tol:
            break
    else:
        raise RuntimeError(f"Iteration did not converge: residual={residual}")
    # Scaled formula avoids subtracting two close logarithms.
    bsum = math.fsum(float(h[j*grid//b])/abs(math.sin(math.pi*(j/b-c)))**s
                     for j in range(1,b))
    scaled_excess = math.log1p(abs(math.sin(math.pi*c))**s*bsum)/abs(c)**s
    d0 = float(np.sinc(b*c)/np.sinc(c))
    return {"base":b,"s":s,"phase":c,"grid":grid,"iterations":step+1,
            "iteration_residual":residual,"rho":rho,"pressure":math.log(rho),
            "scaled_excess":scaled_excess,
            "target":float(2*(mp.mpf(b)**s-1)*mp.zeta(s)),
            "atomic_branch_log":s*math.log(abs(d0))}


def high_precision_checks() -> dict:
    mp.mp.dps = 65
    identity_errors=[]
    coefficient_errors=[]
    for b in (2,3,5,7):
        for sval in ('1.25','1.5','2','2.5','3','3.5','5.25'):
            s=mp.mpf(sval)
            for xx in ('0.03125','0.21','0.5','0.83'):
                x=mp.mpf(xx)
                lh=mp.mpf(0)
                for k in range(b):
                    y=(x+k)/b
                    w=abs(mp.sin(mp.pi*b*y)/(b*mp.sin(mp.pi*y)))**s
                    lh += w*h_atomic(s,y)
                identity_errors.append(abs(lh-h_atomic(s,x)))
            lhs=mp.pi**s*sum(h_atomic(s,mp.mpf(k)/b)/
                                abs(mp.sin(mp.pi*k/b))**s for k in range(1,b))
            rhs=2*(mp.mpf(b)**s-1)*mp.zeta(s)
            coefficient_errors.append(abs(lhs-rhs))
    assert max(identity_errors) < mp.mpf('1e-58')
    assert max(coefficient_errors) < mp.mpf('1e-58')
    # Exact rational identity after removing the common zeta value.
    b=sp.symbols('b', integer=True, positive=True)
    for m in range(1,21):
        assert sp.expand(-sp.Rational(2*m,m)*(b**(2*m)-1)
                         +2*(b**(2*m)-1)) == 0
    return {"precision_decimal_digits":mp.mp.dps,
            "atomic_eigenfunction_tests":len(identity_errors),
            "largest_atomic_identity_error":str(max(identity_errors)),
            "amplitude_tests":len(coefficient_errors),
            "largest_amplitude_error":str(max(coefficient_errors)),
            "exact_integer_cancellations_checked":20}


def main() -> None:
    parser=argparse.ArgumentParser()
    parser.add_argument('--grid', type=int, default=65536)
    parser.add_argument('--output', type=Path, default=Path('results/verification.json'))
    parser.add_argument('--skip-numerics', action='store_true')
    args=parser.parse_args()
    record={"status":"Diagnostics; not a proof-assistant or interval certificate",
            "algebra_and_identities":high_precision_checks(),"cusp_diagnostics":[]}
    if not args.skip_numerics:
        for b,s in ((2,1.5),(2,2.5),(2,3.0),(2,3.5),(3,1.5),(3,2.5)):
            for c in (0.01,0.003,0.001):
                row=pressure_collocation(b,s,c,args.grid)
                record['cusp_diagnostics'].append(row)
                print(f"b={b} s={s:g} c={c:g}: scaled={row['scaled_excess']:.10f}, "
                      f"target={row['target']:.10f}")
        for b,s in ((2,1.5),(3,2.5)):
            row=pressure_collocation(b,s,0.001,2*args.grid)
            row['purpose']='grid-refinement check'
            record['cusp_diagnostics'].append(row)
    args.output.parent.mkdir(parents=True,exist_ok=True)
    args.output.write_text(json.dumps(record,indent=2)+'\n')
    print(f"Wrote {args.output}")


if __name__ == '__main__':
    main()
