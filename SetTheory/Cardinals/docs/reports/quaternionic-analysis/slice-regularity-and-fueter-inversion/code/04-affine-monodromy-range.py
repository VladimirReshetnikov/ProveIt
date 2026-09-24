#!/usr/bin/env python3
"""Independent algebraic and quadrature checks for the accompanying manuscript.

These checks are diagnostics, not substitutes for the proofs.  Requires
Python >= 3.10, SymPy, and NumPy.  No network access is used.
"""
from __future__ import annotations
import json
import math
from pathlib import Path
import numpy as np
import sympy as sp


def symbolic_checks() -> dict[str, bool]:
    x, r, a, b = sp.symbols('x r a b', real=True)
    X, Y = x-a, r-b
    D = X**2+Y**2
    P0 = X/(sp.pi*r*D)
    Q0 = -Y/(sp.pi*r*D)+sp.log(D)/(2*sp.pi*r**2)
    P1 = x*P0+sp.log(D)/(2*sp.pi*r)+Y/(sp.pi*D)
    Q1 = x*Q0+X/(sp.pi*D)
    checks: dict[str, bool] = {}
    for name, P, Q in [('B',P0,Q0),('A',P1,Q1)]:
        checks[name+'_vekua_first'] = sp.simplify(sp.diff(P,x)-sp.diff(Q,r)-2*Q/r)==0
        checks[name+'_vekua_second'] = sp.simplify(sp.diff(Q,x)+sp.diff(P,r))==0
        J = -(P+r*sp.diff(P,r))/2-sp.I*r*sp.diff(P,x)/2
        z = x+sp.I*r
        zeta = a+sp.I*b
        expected = -1/(2*sp.pi*sp.I*(z-zeta)**2)
        if name=='A':
            expected = 2/(2*sp.pi*sp.I*(z-zeta))+z*expected
        checks[name+'_second_derivative'] = sp.simplify(sp.expand_complex(J-expected))==0
    # A complex-affine stem z*(i*c)+i*d has precisely this nonzero image.
    c,d=sp.symbols('c d',real=True)
    P=-2*c/r
    Q=-2*(x*c+d)/r**2
    checks['J_kernel_vekua_first']=sp.simplify(sp.diff(P,x)-sp.diff(Q,r)-2*Q/r)==0
    checks['J_kernel_vekua_second']=sp.simplify(sp.diff(Q,x)+sp.diff(P,r))==0
    checks['J_kernel_zero']=sp.simplify(-(P+r*sp.diff(P,r))/2-sp.I*r*sp.diff(P,x)/2)==0
    return checks


def defect_values(z: np.ndarray, zeta: complex, name: str,
                  symmetric: bool=False) -> tuple[np.ndarray,np.ndarray]:
    x,r=z.real,z.imag
    if np.any(r <= 0):
        raise ValueError('Quadrature circles must stay in the upper half-plane.')
    if symmetric:
        k=zeta.imag/(np.pi*(z-zeta)*(z-zeta.conjugate()))
        d=-np.log(np.abs(z-zeta)**2/np.abs(z-zeta.conjugate())**2)/(4*np.pi)
    else:
        k=1/(2*np.pi*1j*(z-zeta))
        d=-np.log(np.abs(z-zeta)**2)/(4*np.pi)
    P=-2*k.imag/r
    Q=2*k.real/r-2*d/r**2
    if name=='A':
        P,Q=x*P-2*d/r-2*k.real,x*Q-2*k.imag
    elif name!='B':
        raise ValueError(name)
    return P,Q


def period_checks(n: int=32768) -> list[dict[str, object]]:
    t=np.arange(n)*(2*np.pi/n)
    out=[]
    zeta=0.3+1.4j
    for symmetric in (False,True):
        for radius in (0.07,0.21,0.55):
            z=zeta+radius*np.exp(1j*t)
            dz=1j*radius*np.exp(1j*t)
            for name in ('A','B'):
                P,Q=defect_values(z,zeta,name,symmetric)
                alpha=float(np.mean((-P*dz.real+Q*dz.imag)/2)*2*np.pi)
                beta=float(np.mean(((z.real*P+z.imag*Q)*dz.real+
                                    (z.imag*P-z.real*Q)*dz.imag)/2)*2*np.pi)
                target=(1.0,0.0) if name=='A' else (0.0,1.0)
                error=max(abs(alpha-target[0]),abs(beta-target[1]))
                out.append(dict(symmetric=symmetric,radius=radius,field=name,
                                alpha=alpha,beta=beta,max_error=error))
    return out


def main() -> None:
    algebra=symbolic_checks()
    quadrature=period_checks()
    ok=all(algebra.values()) and all(row['max_error']<1e-10 for row in quadrature)
    results={'symbolic_checks':algebra,'period_quadrature':quadrature,
             'all_checks_passed':ok,
             'disclaimer':'Finite diagnostics only; the manuscript gives analytic proofs.'}
    text=json.dumps(results,indent=2)
    Path(__file__).with_name('verification_results.json').write_text(text+'\n')
    print(text)
    if not ok:
        raise SystemExit('A diagnostic check failed.')

if __name__=='__main__':
    main()
