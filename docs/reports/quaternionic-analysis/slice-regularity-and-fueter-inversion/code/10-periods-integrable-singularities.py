#!/usr/bin/env python3
"""Independent algebraic and numerical checks for the accompanying paper.

These checks do not replace the mathematical proofs. Run with Python 3.10+,
SymPy, and NumPy. Results are deterministic and saved beside this script.
"""
from __future__ import annotations

import json
import math
from pathlib import Path

import numpy as np
import sympy as sp


def symbolic_checks() -> dict[str, bool]:
    x, r, u, v = sp.symbols('x r u v', real=True)
    s = (x-u)**2 + (r-v)**2
    L = sp.log(s)/2
    P0 = (x-u)/(sp.pi*r*s)
    Q0 = -(r-v)/(sp.pi*r*s) + L/(sp.pi*r**2)
    P1 = (L + (x*(x-u)+r*(r-v))/s)/(sp.pi*r)
    Q1 = (x*v-r*u)/(sp.pi*r*s) + x*L/(sp.pi*r**2)
    checks: dict[str, bool] = {}
    for name, P, Q in [('constant', P0, Q0), ('linear', P1, Q1)]:
        tests = {
            'vekua_1': sp.diff(P,x)-sp.diff(Q,r)-2*Q/r,
            'vekua_2': sp.diff(Q,x)+sp.diff(P,r),
            'omega_closed': sp.diff(Q/2,x)+sp.diff(P/2,r),
            'eta_closed': sp.diff((r*P-x*Q)/2,x)-sp.diff((x*P+r*Q)/2,r),
        }
        for test, expr in tests.items():
            checks[f'{name}_{test}'] = sp.simplify(expr) == 0
    # The leading singular coefficient in the angular energy is constant.
    t, c0, c1 = sp.symbols('t c0 c1', real=True)
    checks['angular_energy_identity'] = sp.trigsimp(
        (c0*sp.cos(t)+c1*sp.sin(t))**2 +
        (-c0*sp.sin(t)+c1*sp.cos(t))**2-c0**2-c1**2) == 0
    # General holomorphic polynomial, with no reality restriction on upper data.
    z = x+sp.I*r
    F = (1+2*sp.I)*z**4+(3-sp.I)*z**2+(2+sp.I)*z-4*sp.I
    A, B = sp.expand_complex(F).as_real_imag()
    P = 2*sp.diff(A,r)/r
    Q = 2*(sp.diff(B,r)/r-B/r**2)
    C, D = B/r, A-x*B/r
    checks['potential_C_x'] = sp.simplify(sp.diff(C,x)+P/2) == 0
    checks['potential_C_r'] = sp.simplify(sp.diff(C,r)-Q/2) == 0
    checks['potential_D_x'] = sp.simplify(sp.diff(D,x)-(x*P+r*Q)/2) == 0
    checks['potential_D_r'] = sp.simplify(sp.diff(D,r)-(r*P-x*Q)/2) == 0
    if not all(checks.values()):
        raise AssertionError(f'Symbolic check failed: {checks}')
    return checks


def modes(x: np.ndarray, r: np.ndarray, u: float, v: float):
    s = (x-u)**2+(r-v)**2
    if np.any(s <= 0) or np.any(r <= 0):
        raise ValueError('Evaluation points must have r>0 and avoid the pole.')
    L = 0.5*np.log(s)
    P0 = (x-u)/(math.pi*r*s)
    Q0 = -(r-v)/(math.pi*r*s)+L/(math.pi*r*r)
    P1 = (L+(x*(x-u)+r*(r-v))/s)/(math.pi*r)
    Q1 = (x*v-r*u)/(math.pi*r*s)+x*L/(math.pi*r*r)
    return P0,Q0,P1,Q1


def circle_periods(u: float, v: float, radius: float, n: int = 16384):
    t = (np.arange(n)+0.5)*(2*math.pi/n)
    x,r = u+radius*np.cos(t),v+radius*np.sin(t)
    dx,dr = -radius*np.sin(t),radius*np.cos(t)
    P0,Q0,P1,Q1 = modes(x,r,u,v)
    def integrate(P,Q):
        a = float(np.mean((-P*dx+Q*dr)/2)*2*math.pi)
        b = float(np.mean(((x*P+r*Q)*dx+(r*P-x*Q)*dr)/2)*2*math.pi)
        return [a,b]
    return {'G0':integrate(P0,Q0),'G1':integrate(P1,Q1)}


def numerical_checks():
    u,v = 0.4,1.7
    periods = {str(radius):circle_periods(u,v,radius) for radius in [0.15,0.4,0.9]}
    errors = []
    for value in periods.values():
        errors.extend(abs(np.asarray(value['G0'])-np.array([0.0,1.0])))
        errors.extend(abs(np.asarray(value['G1'])-np.array([1.0,0.0])))
    max_error = float(max(errors))
    if max_error > 1e-11:
        raise AssertionError(f'Period error too large: {max_error}')
    # Non-real right quaternionic coefficients (stored in the basis 1,i,j,k).
    a = np.array([1.0,0.2,-0.3,0.7])
    b = np.array([-0.4,0.5,0.9,-1.1])
    c0,c1 = u*a+b,v*a
    limit = float(8*(c0@c0+c1@c1))
    n = 32768
    t=(np.arange(n)+0.5)*(2*math.pi/n)
    rows=[]
    for rho in [0.1,0.03,0.01,0.003,0.001,0.0003,0.0001,0.00003]:
        x,r=u+rho*np.cos(t),v+rho*np.sin(t)
        P0,Q0,P1,Q1=modes(x,r,u,v)
        P=P1[:,None]*a+P0[:,None]*b
        Q=Q1[:,None]*a+Q0[:,None]*b
        squared=np.sum(P*P+Q*Q,axis=1)
        density=float(4*math.pi*rho*rho*2*math.pi*np.mean(r*r*squared))
        rows.append({'rho':rho,'logarithmic_shell_energy':density,
                     'predicted_limit':limit,'absolute_error':abs(density-limit)})
    if rows[-1]['absolute_error'] > 1e-5:
        raise AssertionError('Energy limit check failed.')
    # The I-average is exact. If n*g=R+I*S and H=h0+I*r, its
    # two relevant spherical averages are R and h0*R-r*S.
    fluxes = []
    expected0 = 8*math.pi*v*c0
    expected1 = -8*math.pi*v**3*a
    max_flux_error = 0.0
    for rho in [0.15,0.4,0.9]:
        x,r = u+rho*np.cos(t),v+rho*np.sin(t)
        P0,Q0,P1,Q1 = modes(x,r,u,v)
        P = P1[:,None]*a+P0[:,None]*b
        Q = Q1[:,None]*a+Q0[:,None]*b
        R = np.cos(t)[:,None]*P-np.sin(t)[:,None]*Q
        S = np.sin(t)[:,None]*P+np.cos(t)[:,None]*Q
        h0 = 3*(x-u)
        factor = 8*math.pi**2*rho
        phi0 = factor*np.mean(r[:,None]**2*R,axis=0)
        phi1 = factor*np.mean(r[:,None]**2*(h0[:,None]*R-r[:,None]*S),axis=0)
        err = float(max(np.max(np.abs(phi0-expected0)),np.max(np.abs(phi1-expected1))))
        max_flux_error = max(max_flux_error,err)
        fluxes.append({'rho':rho,'Phi0':phi0.tolist(),'Phi1':phi1.tolist(),
                       'max_component_error':err})
    if max_flux_error > 1e-10:
        raise AssertionError(f'Conserved flux error too large: {max_flux_error}')
    return {'pole':{'u':u,'v':v},'periods':periods,'max_period_error':max_error,
            'a':a.tolist(),'b':b.tolist(),'energy_limit':limit,'energy_shells':rows,
            'expected_Phi0':expected0.tolist(),'expected_Phi1':expected1.tolist(),
            'conserved_fluxes':fluxes,'max_flux_error':max_flux_error}


def main():
    result={'symbolic':symbolic_checks(),'numerical':numerical_checks(),
            'versions':{'numpy':np.__version__,'sympy':sp.__version__},
            'scope':'Finite symbolic identities and floating-point checks; not formal verification.'}
    out=Path(__file__).resolve().parent
    (out/'verification_results.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
    lines=['ALL CHECKS PASSED',f"Symbolic checks: {len(result['symbolic'])}",
           f"Maximum period error: {result['numerical']['max_period_error']:.3e}",
           f"Maximum conserved flux component error: {result['numerical']['max_flux_error']:.3e}",
           f"Predicted energy coefficient: {result['numerical']['energy_limit']:.12g}",
           'rho             shell energy           absolute error']
    lines.extend(f"{x['rho']:<15.6g} {x['logarithmic_shell_energy']:<22.13g} {x['absolute_error']:.5e}"
                 for x in result['numerical']['energy_shells'])
    text='\n'.join(lines)+'\n'
    (out/'verification_results.txt').write_text(text,encoding='utf-8')
    print(text)

if __name__=='__main__':
    main()
