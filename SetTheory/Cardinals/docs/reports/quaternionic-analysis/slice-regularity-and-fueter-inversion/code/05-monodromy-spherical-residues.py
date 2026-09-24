#!/usr/bin/env python3
"""Reproducible algebraic and numerical checks for the accompanying article.

These checks are independent diagnostics, NOT a formal verification of the proofs.
No network access is used. Requires Python 3.10+, sympy, numpy, and mpmath.
Run: python verify.py
"""
from __future__ import annotations

import json
import math
from pathlib import Path

import mpmath as mp
import numpy as np
import sympy as sp


def symbolic_checks() -> dict[str, bool]:
    x, y, u, v = sp.symbols('x y u v', real=True)
    s, t = x-u, y-v
    d = s*s+t*t
    ell = sp.log(d)/2
    P0 = s/(sp.pi*y*d)
    Q0 = ell/(sp.pi*y*y)-t/(sp.pi*y*d)
    P1 = (x*s+y*t)/(sp.pi*y*d)+ell/(sp.pi*y)
    Q1 = (y*s-x*t)/(sp.pi*y*d)+x*ell/(sp.pi*y*y)
    out: dict[str, bool] = {}
    for label, P, Q in [('single_log', P0, Q0), ('z_single_log', P1, Q1)]:
        out[label+'_vekua_1'] = sp.simplify(sp.diff(P,x)-sp.diff(Q,y)-2*Q/y) == 0
        out[label+'_vekua_2'] = sp.simplify(sp.diff(Q,x)+sp.diff(P,y)) == 0
        ax, ay = -P/2, Q/2
        bx, by = (x*P+y*Q)/2, (y*P-x*Q)/2
        out[label+'_alpha_closed'] = sp.simplify(sp.diff(ay,x)-sp.diff(ax,y)) == 0
        out[label+'_beta_closed'] = sp.simplify(sp.diff(by,x)-sp.diff(bx,y)) == 0
    # Check the exact differential of the real and imaginary parts of log.
    # A=arg(z-a)/(2*pi), B=-log|z-a|/(2*pi).
    Ax, Ay = -t/(2*sp.pi*d), s/(2*sp.pi*d)
    B, Bx, By = -ell/(2*sp.pi), -s/(2*sp.pi*d), -t/(2*sp.pi*d)
    out['single_log_laplacian_P'] = sp.simplify(2*Ay/y-P0) == 0
    out['single_log_laplacian_Q'] = sp.simplify(2*By/y-2*B/y**2-Q0) == 0
    # z(A+iB) has real part xA-yB, imaginary part yA+xB;
    # the undifferentiated A cancels from the Laplacian.
    out['z_log_laplacian_P'] = sp.simplify(2*(x*Ay-B-y*By)/y-P1) == 0
    out['z_log_laplacian_Q'] = sp.simplify(2*(y*Ay+x*By)/y-2*x*B/y**2-Q1) == 0
    # Leading energy identity, coordinate by coordinate (all products real).
    c, h, ss, tt, vv = sp.symbols('c h s t v', real=True)
    out['energy_quadratic_identity'] = sp.expand(
        (c*ss+vv*h*tt)**2+(vv*h*ss-c*tt)**2
        -(c*c+vv*vv*h*h)*(ss*ss+tt*tt)) == 0
    # The reflected modes are differences of two such solutions.
    if not all(out.values()):
        raise AssertionError(f'Symbolic check failed: {out}')
    return out


def modes_mp(x: mp.mpf, y: mp.mpf, u: mp.mpf, v: mp.mpf):
    """Reflected-log modes (Phi P,Q; Psi P,Q), real arguments, y,v>0."""
    s = x-u
    dm, dp = s*s+(y-v)**2, s*s+(y+v)**2
    ell = mp.log(dm/dp)/2
    H = 1/dm-1/dp
    T = (y-v)/dm-(y+v)/dp
    P0 = s*H/(mp.pi*y)
    Q0 = ell/(mp.pi*y*y)-T/(mp.pi*y)
    P1 = (x*s*H+y*T+ell)/(mp.pi*y)
    Q1 = (y*s*H-x*T)/(mp.pi*y)+x*ell/(mp.pi*y*y)
    return ((P0,Q0),(P1,Q1))


def periods() -> dict[str, float]:
    mp.mp.dps = 45
    centers = [(mp.mpf('-0.7'),mp.mpf('1.2')),
               (mp.mpf('0.8'),mp.mpf('1.5'))]
    radius = mp.mpf('0.19')
    errors: dict[str,float] = {}
    for j,(u,v) in enumerate(centers):
        for k,(cx,cy) in enumerate(centers):
            for mode in [0,1]:
                def integrand(theta, which):
                    x = cx+radius*mp.cos(theta)
                    y = cy+radius*mp.sin(theta)
                    dx = -radius*mp.sin(theta)
                    dy = radius*mp.cos(theta)
                    P,Q = modes_mp(x,y,u,v)[mode]
                    if which == 0:
                        return (-P*dx+Q*dy)/2
                    return ((x*P+y*Q)*dx+(y*P-x*Q)*dy)/2
                for which in [0,1]:
                    val = mp.quad(lambda t:integrand(t,which),
                                  [0,mp.pi/2,mp.pi,3*mp.pi/2,2*mp.pi])
                    expected = int(j == k and ((mode==0 and which==1) or
                                                (mode==1 and which==0)))
                    err = float(abs(val-expected))
                    errors[f'center{j}_loop{k}_mode{mode}_period{which}'] = err
                    if err > 1e-30:
                        raise AssertionError((j,k,mode,which,val,expected))
    return errors


def modes_np(x, y, u, v):
    s = x-u
    dm, dp = s*s+(y-v)**2, s*s+(y+v)**2
    ell = np.log(dm/dp)/2
    H, T = 1/dm-1/dp, (y-v)/dm-(y+v)/dp
    P0, Q0 = s*H/(np.pi*y), ell/(np.pi*y*y)-T/(np.pi*y)
    P1 = (x*s*H+y*T+ell)/(np.pi*y)
    Q1 = (y*s*H-x*T)/(np.pi*y)+x*ell/(np.pi*y*y)
    return P0,Q0,P1,Q1


def energy_check() -> dict:
    u,v = 0.4,1.3
    h = np.array([1.,2.,-1.,0.5])
    k = np.array([0.25,-1.,3.,2.])
    c = u*h+k
    coefficient = 8*(np.dot(c,c)+v*v*np.dot(h,h))
    assert abs(coefficient-181.0) < 1e-12
    na,nr=160,160
    xa,wa=np.polynomial.legendre.leggauss(na)
    theta,wa=np.pi*(xa+1),np.pi*wa
    xr,wr=np.polynomial.legendre.leggauss(nr)
    def shell_density(rho):
        x,y=u+rho*np.cos(theta),v+rho*np.sin(theta)
        P0,Q0,P1,Q1=modes_np(x,y,u,v)
        P=P1[:,None]*h+P0[:,None]*k
        Q=Q1[:,None]*h+Q0[:,None]*k
        n2=np.sum(P*P+Q*Q,axis=1)
        return 4*np.pi*np.dot(wa,y*y*n2*rho*rho)
    R=0.3
    rows=[]
    for eps in [1e-2,1e-3,1e-4,1e-5]:
        lo,hi=math.log(eps),math.log(R)
        t=(hi+lo)/2+(hi-lo)*xr/2
        e=(hi-lo)/2*np.dot(wr,np.array([shell_density(math.exp(ti)) for ti in t]))
        remainder=e-coefficient*math.log(R/eps)
        rows.append({'epsilon':eps,'energy':float(e),
                     'energy_minus_predicted_log':float(remainder),
                     'shell_density':float(shell_density(eps))})
    if abs(rows[-1]['shell_density']-coefficient) > 1e-4:
        raise AssertionError(rows)
    return {'u':u,'v':v,'h':h.tolist(),'k':k.tolist(),
            'outer_radius':R,'predicted_log_coefficient':coefficient,'rows':rows}


def quat_mul(p,q):
    p0,pv=p[0],np.asarray(p[1:]); q0,qv=q[0],np.asarray(q[1:])
    return np.r_[p0*q0-np.dot(pv,qv),p0*qv+q0*pv+np.cross(pv,qv)]


def sphere_average_check() -> float:
    rng=np.random.default_rng(20260921)
    units=[np.r_[0.,sign*np.eye(3)[j]] for j in range(3) for sign in [-1,1]]
    err=0.
    for _ in range(20):
        P,Q=rng.normal(size=(2,4))
        avg=sum(np.dot(P+quat_mul(I,Q),P+quat_mul(I,Q)) for I in units)/6
        err=max(err,abs(avg-np.dot(P,P)-np.dot(Q,Q)))
    if err>1e-12:raise AssertionError(err)
    return err


def layer_check() -> dict[str, float]:
    """Independently integrate the four-dimensional Cauchy layer on S_a."""
    u, v = 0.4, 1.3
    h = np.array([1., 2., -1., .5])
    k = np.array([.25, -1., 3., 2.])
    xi, wi = np.polynomial.legendre.leggauss(48)
    phis = np.arange(96)*2*np.pi/96
    errors = {}
    for label, q in [('nonreal', np.array([.8, .4, .2, -.1])),
                     ('real', np.array([-.3, 0., 0., 0.]))]:
        integral = np.zeros(4)
        for t, w in zip(xi, wi):
            for phi in phis:
                unit = np.array([np.sqrt(1-t*t)*np.cos(phi),
                                 np.sqrt(1-t*t)*np.sin(phi), t])
                p = np.r_[u, v*unit]
                diff = q-p
                kernel = np.r_[diff[0], -diff[1:]]/(2*np.pi**2*np.dot(diff,diff)**2)
                integral += (2*v*w*2*np.pi/96)*quat_mul(kernel, quat_mul(p,h)+k)
        x, y = q[0], np.linalg.norm(q[1:])
        if y:
            P0,Q0,P1,Q1 = modes_np(x,y,u,v)
            unit = np.r_[0., q[1:]/y]
            target = P1*h+P0*k+quat_mul(unit, Q1*h+Q0*k)
        else:
            d=(x-u)**2+v*v
            P0=4*v*(x-u)/(np.pi*d*d)
            P1=-4*v/(np.pi*d)+4*x*v*(x-u)/(np.pi*d*d)
            target=P1*h+P0*k
        error=float(np.linalg.norm(target-integral))
        errors[label+'_absolute_error']=error
        if error>1e-10:
            raise AssertionError((label,error,target,integral))
    return errors


def main() -> None:
    result={'status':'PASS (algebra and finite numerical diagnostics only)',
            'symbolic':symbolic_checks(),
            'period_errors':periods(),
            'sphere_average_max_error':sphere_average_check(),
            'sphere_layer_errors':layer_check(),
            'energy':energy_check(),
            'versions':{'sympy':sp.__version__,'numpy':np.__version__,
                        'mpmath':mp.__version__}}
    out=Path(__file__).with_name('verification_results.json')
    out.write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
    print(json.dumps(result,indent=2))


if __name__=='__main__':
    main()
