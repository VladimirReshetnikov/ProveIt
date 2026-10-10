#!/usr/bin/env python3
"""Symbolic identities and explicitly NON-certified numerical diagnostics."""
from __future__ import annotations
import json
from pathlib import Path
import sys
import math
import mpmath as mp
import numpy as np
import sympy as sp
from scipy.special import roots_genlaguerre, roots_jacobi, gamma

ROOT=Path(__file__).resolve().parents[1]

def symbolic_checks() -> dict:
    u,m,x,xi,r,c=sp.symbols('u m x xi r c', real=True)
    D=1+x*(u*u-(1+m)*u)
    d=u*u-(1+m)*u
    checks={
      'critical_G_m':sp.diff((m-u)/D,m)-(1-x*u)/D**2,
      'critical_polynomial_factor':d+m-(u-m)*(u-1),
      'critical_difference_quotient':d/D-(-m)/(1-x*m)-(u-m)*(u-1)/(D*(1-x*m)),
      'left_atom_G_m':sp.diff((m-u)/(1+x*(u*u-m*u)),m)-1/(1+x*(u*u-m*u))**2,
      'circle_kernel_ratio':sp.diff((1-2*r*c*u+r*r*u*u)/(1-2*r*xi*u+r*r*u*u),u)-2*r*(xi-c)*(1-r*r*u*u)/(1-2*r*xi*u+r*r*u*u)**2,
    }
    c2,c3,c4,c5=sp.symbols('c2 c3 c4 c5',positive=True)
    mean=(c3-c2)/c2
    second=(c4-c3)/c2
    third=(c5-c4)/c2
    variance_expression=sp.Rational(1,2)*(second-third-2*mean*(mean-second)+mean**2*(1-mean))
    target=c3*c4/c2**2-c5/(2*c2)-c3**3/(2*c2**3)
    checks['critical_small_radius_identity']=variance_expression-target
    # Direct rational identities for the imaginary parts (z = p+i q).
    p,q,s,t=sp.symbols('p q s t',real=True)
    z=p+sp.I*q
    denom=(1-s*z)*(1-t*z)
    denabs=(1-2*s*p+s*s*(p*p+q*q))*(1-2*t*p+t*t*(p*p+q*q))
    checks['disk_Pick_imaginary_part']=sp.im(z*sp.conjugate(denom))-q*(1-s*t*(p*p+q*q))
    checks['F_circle_imaginary_part']=sp.im(z*z*sp.conjugate(denom))-q*(2*p-(s+t)*(p*p+q*q))
    checks['Gaussian_denominator']=(1-s*t)**2+(s+t)**2-(1+s*s)*(1+t*t)
    results={name:sp.simplify(expr)==0 for name,expr in checks.items()}
    assert all(results.values()), results
    return results

def h_np(t):
    t=np.asarray(t,dtype=float)
    out=np.empty_like(t)
    small=t<1e-3
    v=t[small]
    out[small]=.5+v/12-v**3/720+v**5/30240-v**7/1209600
    v=t[~small]
    out[~small]=-1/np.expm1(-v)-1/v
    return out

def beta_rule(a,b,n=96):
    # SciPy evaluates an unused 0/0 branch at a+b=1 in its Jacobi
    # recurrence. Suppress only that local floating-point warning, then
    # explicitly reject any non-finite output.
    with np.errstate(invalid="ignore", divide="ignore"):
        nodes,weights=roots_jacobi(n,a-1,b-1)
    assert np.all(np.isfinite(nodes)) and np.all(np.isfinite(weights))
    assert np.all(weights > 0)
    return (nodes+1)/2,weights/np.sum(weights)

def expected_h(T,a,b,n=96):
    v,w=beta_rule(a,b,n)
    return np.dot(h_np(T*v),w)

def kernel(T,a,b):
    w=a+b
    C=T**(w-1)/gamma(w)*expected_h(T,a,b)
    if b==1:
        return T**(a-1)/gamma(a)*(float(mp.euler+mp.digamma(a))-math.log(T))-C
    if abs(w-1)<1e-12:
        return float(mp.zeta(b))*T**(a-1)/gamma(a)-C
    return float(mp.zeta(b))*T**(a-1)/gamma(a)-T**(w-2)/((b-1)*gamma(w-1))-C

def moment_diagnostics():
    parameters=[(.25,.9),(.4,.7),(.5,1.),(.2,1.5),(.75,.5),(1.,.5),(1.5,.4),(2.5,2.),(.1,.9),(.5,.5)]
    rows=[]
    for a,b in parameters:
        w=a+b
        v,vweights=beta_rule(a,b,96)
        nodes,weights=roots_genlaguerre(128,w-1)
        weights=weights/np.sum(weights)
        for n in [1,2,3,7,15]:
            conv=n**(-w)*np.dot(weights,np.dot(h_np(nodes[:,None]*v[None,:]/n),vweights))
            if b==1:
                value=n**(-a)*(float(mp.euler)+math.log(n))-conv
            elif abs(w-1)<1e-12:
                value=1/(1-b)+float(mp.zeta(b))*n**(-a)-conv
            else:
                value=float(mp.zeta(b))*n**(-a)-n**(-(w-1))/(b-1)-conv
            direct=sum(k**(-b) for k in range(1,n))/n**a
            err=abs(value-direct)
            assert err<2e-10,(a,b,n,err)
            rows.append({'a':a,'b':b,'n':n,'absolute_error':err})
    return rows

def direct_coefficients(a,b,N=260):
    h=mp.mpf(0); cs=[mp.mpf(0)]
    for n in range(1,N+1):
        cs.append(h/mp.power(n,a))
        h+=mp.power(n,-b)
    return cs

def angle_eval(cs,rho,c):
    Uprev=mp.mpf(0);U=mp.mpf(1);rp=rho; value=mp.mpf(0)
    for cn in cs[1:]:
        value+=cn*rp*U
        Uprev,U=U,2*c*U-Uprev
        rp*=rho
    return value

def root_proposals():
    from fractions import Fraction
    mp.mp.dps=65
    rows=[]
    params=[('1/10','9/10'),('1/2','1/2'),('9/10','1/10')]
    cases=[(a,b,r) for a,b in params for r in ['1/4','1/2','3/4']]
    cases += [('3/4','1/2','1/2'),('1/4','1','1/2'),('1/4','1/4','1/2')]
    for aa,bb,rr in cases:
        def cv(s):
            q=Fraction(s);return mp.mpf(q.numerator)/q.denominator
        a,b,rho=cv(aa),cv(bb),cv(rr)
        cs=direct_coefficients(a,b,240)
        lo=mp.mpf(0);hi=rho
        for _ in range(125):
            mid=(lo+hi)/2
            if angle_eval(cs,rho,mid)>0:hi=mid
            else:lo=mid
        center=(lo+hi)/2
        scale=10**12
        left=int(mp.floor(center*scale))-2
        right=left+5
        rows.append({'a':aa,'b':bb,'rho':rr,'N':240,
                     'c_lower':str(Fraction(left,scale)),
                     'c_upper':str(Fraction(right,scale)),
                     'approximate_c':mp.nstr(center,28),
                     'approximate_eta':mp.nstr(center/rho,28)})
    (ROOT/'data/root_proposals.json').write_text(json.dumps(rows,indent=2)+'\n')
    return rows

def gaussian_double_quadrature(a,b,N=192):
    nx,wx=roots_genlaguerre(N,a-1);ny,wy=roots_genlaguerre(N,b-1)
    wx=wx/np.sum(wx);wy=wy/np.sum(wy)
    s=np.exp(-nx[:,None]/2);t=s*np.exp(-ny[None,:])
    return -2**(-a)*float(np.dot(wx,np.dot((s+t)/((1+s*s)*(1+t*t)),wy)))

if __name__=='__main__':
    symbols=symbolic_checks()
    moments=moment_diagnostics()
    proposals=root_proposals()
    diagnostics={'status':'Numerical rows are diagnostics, not interval certificates.',
      'symbolic_checks':symbols,'moment_diagnostics':moments,
      'max_moment_error':max(r['absolute_error'] for r in moments),
      'gaussian_double_quadrature':[{'a':a,'b':1-a,'value':gaussian_double_quadrature(a,1-a)} for a in [.1,.5,.9]],
      'critical_normalized_radial_rows':proposals[:9]}
    (ROOT/'data/diagnostics.json').write_text(json.dumps(diagnostics,indent=2)+'\n')
    print(json.dumps({'symbolic_checks':len(symbols),'moment_diagnostics':len(moments),
                     'max_moment_error':diagnostics['max_moment_error'],
                     'root_proposals':len(proposals)},indent=2))
