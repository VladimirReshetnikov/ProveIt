#!/usr/bin/env python3
"""Reproduce algebra and numerical illustrations for the research report.

The proofs are in the LaTeX report. These floating-point checks are not a
formal proof, and the Fourier comparison integral is not an exact transition
density. No network access or precomputed zero tables are required.
"""
from pathlib import Path
import json
import math
import numpy as np
import mpmath as mp
import sympy as sp
from scipy.integrate import quad
from scipy.special import lambertw

ROOT = Path(__file__).resolve().parents[1]
DATA = ROOT / 'data'
DATA.mkdir(exist_ok=True)

def profile(k, x):
    x = np.asarray(x, dtype=float)
    z = 1 - 1j*x
    if k == 0:
        return 1/(np.pi*(1+x*x))
    if k == 1:
        return -np.real((1-np.euler_gamma-np.log(z))/z**2)/np.pi
    if k == 2:
        return np.real(((1.5-np.euler_gamma-np.log(z))**2
                       +np.pi**2/6-1.25)/z**3)/np.pi
    raise ValueError('This implementation displays k=0,1,2.')

def comparison_integral(w, x):
    """Fourier comparison in the proof, not an exact probability density."""
    def kernel(s):
        if s == 0:
            return 1.0
        return np.exp(-s-s*np.log(s)/w)*np.cos(x*s)
    value, error = quad(kernel, 0, 1, epsabs=2e-12, epsrel=2e-12)
    v2, e2 = quad(kernel, 1, 80, epsabs=2e-12, epsrel=2e-12, limit=400)
    return (value+v2)/np.pi, (error+e2)/np.pi

def F(x, p):
    x = np.asarray(x, dtype=float)
    return x*np.log(x) + 0.5*x**(1-2/p)*np.sin(np.pi*x**(1/p))**2

def coefficients(ns, p):
    ns = np.asarray(ns, dtype=float)
    out = np.empty_like(ns)
    at_one = ns == 1
    out[at_one] = F(2, p)
    n = ns[~at_one]
    out[~at_one] = n*(F(n+1,p)-2*F(n,p)+F(n-1,p))
    return out

def remainder(x, p):
    x = np.asarray(x, dtype=float)
    n = np.floor(x)
    delta = x-n
    interpolated = (1-delta)*F(n,p)+delta*F(n+1,p)
    return interpolated/x-np.log(x)

def main():
    mp.mp.dps = 60
    report = {'status':'numerical and symbolic checks; not a Lean verification'}

    # Exact symbolic identity used to prove positivity of all coefficients.
    x,p = sp.symbols('x p', positive=True)
    h = x**(1-2/p)*sp.sin(sp.pi*x**(1/p))**2
    rhs = (-2*(p-2)/p**2*x**(-2/p)*sp.sin(sp.pi*x**(1/p))**2
           +sp.pi*(p-3)/p**2*x**(-1/p)*sp.sin(2*sp.pi*x**(1/p))
           +2*sp.pi**2/p**2*sp.cos(2*sp.pi*x**(1/p)))
    identity = sp.trigsimp(sp.expand_trig(x*sp.diff(h,x,2)-rhs))
    identity = sp.simplify(identity)
    assert identity == 0, identity
    C4 = (4+mp.pi+2*mp.pi**2)/16
    assert C4 < 2
    report['sampling_algebra'] = {'derivative_identity':'exactly zero in SymPy',
        'C4':str(C4),'uniform_coefficient_upper_bound':str(2+C4),
        'pole_location':'1 - 2/p','pole_residue':'1/4'}

    # Check the Gamma-derivative profile formula against independent quadrature.
    profile_checks = []
    for k in range(3):
        for x0 in [0,0.5,1,2,4]:
            z=mp.mpc(1,-x0)
            analytic = (-1)**k*mp.re(mp.diff(lambda s:mp.gamma(s)*z**(-s),k+1,k))/(mp.pi*mp.factorial(k))
            def integrand(u):
                if u == 0:
                    return mp.mpf(1) if k == 0 else mp.mpf(0)
                return (-1)**k*mp.e**(-u)*u**k*mp.log(u)**k*mp.cos(x0*u)/(mp.pi*mp.factorial(k))
            numerical=mp.quad(integrand,[0,0.25,1,5,20,60,mp.inf])
            error=abs(analytic-numerical)
            assert error < mp.mpf('1e-35'), (k,x0,error)
            assert abs(float(analytic)-float(profile(k,x0))) < 2e-14
            profile_checks.append({'k':k,'x':x0,'absolute_error':str(error)})
    report['profile_integrals']=profile_checks

    # Check exact Lambert scale for several conductors and times.
    scales=[]
    for conductor in [1,5,23]:
        kap=mp.euler-1+mp.log(mp.mpf(conductor)/(2*mp.pi))
        for t0 in ['1e-4','1e-8','1e-16']:
            t=mp.mpf(t0)
            w=mp.lambertw(mp.mpf(conductor)*mp.e**(mp.euler-1)/(mp.pi*t))
            a=t*w/2
            err=abs(w-(mp.log(1/a)+kap))
            assert err < mp.mpf('1e-50')
            scales.append({'conductor':conductor,'time':t0,'w':str(w),'a':str(a),'identity_error':str(err)})
    report['scales']=scales

    # These errors concern only the analytic comparison integral in the proof.
    comparison=[]
    grid=np.linspace(-6,6,97)
    for w in [8,16,32,64]:
        actual=np.array([comparison_integral(w,float(z))[0] for z in grid])
        approximation=np.zeros_like(grid)
        for k in range(3):
            approximation += profile(k,grid)/w**k
            err=float(np.max(np.abs(actual-approximation)))
            comparison.append({'w':w,'order':k,'grid_max_error':err,
                               'error_times_w_to_order_plus_one':err*w**(k+1)})
    report['comparison_integral_errors']=comparison

    sample_results=[]
    ns=np.arange(1,10001)
    for p0 in [4,5,8]:
        cs=coefficients(ns,p0)
        assert np.min(cs)>0 and np.max(cs)<4
        # Direct ramp sum and interpolation agree on a small independent grid.
        errors=[]
        for x0 in [1.5,2.1,7.25,12.75,100.5]:
            nn=np.arange(1,math.floor(x0)+1)
            direct=np.sum(coefficients(nn,p0)*(1/nn-1/x0))-np.log(x0)
            errors.append(abs(direct-remainder(x0,p0)))
        assert max(errors)<1e-10
        sample_results.append({'p':p0,'tested_n':[1,10000],
                               'minimum_coefficient':float(np.min(cs)),
                               'maximum_coefficient':float(np.max(cs)),
                               'ramp_identity_max_error':float(max(errors))})
    report['bounded_positive_weights']=sample_results

    # Critical fractional-moment constants.
    moment_checks=[]
    for p0 in [mp.mpf('0.25'),mp.mpf('0.5'),mp.mpf('0.75')]:
        J=mp.pi/(2*mp.gamma(1+p0)*mp.sin(mp.pi*p0/2))
        ratio=mp.gamma(1-p0)/(p0*J)
        target=1/mp.cos(mp.pi*p0/2)
        assert abs(ratio-target)<mp.mpf('1e-50')
        moment_checks.append({'p':str(p0),'cauchy_moment':str(ratio)})
    report['fractional_moments']=moment_checks
    path=DATA/'verification_results.json'
    path.write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps({'status':'PASS','profile_integrals':len(profile_checks),
                      'lambert_identities':len(scales),'coefficient_checks':30000,
                      'output':str(path)},indent=2))

if __name__=='__main__':
    main()
