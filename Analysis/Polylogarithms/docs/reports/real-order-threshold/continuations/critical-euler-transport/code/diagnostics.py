#!/usr/bin/env python3
"""Independent floating-point diagnostics, explicitly not certificates."""
from __future__ import annotations
from functools import lru_cache
from math import comb
from pathlib import Path
import json
import mpmath as mp
import numpy as np
import scipy
from scipy.special import roots_jacobi, roots_genlaguerre
from scipy.optimize import minimize_scalar

mp.mp.dps = 180
@lru_cache(None)
def weights(n: int):
    t=1<<n
    out=[]
    for j in range(n):
        t-=comb(n,j)
        out.append(t if j%2==0 else -t)
    return out

def euler_values(a, K=384, depths=(1,8,16,32,64,128,256)):
    a=mp.mpf(a); b=1-a
    fs=[mp.mpf(0)]; h=mp.mpf(0)
    for j in range(1,2*K-1):
        h+=mp.power(j,-b)
        if j%2==0:
            fs.append(h*mp.power(j+1,-a))
    def ev(n):
        return mp.fdot(weights(n),fs[:n])*mp.power(2,-n)
    g=ev(K)
    return g,{N:mp.power(2,N)*(ev(N)-g) for N in depths}

def gaussian_beta(a, b, rho=1., degree=100):
    """Gamma(w,1) x Beta(a,b), unrelated to finite Euler differences."""
    nodes,bw=roots_jacobi(degree,b-1,a-1)
    v=(nodes+1)/2; bw=bw/bw.sum()
    t,tw=roots_genlaguerre(degree,a+b-1); tw=tw/tw.sum()
    x=np.exp(-t[:,None]*v[None,:]); y=np.exp(-t[:,None])
    H=x*(x+y)/((1+rho*rho*x*x)*(1+rho*rho*y*y))
    return rho**3*float(tw @ H @ bw)

def hfun(t):
    if abs(t)<mp.mpf('1e-12'):
        return mp.mpf('.5')+t/12-t**3/720+t**5/30240
    return -1/mp.expm1(-t)-1/t

def density(a,T):
    a=mp.mpf(a);T=mp.mpf(T);b=1-a
    C=mp.quad(lambda v: v**(b-1)*(1-v)**(a-1)*hfun(T*v),
              [0,mp.mpf('.5'),1]) / mp.beta(b,a)
    return -mp.zeta(b)*T**(-b)/mp.gamma(a)+C

def surplus(a,T):
    """Regularized Bose integral; cancellation only inside its smooth difference."""
    a=mp.mpf(a);T=mp.mpf(T);b=1-a
    def fun(t):
        return mp.expm1(-b*mp.log1p(-t/T))*t**(b-1)/mp.expm1(t)
    first=mp.quad(fun,[0,T/2,T])
    tail=mp.quad(lambda t:t**(b-1)/mp.expm1(t),[T,mp.inf])
    return T**(-b)*(first-tail)/(mp.gamma(a)*mp.gamma(b))

def A(b):
    return b*b*mp.zeta(1+b)/mp.gamma(1-b)

def text(x):return mp.nstr(x,32)

def run():
    data={'status':'PASS','evidence':'floating-point diagnostics, not outward enclosures',
          'versions':{'mpmath':mp.__version__,'numpy':np.__version__,'scipy':scipy.__version__},
          'mpmath_decimal_precision':mp.mp.dps}
    gr=[]
    for a in (mp.mpf('.1'),mp.mpf('.25'),mp.mpf('.5'),mp.mpf('.75'),mp.mpf('.9')):
        g,rs=euler_values(a)
        q100=gaussian_beta(float(a),float(1-a),degree=100)
        q180=gaussian_beta(float(a),float(1-a),degree=180)
        discrepancy=abs(float(-g)-q180)
        assert discrepancy<2e-10
        gr.append({'a':str(a),'minus_g_Euler':text(-g),
                   'beta_gamma_degree100':q100,'beta_gamma_degree180':q180,
                   'observed_discrepancy':discrepancy,
                   'scaled_errors':{str(n):text(v) for n,v in rs.items()}})
    data['independent_gaussian_checks']=gr
    dr=[]
    # Quarter-order endpoint singularities converge well at this precision.
    with mp.workdps(85):
        for a in (mp.mpf('.25'),mp.mpf('.5'),mp.mpf('.75')):
            for T in (2,10,50):
                p=density(a,T); ex=surplus(a,T)
                err=abs((p-1)-ex)
                assert p>1 and err<mp.mpf('1e-18')
                b=1-a
                alpha2=mp.rf(b,2)**2*mp.zeta(b+2)/(2*mp.gamma(a))
                leading=A(b)*T**(-b-1)
                dr.append({'a':str(a),'T':T,'p_minus_one':text(p-1),
                           'Bose_identity_discrepancy':text(err),
                           'ratio_to_leading':text((p-1)/leading),
                           'ratio_to_two_terms':text((p-1)/(leading+alpha2*T**(-b-2)))})
    data['density_identity_and_asymptotics']=dr
    # Finite-depth maximizers: numerical local maximization after a grid scan.
    # This is evidence for an eventual-unimodality question, not its proof.
    cache={}
    def R(a,N):
        key=round(float(a),14)
        if key not in cache:
            _,rs=euler_values(mp.mpf(str(key)),K=384)
            cache[key]=rs
        return float(cache[key][N])
    opt=[]
    for N in (8,16,32,64,128,256):
        grid=np.linspace(.025,.975,20)
        vals=[R(a,N) for a in grid]
        j=int(np.argmax(vals))
        lo=0.0001 if j==0 else float(grid[j-1])
        hi=.9999 if j==len(grid)-1 else float(grid[j+1])
        fit=minimize_scalar(lambda a:-R(a,N),bounds=(lo,hi),method='bounded',options={'xatol':1e-8})
        opt.append({'N':N,'numerical_argmax_a':float(fit.x),
                    'numerical_max_R':float(-fit.fun),'grid_points':20,
                    'scope':'grid scan plus bounded local optimization; uniqueness not certified'})
    data['finite_depth_optimizers']=opt
    sp=[]
    for ell in (2,4,8,16,32):
        fit=minimize_scalar(lambda b:-float(A(mp.mpf(str(b)))*mp.exp(-ell*b)),
                            bounds=(1e-8,.999999),method='bounded',options={'xatol':1e-12})
        sp.append({'ell':ell,'surrogate_b':float(fit.x),'ell_times_b':ell*float(fit.x),
                   'e_ell_times_surrogate_max':float(mp.e*ell*(-fit.fun)),
                   'scope':'maximizer of A(b) exp(-ell*b), not a finite-N computation'})
    data['asymptotic_surrogate']=sp
    data['critical_constant']=text(mp.pi/4+mp.log(2)/2)
    return data

if __name__=='__main__':
    result=run()
    p=Path(__file__).resolve().parents[1]/'data'/'diagnostics.json'
    p.write_text(json.dumps(result,indent=2)+'\n')
    print('PASS: independent Gaussian, density, and optimization diagnostics')
    print('Finite-depth optimizer proposals:',result['finite_depth_optimizers'])
