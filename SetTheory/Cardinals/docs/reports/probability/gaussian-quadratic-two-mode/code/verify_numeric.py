"""Deterministic numerical diagnostics. Not interval arithmetic or proof certificates."""
from __future__ import annotations
import json, math, platform, csv
from pathlib import Path
import numpy as np
import scipy
from scipy.integrate import quad
from scipy.special import gamma
from two_mode import (normalize, parameters, centered_moments, log_mgf,
                      envelope_log_mgf, rigidity, chernoff, zero_skew_absolute_moment)
ROOT=Path(__file__).resolve().parents[1]

def fractional_moment(z, p: float) -> tuple[float,float]:
    """Fourier absolute-moment integral for variance-two forms, 2<p<4.

    Returns a floating-point value and an error diagnostic: quadrature estimates
    plus the rigorous bound for the discarded characteristic-function tail.
    The diagnostic is not an interval certificate for floating-point evaluation.
    """
    if not 2 < p < 4: raise ValueError('2<p<4 is required')
    z=np.asarray(z,dtype=float)
    assert abs(float(z@z)-1)<1e-10
    moments=centered_moments(z,14)
    cutoff=.035/max(abs(z))
    lo=1e-7; upper=1024.
    def phi(t):
        return np.exp(np.sum(-1j*t*z-.5*np.log1p(-2j*t*z)))
    def kernel(t):
        if t < cutoff:
            return sum((-1)**k*moments[2*k]*t**(2*k)/math.factorial(2*k)
                       for k in range(2,8))
        return float(phi(t).real)-1+t*t
    c=-2*gamma(p+1)*math.sin(math.pi*p/2)/math.pi
    low=sum((-1)**k*moments[2*k]*lo**(2*k-p)/(math.factorial(2*k)*(2*k-p))
            for k in range(2,8))
    points=sorted(set([math.log(lo), min(0.,math.log(cutoff)),0.]))
    val=low; err=0.
    for left,right in zip(points,points[1:]):
        v,e=quad(lambda u:kernel(math.exp(u))*math.exp(-p*u),left,right,
                 epsabs=2e-10,epsrel=2e-10,limit=200)
        val+=v;err+=e
    val+=1/(p-2)-1/p
    for left,right in zip(np.linspace(0,math.log(upper),20)[:-1],
                          np.linspace(0,math.log(upper),20)[1:]):
        v,e=quad(lambda u:float(phi(math.exp(u)).real)*math.exp(-p*u),left,right,
                 epsabs=1e-11,epsrel=1e-10,limit=300)
        val+=v;err+=e
    err+=upper**(-p)/p
    return float(c*val),float(c*err)

def main():
    rng=np.random.default_rng(20261008)
    checks=0
    minima={name:float('inf') for name in ['spectral_gap','relative_even_moment_gap',
            'mgf_gap','rigidity_gap','moment_stability_gap','saddle_residual_margin']}
    random_spectra=4000
    for _ in range(random_spectra):
        n=int(rng.integers(2,65));raw=rng.normal(size=n)
        if rng.random()<.25: raw=abs(raw)
        z,_,delta=normalize(raw);a,b=parameters(delta)
        gap=min(a-float(max(z)), b+float(min(z)))
        assert gap>=-2e-11;checks+=1;minima['spectral_gap']=min(minima['spectral_gap'],gap)
        m=centered_moments(z,12);M=centered_moments([a,-b],12)
        defect=a**4+b**4-float(sum(z**4))
        for k in [4,6,8,10,12]:
            gap=(M[k]-m[k])/M[k]
            assert gap>=-2e-11;checks+=1
            minima['relative_even_moment_gap']=min(minima['relative_even_moment_gap'],gap)
            cp=48. if k==4 else 4*gamma(k)*(a+b)**(k-4)
            sgap=(M[k]-m[k]-cp*defect)/M[k]
            assert sgap>=-2e-11;checks+=1
            minima['moment_stability_gap']=min(minima['moment_stability_gap'],sgap)
        for fac in [-.9,-.5,-.1,.1,.5,.9]:
            t=fac/(2*(a if fac>0 else b))
            gap=envelope_log_mgf(delta,t)-log_mgf(z,t)
            assert gap>=-2e-10;checks+=1;minima['mgf_gap']=min(minima['mgf_gap'],gap)
        r=rigidity(z)
        gap=r['rigidity_constant']*r['fourth_trace_defect']-r['distance_squared']
        assert gap>=-2e-10;checks+=1;minima['rigidity_gap']=min(minima['rigidity_gap'],gap)
        x=float(rng.uniform(.01,30));bound,rate,t=chernoff(delta,x)
        deriv=-(a-b)+a/(1-2*a*t)-b/(1+2*b*t)
        residual=abs(deriv-x)/(1+x)
        assert residual<1e-10 and 0<=bound<=1, (delta,a,b,x,t,bound,rate,residual);checks+=1
        minima['saddle_residual_margin']=min(minima['saddle_residual_margin'],1e-10-residual)

    fcases=[[1], [1,-1], [3,4,5,-6], [1,1,1], [1,1,-1,-1], [1,2,-3],
            [1]*10, [1]*5+[-1]*5]
    fcases += [rng.normal(size=int(rng.integers(3,10))).tolist() for _ in range(12)]
    rows=[]
    for ci,raw in enumerate(fcases):
        z,_,delta=normalize(raw);a,b=parameters(delta)
        for p in [3.,3.25,3.5,3.75]:
            value,ev=fractional_moment(z,p);envelope,ee=fractional_moment([a,-b],p)
            gap=envelope-value
            assert gap>=-3e-7;checks+=1
            if abs(delta)<1e-13:
                assert abs(envelope-zero_skew_absolute_moment(p))<3e-7;checks+=1
            if len(raw)==1:
                ref=quad(lambda x:abs(x*x-1)**p*math.sqrt(2/math.pi)*math.exp(-x*x/2),
                         0,1,epsabs=1e-10)[0]+quad(
                         lambda x:abs(x*x-1)**p*math.sqrt(2/math.pi)*math.exp(-x*x/2),
                         1,np.inf,epsabs=1e-10)[0]
                assert abs(ref-value)<3e-7;checks+=1
            rows.append({'case':ci,'dimension':len(raw),'p':p,'delta':delta,
                         'moment':value,'envelope':envelope,'gap':gap,
                         'combined_error_diagnostic':ev+ee})
    with (ROOT/'results'/'fractional_moments.csv').open('w',newline='') as f:
        w=csv.DictWriter(f,fieldnames=list(rows[0]));w.writeheader();w.writerows(rows)
    result={'status':'PASS','seed':20261008,'random_spectra':random_spectra,
            'fractional_moment_comparisons':len(rows),'numerical_assertion_checks':checks,
            'minimum_diagnostics':minima,
            'max_fractional_error_diagnostic':max(r['combined_error_diagnostic'] for r in rows),
            'environment':{'python':platform.python_version(),'numpy':np.__version__,'scipy':scipy.__version__},
            'limitations':'Floating-point diagnostics, not formal or interval-certified proofs.'}
    (ROOT/'results'/'numeric_checks.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))
if __name__=='__main__':main()
