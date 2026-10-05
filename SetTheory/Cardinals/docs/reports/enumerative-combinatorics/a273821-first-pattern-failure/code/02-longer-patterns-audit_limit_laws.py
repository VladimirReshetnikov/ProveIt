#!/usr/bin/env python3
"""Independent algebraic and numerical audits of generalized limit laws.

Exact rational derivatives verify fixed-r mean and variance. Stable hyperbolic
arithmetic checks the r-to-infinity Laplace transform. A floating coefficient
sum independently checks the critical heavy-tail moment constants for r=3.
The numerical part is a check, not a substitute for a uniform coefficient proof.
"""
from fractions import Fraction
from math import asinh, cos, exp, expm1, pi, sin, sinh, sqrt
from pathlib import Path
import json
from verify_first_failure import D_coeffs, gf_rows


def peval(a,x):
    return sum(c*x**j for j,c in enumerate(a))


def derivative(a):
    return [(j+1)*a[j+1] for j in range(len(a)-1)]


def exact_moments(r):
    d=D_coeffs(r)
    x=Fraction(1,4)
    D=peval(d,x)
    Dx=peval(derivative(d),x)
    Dxx=peval(derivative(derivative(d)),x)
    assert D==Fraction(r+2,2**(r+1))
    assert Fraction(2**(r-2),4**r)*(r+1-Fraction(r,2))/(D*Fraction(1,4))==1
    assert -Dx/(4*D)==Fraction(r*(r+1),6)
    mean=r+2-Fraction(r,r+2)-Dx/(4*D)
    variance=mean-r-Fraction(r*r,(r+2)**2)+2-(Dxx/D-(Dx/D)**2)/16
    mean_expected=Fraction(r*(r+1),6)+r+2-Fraction(r,r+2)
    variance_expected=(Fraction(r*(r+1)*(r+3)*(r+4),90)+4
                       -Fraction(r,r+2)-Fraction(r*r,(r+2)**2))
    assert mean==mean_expected
    assert variance==variance_expected
    residual_mean=Fraction(r+4,r+2)
    residual_variance=4-Fraction(r,r+2)-Fraction(r*r,(r+2)**2)
    spectral_means=sum((cos(pi*j/(r+2))/sin(pi*j/(r+2)))**2
                       for j in range(1,(r+1)//2+1))
    spectral_variances=sum(cos(pi*j/(r+2))**2/sin(pi*j/(r+2))**4
                           for j in range(1,(r+1)//2+1))
    assert abs((r+float(residual_mean)+spectral_means)/float(mean)-1)<1e-12
    assert abs((float(residual_variance)+spectral_variances)/float(variance)-1)<1e-12
    N=r+2
    coupling_bound=(r+residual_mean)/N**2+Fraction(3*r+4,6*N**2)
    assert coupling_bound==Fraction(9*r*r+28*r+32,6*N**3)
    return dict(r=r,mean=str(mean),variance=str(variance),
                scaled_mean=float(mean/r**2),scaled_variance=float(variance/r**4),
                wasserstein_bound=str(coupling_bound))


def laplace(r,s):
    if s==0:
        return 1.0
    logy=-s/r**2
    y=exp(logy)
    t=asinh(sqrt(expm1(-logy)))
    return (0.5*exp((r-1)*logy/2)*(r+1-r*y/2)*sinh(t)
            /(sinh((r+2)*t)*(1-y/2)**2))


def r3_critical_moments(n,jcap=180):
    """Normalized exact convolution, with geometric j-tail cut at jcap.

    Coefficients of q=1/(1-3u+u^2) are computed after multiplication by rho^h.
    Since 2rho<1, the omitted contribution is negligible at this jcap.
    """
    rho=(3-sqrt(5))/2
    q=[1.0,3*rho]
    for h in range(2,n+1):
        q.append(3*rho*q[-1]-rho*rho*q[-2])
    diagonal=rho*q[n-1]-(rho*rho*q[n-2] if n>=2 else 0)
    z=diagonal
    sums=[0.0,0.0,0.0]
    first_w=rho**3/4 # rho^3 4^(-m) [x^(m-1)] C(x)^4, initially m=1
    for m in range(1,n-2):
        k=n-m
        w=first_w
        count=0.0
        for j in range(3,min(k,jcap)+1):
            count+=w*q[k-j]
            w*=rho*(j+2)*(2*m+j-1)/((j+1)*(m+j+1))
        z+=count
        for ell in range(1,4):
            sums[ell-1]+=m**ell*count
        first_w*=(2*m+3)*(2*m+2)/(4*m*(m+4))
    P=(5-sqrt(5))/2
    a=4/sqrt(pi)
    scaled=[sums[ell-1]/z/n**(ell-0.5) for ell in range(1,4)]
    targets=[2*a/(P*(2*ell-1)) for ell in range(1,4)]
    ratio=2*rho
    d=rho*sqrt(5)
    tail_bound=(rho**3/d*ratio**(jcap-2)
                *((jcap+2)/(1-ratio)+ratio/(1-ratio)**2)) if n>jcap+1 else 0.0
    return dict(n=n,partition=z,partition_target=P,
                scaled_moments=scaled,target_constants=targets,
                j_tail_partition_bound=tail_bound,
                relative_errors=[v/t-1 for v,t in zip(scaled,targets)])


def run(outdir=None):
    exact=[exact_moments(r) for r in range(2,61)]
    ls=[]
    for s in (0.1,1.,5.,10.):
        target=sqrt(s)/sinh(sqrt(s))
        ls.append(dict(s=s,target=target,
                       values={str(r):laplace(r,s) for r in (16,64,256,1024,4096)}))
    critical=[r3_critical_moments(n) for n in (100,1000,10000,100000)]
    exact_rows,_,_=gf_rows(100,3)
    rho=(3-sqrt(5))/2
    for n in (10,30,100):
        exact_z=sum(count*rho**k*4.0**(k-n) for k,count in enumerate(exact_rows[n]))
        computed=r3_critical_moments(n)['partition']
        assert abs(exact_z-computed)<1e-12,(n,exact_z,computed)
    result=dict(status='PASS',exact_rational_moment_checks=59,
                exact_moment_samples=exact[:9],laplace_checks=ls,
                critical_r3_checks=critical)
    path=(Path(outdir) if outdir else Path(__file__).resolve().parents[1]/'data')/'limit_law_audit.json'
    path.write_text(json.dumps(result,indent=2)+'\n')
    return result


if __name__=='__main__':
    print(json.dumps(run(),indent=2))
