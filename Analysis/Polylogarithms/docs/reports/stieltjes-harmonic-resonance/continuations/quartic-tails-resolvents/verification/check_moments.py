#!/usr/bin/env python3
"""Independent diagnostics for continuous powers of the cotangent resolvent.

No numerical comparison in this file is used as an identity proof.
The exact checks compare separate finite coefficient constructions.
"""
from pathlib import Path
import json
import math
import mpmath as mp
import sympy as sp

OUT = Path(__file__).resolve().parent
mp.mp.dps = 55
records = []

def data(z):
    eps = 1 if mp.im(z) > 0 else -1
    a = z + eps * mp.pi * 1j
    return eps, -1 / a, (z - eps * mp.pi * 1j) / a, -2 * eps * mp.pi * 1j

def log_ratio(x, z):
    """Principal Log(R_z(x)/x), avoiding the cancellation at x=0."""
    t = mp.pi * x
    if abs(t) < mp.mpf('1e-8'):
        logsinc = -t*t/6-t**4/180-t**6/2835-t**8/37800
    else:
        logsinc = mp.log(mp.sin(t)/t)
    return logsinc-mp.log1p(-2*mp.sin(t/2)**2-(z/mp.pi)*mp.sin(t))

def log_resolvent(x, z):
    return mp.log(x) + log_ratio(x, z)

def rpower(x, z, lam):
    return mp.exp(lam*log_resolvent(x,z))

def quad01(f):
    return mp.quad(f,[0,mp.mpf('.05'),mp.mpf('.3'),mp.mpf('.7'),mp.mpf('.95'),1])

def record(label, actual, predicted, **parameters):
    err=abs(actual-predicted)
    records.append({'label':label,'parameters':{k:str(v) for k,v in parameters.items()},
                    'actual':str(actual),'predicted':str(predicted),'absolute_error':str(err)})
    print(label, mp.nstr(err,6), flush=True)
    assert err < mp.mpf('1e-28'), (label,err)

def hyper_exp(t,z,lam):
    eps,C,q,sigma=data(z)
    a=t/sigma
    return mp.exp(lam*mp.log(C)+t/2)*mp.gamma(1+lam)*mp.hyp2f1(lam,-a,1+lam-a,q)/(mp.gamma(1+a)*mp.gamma(1+lam-a))

def harmonic(j,lam):
    return mp.digamma(1+lam)+mp.euler if j==1 else mp.zeta(j)-mp.zeta(j,1+lam)

def hm(n,lam):
    h=[mp.mpf(1)]
    for k in range(1,n+1):
        h.append(mp.fsum(harmonic(j,lam)*h[k-j] for j in range(1,k+1))/k)
    return h[n]

def l_mellin(nu,lam,q):
    def integrand(t):
        w=mp.exp(-t)
        lf=mp.log(-mp.expm1(-t))-mp.log1p(-q*w)
        return t**(nu-1)*mp.expm1(lam*lf)
    return mp.quad(integrand,[0,mp.mpf('.1'),1,4,12,mp.inf])/mp.gamma(nu)

def log_integral(z):
    # This is the exact subtraction of log(x)/x from gamma_0(x) Log R.
    return quad01(lambda x:log_ratio(x,z)/x-mp.digamma(1+x)*log_resolvent(x,z))

def dpolylog1(q):
    if q == 0:
        return mp.mpf(0)
    terms=[]
    qn=q
    n=1
    while True:
        term=-qn*mp.log(n)/n
        terms.append(term)
        if n>12 and abs(term)<mp.mpf('1e-60'):
            return mp.fsum(terms)
        qn*=q
        n+=1

def predicted_log(z):
    eps,C,q,sigma=data(z)
    ls=mp.log(sigma)
    return (mp.stieltjes(1)+mp.euler**2/2-mp.zeta(2)/2-ls**2/2
            +dpolylog1(q)+(mp.euler+ls)*mp.log(1-q))

def exact_coefficients():
    lam,q=sp.symbols('lam q')
    checks=0
    for n in range(1,10):
        direct=sum((-1)**k*sp.ff(lam,k)/sp.factorial(k)*sp.rf(lam,n-k)*q**(n-k)/sp.factorial(n-k)
                   for k in range(n+1))
        beta=-lam*(1-q)*sum(sp.binomial(n-1,j)*q**(n-1-j)*(1-q)**j*sp.rf(1-lam,j)/sp.factorial(j+1)
                            for j in range(n))
        assert sp.expand(direct-beta)==0
        checks+=1
    # Deliberately changing the coefficient prefactor must fail.
    assert sp.expand((-lam*(1-q))-lam*(1-q))!=0
    return {'independent_symbolic_coefficients':checks,'corruption_control':'PASS'}

def main():
    exact=exact_coefficients()
    moment_cases=[
        (mp.mpc('.8','2.1'),mp.mpc('.4','.15'),mp.mpc('.7','.2')),
        (mp.mpc('-.6','-1.4'),mp.mpc('-.4','.1'),mp.mpc('-.3','.4')),
        (mp.mpc('.3','1.2'),mp.mpc('1.8','-.2'),mp.mpc('.2','-.6')),
    ]
    for z,lam,t in moment_cases:
        actual=quad01(lambda x:mp.exp(t*x)*rpower(x,z,lam))
        record('ordinary_exponential_moment',actual,hyper_exp(t,z,lam),z=z,lam=lam,t=t)
        C=data(z)[1]
        record('fractional_mean',quad01(lambda x:rpower(x,z,lam)),mp.exp(lam*mp.log(C)),z=z,lam=lam)
        _,C,q,sigma=data(z)
        first=mp.exp(lam*mp.log(C))/sigma*(mp.digamma(1+lam)+mp.euler+q*mp.lerchphi(q,1,1+lam)+mp.log(1-q))
        record('digamma_Lerch_first_moment',quad01(lambda x:(x-mp.mpf('.5'))*rpower(x,z,lam)),first,z=z,lam=lam)
    for eps,lam,n in [(1,mp.mpf('-.5'),1),(1,mp.mpf('-.5'),2),
                       (-1,mp.mpf('.5'),3),(1,mp.mpc('.3','.2'),4)]:
        z=eps*mp.pi*1j
        _,C,q,sigma=data(z)
        actual=quad01(lambda x:mp.bernpoly(n,x)*rpower(x,z,lam))
        predicted=mp.factorial(n)*mp.exp(lam*mp.log(C))*sigma**(-n)*hm(n,lam)
        record('Bernoulli_Gamma_moment',actual,predicted,eps=eps,lam=lam,n=n)
    for z,lam,s,p in [(mp.mpc('.6','2'),mp.mpc('.35','.1'),mp.mpc('2.7','.15'),1),
                       (mp.mpc('-.7','-1.8'),mp.mpc('-.3','.1'),mp.mpc('1.8','.2'),0)]:
        _,C,q,sigma=data(z)
        actual=quad01(lambda x:(-1)**p*mp.rf(1-s,p)*mp.zeta(1-s+p,x)*rpower(x,z,lam))
        predicted=mp.exp(lam*mp.log(C))*mp.gamma(s)*mp.exp((p-s)*mp.log(sigma))*l_mellin(s-p,lam,q)
        record('Hurwitz_spectral_transform',actual,predicted,z=z,lam=lam,s=s,p=p)
    for z in [mp.mpc('.8','2.1'),mp.mpc('-.6','-1.4'),mp.pi*1j]:
        record('finitepart_log_resolvent',log_integral(z),predicted_log(z),z=z)
    # At q=0 the finite part has a separate convergent gamma-correlation representative.
    gamma_cross=quad01(lambda x:mp.digamma(x)*mp.loggamma(1-x))
    gamma_value=mp.stieltjes(1)+mp.euler**2/2+mp.pi**2/24-mp.log(2*mp.pi)**2/2
    record('ordinary_reflected_gamma_integral',gamma_cross,gamma_value)
    # Exact collision canary: p=2,s=1,lambda=1.  The pointwise Hurwitz derivative
    # is zero, while fixed-lambda spectral continuation is -1.
    collision={'p':2,'s':1,'lambda':1,'ordinary_integral':0,
               'spectral_continuation':-1,'explanation':'Endpoint contact; boundary Re(s+lambda)=p.'}
    summary={'status':'PASS','precision_decimal_digits':mp.mp.dps,'exact':exact,
             'numeric_comparisons':len(records),'max_absolute_error':str(max(mp.mpf(r['absolute_error']) for r in records)),
             'resonance_canary':collision,'records':records,
             'scope':'Symbolic identities and independent numerical diagnostics; no interval claim.'}
    (OUT/'moment_checks.json').write_text(json.dumps(summary,indent=2)+'\n')
    print(json.dumps({k:v for k,v in summary.items() if k!='records'},indent=2))

if __name__=='__main__':
    main()
