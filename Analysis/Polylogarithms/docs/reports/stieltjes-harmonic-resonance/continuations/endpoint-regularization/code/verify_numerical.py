#!/usr/bin/env python3
"""Independent high-precision numerical comparisons (not interval proofs)."""
from __future__ import annotations
from pathlib import Path
from functools import lru_cache
from itertools import product
from math import factorial
import json, platform
import mpmath as mp

ROOT=Path(__file__).resolve().parents[1]
mp.mp.dps=60
records=[]

def record(group, params, lhs, rhs, tolerance='1e-40'):
    err=abs(lhs-rhs)
    if err>mp.mpf(tolerance):
        raise AssertionError(f'{group}: {params}: error {mp.nstr(err,12)}')
    records.append({'group':group,'parameters':params,
                    'absolute_error':mp.nstr(err,12),
                    'lhs':mp.nstr(lhs,45),'rhs':mp.nstr(rhs,45),
                    'tolerance':tolerance})

# Exact special-function evaluation of finite harmonic power sums, compared
# with a direct finite product. Coefficients are evaluated numerically here.
for astr in ['0.5','1.3','2.0']:
    a=mp.mpf(astr)
    for N in [5,20]:
        bound=(1,1,1)
        inds=sorted(product(range(2),repeat=3),key=lambda x:(sum(x),x))
        zero=(0,0,0)
        direct={alpha:mp.mpf(0) for alpha in inds};direct[zero]=mp.mpf(1)
        for n in range(N):
            x=n+a; row=[mp.log(x)**r/x for r in range(3)]
            new=direct.copy()
            for alpha in inds:
                for r in range(3):
                    if alpha[r]==0:
                        beta=list(alpha);beta[r]=1;beta=tuple(beta)
                        new[beta]+=direct[alpha]*row[r]
            direct=new
        logcoef={}
        for alpha in inds[1:]:
            k=sum(alpha);w=sum(r*m for r,m in enumerate(alpha))
            if k==1:
                power=mp.stieltjes(w,a)-mp.stieltjes(w,a+N)
            else:
                power=(-1)**w*mp.diff(lambda s:mp.zeta(s,a)-mp.zeta(s,a+N),k,w)
            logcoef[alpha]=(-1)**(k-1)*factorial(k-1)*power
        exp={zero:mp.mpf(1)}
        for alpha in inds[1:]:
            exp[alpha]=sum(sum(beta)*val*exp[tuple(x-y for x,y in zip(alpha,beta))]
                           for beta,val in logcoef.items()
                           if all(x>=y for x,y in zip(alpha,beta)))/sum(alpha)
        for alpha in inds:
            record('finite_harmonic_stieltjes_zeta',{'a':astr,'N':N,'content':alpha},
                   direct[alpha],exp[alpha], '1e-47')

# Full unweighted generating function: a direct geometric-convergent series,
# a hypergeometric expression, and an incomplete-beta expression.
for astr in ['0.5','1','1.7','3']:
    a=mp.mpf(astr)
    for ustr in ['0.17','-0.11']:
        u=mp.mpf(ustr)
        for zstr in ['0.23','0.71','0.93']:
            zz=mp.mpf(zstr)
            term=u*zz**a/a
            terms=[term]
            for n in range(1,10000):
                term*=zz*(a+u+n-1)/(a+n)
                terms.append(term)
                if abs(term)<mp.mpf('1e-59'):break
            else:raise RuntimeError('Series did not converge within 10000 terms.')
            direct=1+mp.fsum(terms)
            hyp=1+u*zz**a/a*mp.hyp2f1(1,a+u,a+1,zz)
            beta=1+u*(1-zz)**(-u)*mp.betainc(a,u,0,zz)
            params={'a':astr,'u':ustr,'z':zstr,'terms':len(terms)}
            record('full_generator_series_hypergeometric',params,direct,hyp,'1e-55')
            record('full_generator_beta_hypergeometric',params,beta,hyp,'1e-55')

# Convergent primitive generating identities, checked by numerical integrals.
for M in [1,2,3,5]:
    for ustr,vstr in [('0.17','0.13'),('-0.21','-0.16')]:
        u=mp.mpf(ustr);v=mp.mpf(vstr)
        P=mp.fprod(1+u/j for j in range(1,M))
        def remainder(t):
            if M==1:
                return mp.expm1(-u*mp.log1p(-t))
            return (1-t)**(-u)-mp.fsum(mp.rf(u,n)/mp.factorial(n)*t**n for n in range(M))
        integ=v*mp.quad(lambda t:t**(-v-1)*remainder(t),[0,mp.mpf('.5'),mp.mpf('.9'),1])/P
        rhs=(1-mp.gamma(1-u)*mp.gamma(1-v)/mp.gamma(1-u-v)
             -sum(mp.rf(u,n)/mp.factorial(n)*v/(n-v) for n in range(1,M)))/P
        record('primitive_double_generator',{'M':M,'u':ustr,'v':vstr},integ,rhs,'1e-42')
        integ1=mp.quad(lambda t:remainder(t)/t,[0,mp.mpf('.5'),mp.mpf('.9'),1])/P
        rhs1=(-mp.digamma(1-u)-mp.euler
              -sum(mp.rf(u,n)/(mp.factorial(n)*n) for n in range(1,M)))/P
        record('primitive_first_generator',{'M':M,'u':ustr},integ1,rhs1,'1e-42')

# Parameter derivatives of generalized Stieltjes constants.
for astr in ['0.5','1.2']:
    a=mp.mpf(astr)
    for r in range(3):
        lhs=mp.diff(lambda x:mp.stieltjes(r,x),a)
        rhs=(-1)**(r+1)*(mp.diff(lambda s:mp.zeta(s,a),2,r)
              +(r*mp.diff(lambda s:mp.zeta(s,a),2,r-1) if r else 0))
        record('stieltjes_parameter_derivative',{'a':astr,'r':r},lhs,rhs,'1e-45')

# Cauchy average of a Laurent function: independently extracts the diagonal CT.
for astr in ['1','0.5']:
    a=mp.mpf(astr);rad=mp.mpf('.025');K=48
    g0=-mp.digamma(a);g1=mp.stieltjes(1,a);g2=mp.stieltjes(2,a)
    for d in [2,3]:
        vals=[]
        for j in range(K):
            t=rad*mp.exp(2j*mp.pi*j/K)
            z1=mp.zeta(1+t,a);z2=mp.zeta(2+2*t,a)
            val=(z1*z1-z2)/2 if d==2 else (z1**3-3*z1*z2+2*mp.zeta(3+3*t,a))/6
            vals.append(val)
        lhs=mp.fsum(vals)/K
        rhs=((g0*g0-mp.zeta(2,a))/2-g1 if d==2 else
             (g0**3-3*g0*mp.zeta(2,a)+2*mp.zeta(3,a))/6-g0*g1+g2/4
             -mp.diff(lambda s:mp.zeta(s,a),2))
        record('diagonal_laurent_cauchy_average',{'a':astr,'depth':d,'points':K},lhs,rhs,'1e-43')

# Full convergent antiderivatives: generalized hypergeometric expression.
for astr in ['0.5','1.3']:
    a=mp.mpf(astr);u=mp.mpf('.17');zz=mp.mpf('.71')
    for p in [1,2,3]:
        term=u*zz**a/a
        terms=[term/a**p]
        for n in range(1,1500):
            term*=zz*(a+u+n-1)/(a+n)
            terms.append(term/(a+n)**p)
            if abs(terms[-1])<mp.mpf('1e-59'):break
        lhs=mp.fsum(terms)
        rhs=u*zz**a/a**(p+1)*mp.hyper([1,a+u]+[a]*p,[a+1]*(p+1),zz)
        record('full_antiderivative_hypergeometric',{'a':astr,'p':p,'u':'.17','z':'.71'},lhs,rhs,'1e-55')

# Beta-weighted ordinary moments, including log moments in the endpoint variable.
for astr in ['0.5','1.3','2']:
    a=mp.mpf(astr);u=mp.mpf('.17');b=mp.mpf('1.2')
    for k in [0,1,2]:
        lhs=mp.quad(lambda t:(1-t)**(b-1)*mp.log(1-t)**k*
                    (u*t**a/a*mp.hyp2f1(1,a+u,a+1,t)),
                    [0,mp.mpf('.5'),mp.mpf('.9'),1])
        rhs=mp.diff(lambda x:u*mp.beta(a,x)/(x-u),b,k)
        record('beta_weighted_moment_generator',{'a':astr,'b':'1.2','u':'.17','log_power':k},lhs,rhs,'1e-42')

# Integer-shift elementary reduction, compared to direct harmonic coefficients.
for M0 in [1,2,4]:
    zz=mp.mpf('.71');LL=-mp.log(1-zz)
    for d in [1,2,3,4]:
        prefix=[mp.mpf(1)]+[mp.mpf(0)]*(d-1)
        direct=mp.mpf(0)
        for n in range(M0,600):
            direct+=zz**n*prefix[d-1]/n
            for j in range(d-1,0,-1):prefix[j]+=prefix[j-1]/n
        elementary=LL**d/mp.factorial(d)
        elementary+=sum((-1)**j*mp.binomial(M0-1,j)/mp.mpf(-j)**d*
                        ((1-zz)**j-sum((-j*LL)**k/mp.factorial(k) for k in range(d)))
                        for j in range(1,M0))
        record('integer_shift_elementary_function',{'M':M0,'depth':d,'z':'.71'},direct,elementary,'1e-48')

# Half-shift reflection moments checked through their depth-generating sums.
a=mp.mpf('.5');b=mp.mpf('.5');u=mp.mpf('.17');x=2*u;ll=mp.log(2)
A=mp.gamma(a)*mp.gamma(1+u)/mp.gamma(a+u)
explicit=[mp.pi*x/(1-x),
          -2*mp.pi*(x/(1-x)**2+ll*x/(1-x)),
          mp.pi*(4*x*(1+x)/(1-x)**3+(8*ll+4)*x/(1-x)**2
                 +(4*ll**2+mp.pi**2/3)*x/(1-x))]
for k in range(3):
    lhs=mp.quad(lambda t:(-t)**k*mp.exp(-(b-u)*t)*
                (A-u*mp.betainc(u,a,0,mp.exp(-t))),[0,1,4,mp.inf])
    record('half_shift_reflection_log_moments',{'u':'.17','log_power':k},lhs,explicit[k],'1e-43')

# Ordinary zero-based primitives, distinct from logarithmic dz/z primitives.
for astr in ['0.5','1.3']:
    a=mp.mpf(astr);u=mp.mpf('.17');zz=mp.mpf('.71')
    for q in [1,2,3]:
        term=u*zz**a/a;terms=[term*zz**q/mp.rf(a+1,q)]
        for n in range(1,1500):
            term*=zz*(a+u+n-1)/(a+n)
            terms.append(term*zz**q/mp.rf(a+n+1,q))
            if abs(terms[-1])<mp.mpf('1e-59'):break
        lhs=mp.fsum(terms)
        rhs=u*mp.gamma(a)*zz**(a+q)/mp.gamma(a+q+1)*mp.hyp2f1(1,a+u,a+q+1,zz)
        record('ordinary_antiderivative_hypergeometric',{'a':astr,'q':q,'z':'.71'},lhs,rhs,'1e-55')

counts={}
for r in records:counts[r['group']]=counts.get(r['group'],0)+1
out={'status':'PASS','comparisons':len(records),'decimal_precision':mp.mp.dps,
     'largest_absolute_error':mp.nstr(max(mp.mpf(r['absolute_error']) for r in records),12),
     'groups':counts,'python':platform.python_version(),'mpmath':mp.__version__,
     'meaning':'Uncertified floating-point comparisons, not proofs or interval enclosures.',
     'records':records}
(ROOT/'results/numerical_checks.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({k:v for k,v in out.items() if k!='records'},indent=2))
