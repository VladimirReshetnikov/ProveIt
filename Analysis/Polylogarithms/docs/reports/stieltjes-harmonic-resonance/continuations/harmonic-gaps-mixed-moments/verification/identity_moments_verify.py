#!/usr/bin/env python3
"""Independent checks for mixed centered even-order Hurwitz-tail moments.

Formula implementation: Bernoulli polynomial summation by parts and Euler
odd-weight reduction. Numerical implementation: direct finite head plus an
independently generated centered Hurwitz asymptotic tail. Floating-point
errors are observations, not interval certificates.
"""
from __future__ import annotations
import json
from pathlib import Path
from functools import lru_cache
import sympy as s
import mpmath as mp

HERE=Path(__file__).resolve().parents[1]/'results'

@lru_cache(None)
def Z(k):
    return -s.Rational(1,2) if k==0 else s.Symbol(f'zeta_{k}')

@lru_cache(None)
def dz_even_odd(m,n):
    assert m>=2 and m%2==0 and n>=1 and n%2==1
    w=m+n
    if n==1:
        return s.Rational(m,2)*Z(w)-sum(Z(2*j)*Z(w-2*j) for j in range(1,m//2))
    return (Z(m)*Z(n)+s.Rational(s.binomial(w,m)-1,2)*Z(w)
            -sum((s.binomial(w-2*j-1,m-1)+s.binomial(w-2*j-1,n-1))*Z(2*j)*Z(w-2*j)
                 for j in range(1,(w-3)//2+1)))

def fc(p,h):
    if p<1 or p%2!=1 or h<1 or h>p+1:
        return s.S.Zero
    return s.binomial(p+1,h)*s.bernoulli(p+1-h,1)/(p+1)

@lru_cache(None)
def oriented(a,b,d):
    if d<a:
        return s.expand(dz_even_odd(b,a-d)+Z(a+b-d)/2)
    p=d-a
    return s.expand(sum(fc(p,2*j)*Z(b-2*j) for j in range(1,min(b//2,(p+1)//2)+1)))

@lru_cache(None)
def E(a,b,d):
    return s.expand(oriented(a,b,d)+oriented(b,a,d))

@lru_cache(None)
def moment(a,b,M):
    return s.expand(sum(s.binomial(2*M+1,2*l+1)*s.bernoulli(2*M-2*l,s.Rational(1,2))*E(a,b,2*l+1)/(2*M+1)
                        for l in range(M+1)))

def numeric(expr):
    return mp.mpf(str(s.N(expr.subs({x:s.zeta(int(str(x).split('_')[-1])) for x in expr.free_symbols}),mp.mp.dps)))

@lru_cache(None)
def center_coeff(a,k):
    if k==0: return s.Rational(1,a-1)
    return s.bernoulli(2*k,s.Rational(1,2))*s.rf(a,2*k-1)/s.factorial(2*k)

@lru_cache(None)
def product_coeff(a,b,k):
    return sum(center_coeff(a,j)*center_coeff(b,k-j) for j in range(k+1))

def mpq(x):
    return mp.mpf(str(s.numer(x)))/mp.mpf(str(s.denom(x)))

def finite_head(a,b,M,N):
    # T_a(n)=zeta(a,n+1), independently computed by mpmath's Hurwitz zeta.
    return mp.fsum((mp.mpf(n)+mp.mpf('0.5'))**(2*M)*mp.zeta(a,n+1)*mp.zeta(b,n+1) for n in range(N))

def tail_value(a,b,M,N,K):
    return finite_head(a,b,M,N)+mp.fsum(mpq(product_coeff(a,b,k))*mp.zeta(a+b-2+2*k-2*M,mp.mpf(N)+mp.mpf('0.5')) for k in range(K+1))

def cutoff_tau(a,j):
    if j==a-1: return s.Rational(1,a-1)
    if j==a: return -s.Rational(1,2)
    v=j-a+1
    if v>=2 and v%2==0:
        return s.bernoulli(v)*s.rf(a,v-1)/s.factorial(v)
    return s.S.Zero

def check_boundary(a,b,d):
    lhs=sum(cutoff_tau(a,j)*cutoff_tau(b,d-j) for j in range(d+1))
    for aa,bb in ((a,b),(b,a)):
        if d>aa:
            lhs+=sum(fc(d-aa,h)*cutoff_tau(bb,h) for h in range(1,d-aa+2))
    rhs=-(fc(d-a,b)+fc(d-b,a))/2
    return s.expand(lhs-rhs)==0

def check_sbp(a,b,M,N):
    za,zb=s.symbols('za zb')
    ha=s.S.Zero; hb=s.S.Zero; lhs=s.S.Zero
    for n in range(N):
        lhs+=(s.Rational(2*n+1,2))**(2*M)*(za-ha)*(zb-hb)
        ha+=s.Rational(1,(n+1)**a); hb+=s.Rational(1,(n+1)**b)
    rhs=s.S.Zero
    for l in range(M+1):
        d=2*l+1
        e=N**d*(za-ha)*(zb-hb)
        hak=s.S.Zero; hbk=s.S.Zero
        for k in range(1,N+1):
            e+=s.Integer(k)**(d-a)*(zb-hbk)+s.Integer(k)**(d-b)*(za-hak)-s.Integer(k)**(d-a-b)
            hak+=s.Rational(1,k**a); hbk+=s.Rational(1,k**b)
        rhs+=s.binomial(2*M+1,d)*s.bernoulli(2*M+1-d,s.Rational(1,2))*e/(2*M+1)
    return s.expand(lhs-rhs)==0

def main():
    mp.mp.dps=95
    boundary=[check_boundary(a,b,d) for a in (2,4,6,8,10) for b in (2,4,6,8,10) for d in range(1,32,2)]
    sbp=[check_sbp(a,b,M,N) for a,b in ((2,2),(2,4),(4,6),(6,6)) for M in range(5) for N in (1,3,7)]
    examples={f'{a},{b}':{str(M):str(moment(a,b,M)) for M in range(7)} for a,b in ((2,2),(2,4),(2,6),(4,4),(4,6))}
    tolerances={'error_N48_K32':mp.mpf('1e-45'),
                'error_N64_K36':mp.mpf('1e-55'),
                'tail_stability':mp.mpf('1e-45')}
    checks=[]
    for a,b in ((2,2),(2,4),(2,6),(4,4),(4,6),(6,8)):
        for M in (0,1,2,4,7):
            exact=numeric(moment(a,b,M))
            v1=tail_value(a,b,M,48,32)
            v2=tail_value(a,b,M,64,36)
            errors={'error_N48_K32':abs(v1-exact),
                    'error_N64_K36':abs(v2-exact),
                    'tail_stability':abs(v2-v1)}
            checks.append({'a':a,'b':b,'M':M,'formula':mp.nstr(exact,55),
                           **{key:mp.nstr(value,8) for key,value in errors.items()},
                           'passed':all(errors[key]<=tol for key,tol in tolerances.items())})
    output={'arithmetic':{'sympy':s.__version__,'mpmath':mp.__version__,'decimal_precision':mp.mp.dps},
            'symbolic_boundary':{'cases':len(boundary),'all_passed':all(boundary)},
            'symbolic_summation_by_parts':{'cases':len(sbp),'all_passed':all(sbp)},
            'numerical_method':'Finite direct Hurwitz head plus centered Hurwitz expansion tail, separately at (N,K)=(48,32),(64,36); not interval-certified.',
            'numerical_tolerances':{key:mp.nstr(tol,5) for key,tol in tolerances.items()},
            'numerical_case_count':len(checks),'numerical_cases':checks,'exact_examples':examples,
            'centered_product_2_4':{str(k):str(product_coeff(2,4,k)) for k in range(6)}}
    (HERE/'identity_moments_checks.json').write_text(json.dumps(output,indent=2)+'\n')
    assert all(boundary), 'At least one exact boundary identity failed'
    assert all(sbp), 'At least one exact finite summation-by-parts identity failed'
    assert all(q['passed'] for q in checks), 'A numerical moment diagnostic exceeded its declared tolerance'
    print(json.dumps({'symbolic_boundary':output['symbolic_boundary'],
                      'symbolic_summation_by_parts':output['symbolic_summation_by_parts'],
                      'numerical_cases':len(checks),
                      'max_error_N64_K36':max(float(q['error_N64_K36']) for q in checks),
                      'output':str(HERE/'identity_moments_checks.json')},indent=2))
    print('T2T4 moments:')
    for M in range(5): print(M,moment(2,4,M))

if __name__=='__main__': main()
