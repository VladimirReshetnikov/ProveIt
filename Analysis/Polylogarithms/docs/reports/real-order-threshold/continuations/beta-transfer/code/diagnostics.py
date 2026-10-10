#!/usr/bin/env python3
"""Independent numerical diagnostics, explicitly NOT interval certificates."""
from __future__ import annotations
from pathlib import Path
from math import comb
import json
import mpmath as mp

mp.mp.dps=45

def bose(x):return 1/mp.expm1(x)

def excess_profile(v,T):
    if v<=0:return bose(T)
    if v>=1:return mp.mpf(0)
    x=(1-v)*T
    if x/v < mp.mpf('.1'):
        result=(1-v)/(2*v)
        for k in range(1,15):
            result += mp.bernoulli(2*k)*x**(2*k-1)*(-mp.expm1(-2*k*mp.log(v)))/mp.factorial(2*k)
        return result
    return bose(x)-bose(x/v)/v

def density(a,T):
    a,T=mp.mpf(a),mp.mpf(T);b=1-a
    def f(t):
        if t<=0:return bose(T)
        if t>=1:return mp.mpf(0)
        v=t**(1/a)
        return (1-v)**(b-1)*excess_profile(v,T)
    return 1+mp.quad(f,[0,mp.mpf('.25'),mp.mpf('.5'),mp.mpf('.9'),1])/(a*mp.beta(a,b))

def independent_density(a,T):
    a,T=mp.mpf(a),mp.mpf(T);b=1-a
    def h(t):
        if t<mp.mpf('.1'):
            return mp.mpf('.5')+sum(mp.bernoulli(2*k)*t**(2*k-1)/mp.factorial(2*k) for k in range(1,15))
        return 1+bose(t)-1/t
    hT=h(T)
    def f(t):
        if t==1:return mp.mpf(0)
        u=t**(1/b)
        return (1-u)**(a-1)*(h(T*u)-hT)
    C=hT+mp.quad(f,[0,mp.mpf('.5'),mp.mpf('.9'),1])/(b*mp.beta(a,b))
    return -mp.zeta(b)*T**(-b)/mp.gamma(a)+C

def mp_coeff(a,b,M):
    H=mp.mpf(0);out=[]
    for n in range(M):
        if n:H+=(2*n-1)**(-b)+(2*n)**(-b)
        out.append(H/(2*n+1)**a)
    return out

def mp_euler(f,N):
    tail=2**N-1;terms=[]
    for n in range(N):
        terms.append((-1)**n*tail*f[n]);tail-=comb(N,n+1)
    return mp.fsum(terms)/2**N

def polylog_profile(p,q,w):
    ii=1j
    alphaP=[mp.exp(2j*mp.pi*(mp.mpf('.25')+j)/p) for j in range(p)]
    alphaQ=[mp.exp(2j*mp.pi*(mp.mpf('.25')+j)/q) for j in range(q)]
    # Numerical merging is used only in this diagnostic. The algebraic
    # certificate has a separate exact exponent-based construction.
    roots=[]
    for alpha in alphaP+alphaQ:
        if not any(abs(alpha-v)<mp.mpf('1e-35') for v in roots):roots.append(alpha)
    total=0j
    for alpha in roots:
        P=abs(alpha**p-ii)<mp.mpf('1e-35')
        Q=abs(alpha**q-ii)<mp.mpf('1e-35')
        if P and Q:
            A=-mp.mpf(p+q)/(2*p*q);B=mp.mpf(1)/(p*q)
        elif P:A=ii/(p*(alpha**q-ii));B=0
        else:A=ii/(q*(alpha**p-ii));B=0
        total+=A*mp.polylog(w,alpha)+B*mp.polylog(w-1,alpha)
    return q**w*total

def integral_profile(p,q,w):
    v=mp.mpf(p)/q
    def f(T):
        x,y=mp.exp(-v*T),mp.exp(-T)
        return T**(w-1)*(-x*y)/((1-1j*x)*(1-1j*y))
    return mp.quad(f,[0,1,5,20,mp.inf])/mp.gamma(w)

rows=[]
for a in ['.1','.5','.9']:
    for T in [1,5,20,100]:
        nu=density(a,T);old=independent_density(a,T)
        b=1-mp.mpf(a);c=b*b*mp.zeta(1+b)/mp.gamma(1-b)
        leading=c*mp.mpf(T)**(-b-1)
        remainder=abs(nu-1-leading)
        assert 1<nu<1+mp.mpf(1)/T
        assert abs(nu-old)<mp.mpf('1e-35')
        if T>=2:assert remainder<=16*c*mp.mpf(T)**(-b-2)+4*mp.exp(-mp.mpf(T)/2)
        rows.append({'a':a,'T':T,'density':mp.nstr(nu,35),
                     'independent_discrepancy':mp.nstr(nu-old,8),
                     'ratio_to_leading_excess':mp.nstr((nu-1)/leading,25)})
print('PASS 12 density comparisons and corresponding bounds')
profiles=[]
for p,q,w in [(1,2,mp.mpf(1)),(1,3,mp.mpf('1.5')),(1,5,mp.mpf('.5')),(3,7,mp.mpf(2))]:
    lhs=integral_profile(p,q,w);rhs=polylog_profile(p,q,w)
    assert abs(lhs-rhs)<mp.mpf('1e-23')
    profiles.append({'p':p,'q':q,'w':str(w),'integral':str(lhs),
                     'polylogarithms':str(rhs),'discrepancy':mp.nstr(lhs-rhs,8)})
print('PASS 4 independent cyclotomic integral/polylogarithm comparisons')
elementary=3*mp.pi/8-mp.log(2)/4-mp.log(1+mp.sqrt(2))/mp.sqrt(2)
assert abs(-mp.im(integral_profile(1,2,1))-elementary)<mp.mpf('1e-40')

with mp.workdps(160):
    grid=[]
    for atext in ['.1','.25','.5','.75','.9']:
        a=mp.mpf(atext);b=1-a;f=mp_coeff(a,b,360);g=mp_euler(f,360)
        scaled={str(N):mp.nstr(2**N*(mp_euler(f,N)-g),30) for N in [1,2,4,8,16,32,64,128]}
        grid.append({'a':atext,'g':mp.nstr(g,60),'scaled_errors':scaled})
    f=mp_coeff(mp.mpf(1),mp.mpf(1),360)
    special_discrepancy=mp_euler(f,360)+mp.pi*mp.log(2)/8
    assert abs(special_discrepancy)<mp.mpf('1e-105')
print('PASS critical-error grid and classical F_1,1 identity')
result={'status':'PASS','scope':'Numerical diagnostics only, not certified intervals.',
        'working_decimal_digits':45,'euler_grid_decimal_digits':160,
        'density_comparisons':rows,'profile_comparisons':profiles,
        'elementary_half_profile':mp.nstr(elementary,40),'critical_error_grid':grid,
        'classical_F11_discrepancy':mp.nstr(special_discrepancy,8)}
output=Path(__file__).resolve().parents[1]/'data'/'diagnostics.json'
output.write_text(json.dumps(result,indent=2)+'\n')
