#!/usr/bin/env python3
"""Numerical stress tests, separate from the exact certificates in verify.py."""
from __future__ import annotations
import json,time
from pathlib import Path
from fractions import Fraction as Q
from math import comb
from functools import lru_cache
import mpmath as mp
import sympy as s
from gaussian import gaussian_euler,euler_sum,kernel_polynomial
ROOT=Path(__file__).resolve().parents[1]

def m(q:Q):return mp.mpf(q.numerator)/q.denominator

def write(name,value):(ROOT/'data'/name).write_text(json.dumps(value,indent=2)+'\n')

@lru_cache(None)
def gamma_derivative(j:int):return mp.diff(mp.gamma,mp.mpf('0.5'),j)

def error_polynomial(a:int,b:int,L):
    T,P=kernel_polynomial(a,b);poly=s.Poly(P,T);out=mp.mpf(0)
    for (degree,),coefficient in poly.terms():
        c=mp.mpf(str(s.N(coefficient,110)))
        out-=c*sum(mp.mpf(comb(degree,j))*L**(degree-j)*(-1)**j*gamma_derivative(j)/2**(j+1)
                   for j in range(degree+1))
    return out

def zero_delta(a:int,b:int,M:int=300):
    H=mp.mpf(0);terms=[]
    for n in range(2,M+1):
        H+=mp.mpf(n-1)**(-b)
        terms.append((n,H*(mp.mpf(2)/n)**a))
    def value(d):
        out=mp.mpf(0)
        for n,c in terms:
            r=n%4
            trig=(-mp.sin(n*d) if r==0 else mp.cos(n*d) if r==1 else
                  mp.sin(n*d) if r==2 else -mp.cos(n*d))
            out+=c*trig
        return out
    lead=(1+mp.mpf(2)**(-b))/2*(mp.mpf(2)/3)**a
    root=mp.findroot(value,(lead*mp.mpf('.8'),lead*mp.mpf('1.2')),tol=mp.mpf('1e-105'))
    return root,value(root)

def main():
    if not __debug__:
        raise RuntimeError("Run verification without Python -O; assertions must remain enabled.")
    start=time.time();mp.mp.dps=120
    errors=[]
    for a,b in [(1,1),(3,1),(2,3),(5,1)]:
        for N in [64,128,256,512]:
            observed=m(gaussian_euler(a,b,N)-gaussian_euler(a,b,2*N))
            leading=mp.sqrt(mp.pi)/(2**(a+b)*mp.factorial(a+b-1))*mp.power(2,-N)/mp.sqrt(N)*mp.log(N)**(a+b-1)
            refined=mp.power(2,-N)/mp.sqrt(N)*error_polynomial(a,b,mp.log(N)/2)
            ratio=observed/refined
            assert observed>0 and abs(ratio-1)<mp.mpf('.25'),(a,b,N,ratio)
            errors.append({'a':a,'b':b,'N':N,'error_proxy_E_N_minus_E_2N':mp.nstr(observed,35),
                           'proxy_absolute_error_bound':mp.nstr((1 if b==1 else mp.mpf(b)/(b-1))*mp.power(2,-2*N),8),
                           'ratio_to_leading_term':mp.nstr(observed/leading,20),
                           'ratio_to_full_polynomial':mp.nstr(ratio,20)})
    write('euler_error_asymptotics.json',errors)
    zeros=[]
    for a in [20,40,80]:
        for b in [1,2,8]:
            d,residual=zero_delta(a,b)
            H=lambda n:sum(mp.mpf(k)**(-b) for k in range(1,n+1))
            A=H(2);B=H(3);C=H(4)
            predicted=A/2*(mp.mpf(2)/3)**a-C/2*(mp.mpf(2)/5)**a+A*B*mp.power(3,-a)-mp.mpf(23)/48*A**3*(mp.mpf(8)/27)**a
            remainder=(d-predicted)/(mp.mpf(2)/7)**a
            # The theorem states O((2/7)^a); the next Fourier mode predicts H_6/2.
            assert abs(remainder-H(6)/2)<mp.mpf('.1'),(a,b,remainder)
            zeros.append({'a':a,'b':b,'delta':mp.nstr(d,75),'theta':mp.nstr(mp.pi/2-d,75),
                          'four_term_delta':mp.nstr(predicted,75),
                          'normalized_remainder':mp.nstr(remainder,30),
                          'predicted_next_coefficient_H6_over_2':mp.nstr(H(6)/2,30),
                          'normalized_equation_residual':mp.nstr(residual,10)})
    write('zero_asymptotics.json',zeros)
    # A finite Fourier table, intentionally labelled numerical, not certified intervals.
    table=[]
    for a in [8,12,20]:
        for b in [1,2,4]:
            d,_=zero_delta(a,b)
            table.append({'a':a,'b':b,'theta_approx':mp.nstr(mp.pi/2-d,13),'delta_approx':mp.nstr(d,13),
                          'method':'300-term Fourier sum; numerical illustration of the proved unique zero'})
    write('zero_table.json',table)
    # Existing S4 identity: do NOT promote numerical agreement to a theorem.
    def S4(N):
        H=Q(0);terms=[]
        for n in range(N):
            if n:H+=Q(1,n)
            terms.append(H/(2*n+1)**4)
        return euler_sum(terms)
    g41=m(gaussian_euler(4,1,500));g32=m(gaussian_euler(3,2,500))
    beta4=(mp.zeta(4,mp.mpf(1)/4)-mp.zeta(4,mp.mpf(3)/4))/4**4
    rhs=mp.mpf(58)/7*g41+mp.mpf(24)/7*g32+mp.mpf(19)/3584*mp.pi**5-2*beta4*mp.log(2)
    v400=m(S4(400));v500=m(S4(500))
    assert abs(v500-rhs)<mp.mpf('1e-110')
    write('s4_conjecture_numerics.json',{
        'status':'Still a conjecture in this package; numerical support is not a proof.',
        'equivalent_rhs':'58*g41/7 + 24*g32/7 + 19*pi^5/3584 - 2*beta(4)*log(2)',
        'S4_500_terms':mp.nstr(v500,112),'rhs':mp.nstr(rhs,112),
        'difference_400_500_terms':mp.nstr(v400-v500,12),'residual':mp.nstr(v500-rhs,12),
        'precision_dps':mp.mp.dps,'S4_tail':'Floating-point display only; rigorous S4 enclosures are in s4_interval_certificate.json.'})
    summary={'status':'PASS','euler_asymptotic_cases':len(errors),'zero_asymptotic_cases':len(zeros),
             'zero_table_entries':len(table),'s4_numerical_case':1,
             'seconds':round(time.time()-start,3),'mpmath':mp.__version__,
             'scope':'Floating-point diagnostics, distinct from the exact rational enclosures.'}
    write('numerical_summary.json',summary);print(json.dumps(summary,indent=2))
if __name__=='__main__':main()
