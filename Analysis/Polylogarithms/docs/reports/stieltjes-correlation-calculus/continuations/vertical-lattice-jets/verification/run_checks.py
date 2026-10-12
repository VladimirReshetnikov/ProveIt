#!/usr/bin/env python3
"""Reproducible exact algebra and independent floating-point diagnostics."""
from pathlib import Path
import json,sys,time,platform
import mpmath as mp
import sympy as sp
from lattice import *
ROOT=Path(__file__).resolve().parents[1]
mp.mp.dps=65
started=time.monotonic(); exact=0; rows=[]
x,s,e=sp.symbols('x s e')

def prove(expr):
    global exact
    assert sp.expand(expr)==0,expr
    exact+=1

def check(name,lhs,rhs,tol='1e-32'):
    error=abs(lhs-rhs)/max(mp.mpf(1),abs(lhs),abs(rhs))
    passed=error<mp.mpf(tol)
    category=('same-master differential cross-check' if name.startswith(('primitive_', 'negative_jet_Bell_')) else 'independent evaluation routes or normalization control')
    row={'name':name,'category':category,'lhs':mp.nstr(lhs,48),'rhs':mp.nstr(rhs,48),
         'scaled_residual':mp.nstr(error,8),'tolerance':tol,'passed':passed}
    rows.append(row);print(name,row['scaled_residual'],passed,flush=True)
    assert passed,row

# Hurwitz Bernoulli polynomial vanishing and exact contact coefficient.
for N in range(19):
    M=(N+1)//2
    rem=-sp.bernoulli(N+1,x)/sp.Integer(N+1)+x**(N+1)/sp.Integer(N+1)-x**N/2
    for j in range(1,M+1):
        rem-=sp.bernoulli(2*j)*sp.rf(-N,2*j-1)*x**(N+1-2*j)/sp.factorial(2*j)
    prove(rem)
    for k in range(N+1,N+10):
        prove(sp.diff(sp.rf(s,k),s).subs(s,-N)-(-1)**N*sp.factorial(N)*sp.factorial(k-N-1))
for M in range(13):
    prove(sp.diff(sp.bernoulli(2*M+2)*sp.rf(s,2*M+1)/sp.factorial(2*M+2),s).subs(s,-2*M)
          -sp.bernoulli(2*M+2)/sp.Integer((2*M+1)*(2*M+2)))
# The harmonic-number logarithmic derivative used in the explicit T_N formula.
for N in range(1,16):
    for j in range(1,(N+1)//2+1):
        k=2*j-1
        prove(sp.diff(sp.rf(s,k),s).subs(s,-N)-sp.factorial(N)/sp.factorial(N-k)*(sp.harmonic(N)-sp.harmonic(N-k)))
# Finite geometric and partial-fraction mechanisms, and a corruption control.
Q,y=sp.symbols('Q y')
prove(sp.together(1/((1-y)*(1-Q*y))-(1/(1-y)-Q/(1-Q*y))/(1-Q)).as_numer_denom()[0])
corruption_rejected=(sp.diff(sp.rf(s,3),s).subs(s,-2)!=-2)
assert corruption_rejected

# Main scalar sampling on both sides of several spectral resonances.
a=mp.mpf('0.8');h=mp.mpf('2.1');tau=2*mp.pi/h
for ss,M in [(mp.mpf(1),0),(mp.mpc('1.4','0.3'),0),(mp.mpf('-0.4'),1),
             (mp.mpf('-2.3'),2),(mp.mpf('2.7'),0),(mp.mpf('-4.2'),3)]:
    check(f'master_s={ss}_M={M}',lattice_remainder(ss,a,h,M),tau**ss*mp.rgamma(ss)*bracket(ss,a,h,M))
for aa,hh in [(mp.mpc('1.1','0.25'),mp.mpf('2.6')),(mp.mpf('1.2'),mp.mpf('1.8'))]:
    ss=mp.mpc('1.3','0.2');tt=2*mp.pi/hh
    check(f'master_complex_base_{aa}',lattice_remainder(ss,aa,hh),tt**ss*mp.rgamma(ss)*bracket(ss,aa,hh))
# Independently constructed complex-safe Stieltjes jets.
for m in range(4):
    check(f'Stieltjes_jet_{m}',stieltjes_lattice(m,a,h),stieltjes_rhs(m,a,h))
# Resonant generalized Gamma ladder, including even and odd N.
for N in range(7):
    check(f'negative_integer_jet_{N}',negative_jet_lattice(N,a,h),negative_jet_rhs(N,a,h))
# A deliberate omission of the known Gamma contact is rejected.
correct=negative_jet_lattice(0,a,h)
wrong=bracket(0,a,h,0)
check('omitted_Gamma_contact_equals_tau_over_24',correct-wrong,tau/24)
assert abs(correct-wrong)>mp.mpf('0.01')
# Finite-image pairings, checked against a direct outer-lattice asymptotic tail.
b=mp.mpf('1.2')
for r,t in [(2,2),(2,3),(3,4),(4,2)]:
    check(f'polygamma_pair_{r}_{t}',bilinear_lattice(r,t,a,b,h),bilinear_rhs(r,t,a,b,h),tol='1e-30')
# Four-shift tests reduce independently to finite elementary reciprocal pairings.
for L,K in [(1,1),(2,1),(2,3)]:
    rhs=four_shift_rhs(a,a+L,b,b+K,h)
    lhs=mp.fsum(tau/(2*(a+j+b+k))*(mp.coth(tau*(a+j)/2)+mp.coth(tau*(b+k)/2))
                for j in range(L) for k in range(K))
    check(f'four_shift_integer_lengths_{L}_{K}',lhs,rhs)
# Noninteger horizontal shifts: numerical quadrature of the zero and image terms.
c=mp.mpf('1.35');d=mp.mpf('1.85');entries=[(a,b,1),(a,d,-1),(c,b,-1),(c,d,1)]
f=lambda u:(mp.exp(-a*u)-mp.exp(-c*u))/(-mp.expm1(-u)) if u else c-a
g=lambda u:(mp.exp(-b*u)-mp.exp(-d*u))/(-mp.expm1(-u)) if u else d-b
zero=tau*mp.quad(lambda u:f(u)*g(u),[0,1,mp.inf])
zero_rhs=tau*mp.fsum(sign*(x+y-1)*mp.digamma(x+y) for x,y,sign in entries)
check('four_shift_noninteger_zero_image',zero,zero_rhs)
q=mp.exp(-tau)
for k in (1,3):
    ell=tau*k;Q=q**k
    image=tau*mp.quad(lambda u:f(u+ell)*g(u)+f(u)*g(u+ell),[0,1,mp.inf])
    image_rhs=-tau/(1-Q)*mp.fsum(sign*(q**(x*k)+q**(y*k))*(mp.digamma(x+y)+Q*lerch_small(Q,1,x+y)) for x,y,sign in entries)
    check(f'four_shift_noninteger_image_{k}',image,image_rhs)
# Anchored Stieltjes primitives and horizontal derivative identities.
for m in range(3):
    def prim(aa):
        return -mp.fsum(mp.binomial(m,j)*(-1)**j*exponential_jet(j,mp.log(tau)+mp.euler)*
                        (-1)**(m-j)*bracket(0,aa,h,0,m-j) for j in range(m+1))
    check(f'primitive_derivative_m={m}',mp.diff(prim,a),stieltjes_rhs(m,a,h))
for N in range(5):
    # Reciprocal-Gamma jet at -N: Bell/harmonic formula for its fourth derivative.
    ss=-N;L=(N+2)//2+1;order=4;lin=mp.log(tau)+mp.euler-mp.harmonic(N)
    lhs=mp.diff(lambda u:tau**u*mp.rgamma(u)*bracket(u,a,h,L),ss,order)
    rhs=(-1)**N*mp.factorial(N)*tau**(-N)*order*mp.fsum(
        mp.binomial(order-1,j)*exponential_jet(j,lin,N)*bracket(ss,a,h,L,order-1-j)
        for j in range(order))
    check(f'negative_jet_Bell_compiler_N={N}',lhs,rhs)
record={'python':platform.python_version(),'mpmath':mp.__version__,'sympy':sp.__version__,
        'working_decimal_digits':mp.mp.dps,'exact_assertions':exact,
        'numerical_comparisons':len(rows),'corruption_controls':2,
        'all_passed':all(r['passed'] for r in rows),'seconds':round(time.monotonic()-started,2),
        'scope':'Finite exact checks and non-interval floating-point diagnostics; analytic proofs are in article.tex.',
        'comparisons':rows}
(ROOT/'results'/'verification.json').write_text(json.dumps(record,indent=2)+'\n')
print(json.dumps({k:v for k,v in record.items() if k!='comparisons'},indent=2))
