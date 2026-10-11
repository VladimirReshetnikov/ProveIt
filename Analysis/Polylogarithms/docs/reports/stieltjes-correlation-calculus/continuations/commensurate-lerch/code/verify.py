#!/usr/bin/env python3
"""Independent exact checks and numerical diagnostics, not interval certification."""
from __future__ import annotations
import argparse, json, platform, time
from pathlib import Path
import sympy as sp
import mpmath as mp
from commensurate import *
ROOT=Path(__file__).resolve().parents[1]
records=[]
def exact(name, expression):
    ok=sp.simplify(sp.expand_trig(expression))==0
    records.append({'kind':'exact','name':name,'passed':bool(ok)})
    if not ok: raise AssertionError((name,expression))
def numerical(name,lhs,rhs,tol='1e-36'):
    err=abs(lhs-rhs)/max(mp.mpf(1),abs(lhs),abs(rhs));ok=err<mp.mpf(tol)
    records.append({'kind':'numerical','name':name,'passed':bool(ok),'normalized_error':mp.nstr(err,9),'tolerance':tol,'lhs':mp.nstr(lhs,48),'rhs':mp.nstr(rhs,48)})
    if not ok: raise AssertionError((name,mp.nstr(err,15),mp.nstr(lhs,50),mp.nstr(rhs,50)))
def negative(name,observed,wrong,tol='1e-10'):
    ok=abs(observed-wrong)>mp.mpf(tol)
    records.append({'kind':'negative_control','name':name,'passed':bool(ok)})
    if not ok: raise AssertionError(name)

def exact_suite():
    families=[(1,), (1,1),(1,2),(1,3),(1,4),(2,3),(1,1,1),(1,1,2),(1,2,2),(1,2,3),(1,3,3),(2,2,3),(1,1,1,1),(1,1,2,2),(1,2,3,3),(1,1,1,1,1),(sp.Rational(1,2),sp.Rational(3,2)),(sp.Rational(2,3),1,2)]
    for qs in families:
        tab=pole_table(qs); independent=direct_local_table(qs)
        for key,a in tab.coefficients.items():exact(f'Bell/direct rates={qs} pole={key}',a-independent.coefficients[key])
        if tab.sign==1:exact(f'zero residue sum {qs}',sum(a for (rho,k),a in tab.coefficients.items() if k==1))
        scaled=pole_table(tuple(2*q for q in qs))
        for (rho,k),a in tab.coefficients.items():exact(f'coefficient scaling {qs} {rho,k}',scaled.coefficients[2*rho,k]-2**sp.Integer(k-len(qs))*a)
    for m in range(1,7):
        tab=pole_table((1,m))
        for r in range(1,m):exact(f'two-scale simple pole m={m} r={r}',tab.coefficients[sp.Integer(r),1]-(-1)**r*sp.pi/m/sp.sin(sp.pi*r/m))
        exact(f'two-scale double pole m={m}',tab.coefficients[sp.Integer(m),2]-(-1)**(m+1))
        exact(f'two-scale vanished simple pole m={m}',tab.coefficients[sp.Integer(m),1])
    T,U,kappa,s=sp.symbols('T U kappa s'); R=sp.Integer(1);gpoly=[sp.Integer(1)]
    for ell in range(7):
        if ell:gpoly.append(sp.expand(T*gpoly[-1]+(kappa+T*T)*sp.diff(gpoly[-1],T)))
        direct=sum(sp.binomial(ell,d)*sp.rf(s,d)*U**d*gpoly[ell-d] for d in range(ell+1))
        exact(f'mixed-moment recurrence ell={ell}',R-direct)
        R=sp.expand((T+s*U)*R+(kappa+T*T)*sp.diff(R,T)+U*U*sp.diff(R,U))
    z=sp.symbols('z')
    for j in range(1,10):
        logpoly=sum((-1)**(n-1)*sp.harmonic(j-1,n)*z**n/n for n in range(1,6))
        rhs=sp.series(sp.factorial(j-1)*z*sp.exp(logpoly),z,0,6).removeO()
        for h in range(1,min(j,5)+1):exact(f'harmonic Pochhammer j={j} h={h}',sp.expand(sp.rf(z,j)).coeff(z,h)-sp.expand(rhs).coeff(z,h))
    for qs in [(1,1,1),(1,2,3),(2,3,4)]:
        exact(f'universal cubic value {qs}',odd_resonance(qs,0)-sp.pi**2*sum(sp.Rational(q)**(-2) for q in qs)/12)
        exact(f'universal cubic resonance -2 {qs}',odd_resonance(qs,2)-sp.Rational(1,2))
        exact(f'universal cubic resonance -4 {qs}',odd_resonance(qs,4))
    expected={(1,1):-sp.sqrt(3)*sp.pi**2/9,(2,1):-2*sp.pi**2/27,(2,2):-2*sp.sqrt(3)*sp.pi/9,(3,1):0,(3,2):-sp.pi/2,(4,1):2*sp.pi**2/27,(4,2):-2*sp.sqrt(3)*sp.pi/9,(5,1):sp.sqrt(3)*sp.pi**2/9,(6,1):-49*sp.pi**2/216,(6,2):0,(6,3):-1}
    tab=pole_table((1,2,3))
    for key,val in expected.items():exact(f'printed 1,2,3 table {key}',tab.coefficients[key]-val)
    corrupted=dict(tab.coefficients);corrupted[sp.Integer(1),1]+=sp.pi**2/9
    detected=sp.simplify(corrupted[sp.Integer(1),1]-direct_local_table((1,2,3)).coefficients[sp.Integer(1),1])!=0
    records.append({'kind':'negative_control','name':'reject corrupted Laurent table coefficient','passed':bool(detected)})
    if not detected:raise AssertionError('corrupted Laurent coefficient accepted')
    try:
        pole_table((1,0));raise AssertionError('zero rate accepted')
    except ValueError:records.append({'kind':'negative_control','name':'reject nonpositive rate','passed':True})

def numeric_suite():
    mp.mp.dps=55
    families=[(1,), (1,1),(1,2),(1,3),(2,3),(1,1,2),(1,2,3),(1,1,2,2)]
    cases=[(mp.mpf('0'),mp.mpf('0')),(mp.mpf('1'),mp.mpf('.3')),(mp.mpf('-2'),mp.mpf('0')),(mp.mpc('.4','.3'),mp.mpc('.2','.1'))]
    for qs in families:
        tab=pole_table(qs)
        for w,A in cases:numerical(f'central/contour q={qs} W={w} A={A}',central(tab,w,A),contour(qs,w,A))
    for qs in [(1,2),(1,3),(1,2,3)]:
        tab=pole_table(qs)
        for w in [mp.mpf('-1'),mp.mpc('.7','.2')]:numerical(f'Lerch/contour q={qs} W={w}',off_centre(tab,w,mp.mpf('.2'),mp.mpf('-.4')),contour(qs,w,mp.mpf('.2'),mp.mpf('-.4')))
    for m in range(1,7):
        direct=mp.quad(lambda x:mp.log1p(mp.exp(x))*mp.log1p(mp.exp(-m*x)),[-mp.inf,0,mp.inf])
        numerical(f'ordinary log product m={m}',direct,pair_master(m,1,1))
    L3=lambda w:mp.power(3,-w)*(mp.zeta(w,mp.mpf(1)/3)-mp.zeta(w,mp.mpf(2)/3))
    numerical('Catalan explicit integral',pair_master(2,1,1),mp.pi*mp.catalan-3*mp.zeta(3)/8)
    numerical('character-three explicit integral',pair_master(3,1,1),2*mp.pi/mp.sqrt(3)*L3(2)+2*mp.zeta(3)/9)
    numerical('raw order swap first',pair_master(2,1,0),5*mp.pi**2/48)
    numerical('raw order swap second',pair_master(2,0,1),5*mp.pi**2/24)
    negative('unnormalized pure order addition',pair_master(2,1,0),pair_master(2,0,1))
    negative('lost resonant W*zeta(W+1) contribution',central(pole_table((1,3)),0),2*mp.pi/(9*mp.sqrt(3)))
    for m in [2,3]:
        for ell in [1,2,3]:
            q=mp.mpf(m);c=mp.mpf('.5')
            direct=mp.quad(lambda x:x**ell/(1+mp.exp(-x))/(1+mp.exp(m*x)),[-mp.inf,0,mp.inf])
            def integrand(t):
                p=c+1j*t
                return (-1)**ell*mp.diff(lambda v:mp.pi/mp.sin(mp.pi*v),p,ell)*(mp.pi/q)/mp.sin(mp.pi*p/q)
            spec=mp.quad(integrand,[-mp.inf,0,mp.inf])/(2*mp.pi)
            numerical(f'ordinary logarithmic moment m={m} ell={ell}',direct,spec)
    def primitive(m,A):
        sigma=(-1)**(m+1);mm=mp.mpf(m);b=(A+mm)/mm
        if sigma==1:return (mp.digamma(b)-mp.pi*mp.fsum((-1)**(r+1)/mp.sin(mp.pi*r/mm)*mp.loggamma((A+r)/mm) for r in range(1,m)))/mm
        return (eta(1,b)-mp.pi*mp.fsum((-1)**(r+1)/mp.sin(mp.pi*r/mm)*(mp.loggamma((A+r)/(2*mm))-mp.loggamma(((A+r)/mm+1)/2)) for r in range(1,m)))/mm
    for m in [2,3,4,5]:
        for A in [mp.mpf('.2'),mp.mpf('1.1')]:numerical(f'Gamma primitive m={m} A={A}',mp.diff(lambda a:primitive(m,a),A),central(pole_table((1,m)),1,A))
    def zjet(h,b):
        if h==0:return mp.zeta(0,b)
        if h==1:return mp.loggamma(b)-mp.log(2*mp.pi)/2
        return mp.diff(lambda v:mp.zeta(v,b),0,h)
    def etazerojet(h,b):return mp.fsum(mp.binomial(h,j)*(-mp.log(2))**(h-j)*(zjet(j,b/2)-zjet(j,(b+1)/2)) for j in range(h+1))
    def etaonejet(h,b):return mp.fsum(mp.binomial(h,j)*(-mp.log(2))**(h-j)*(-1)**j*(mp.stieltjes(j,b/2)-mp.stieltjes(j,(b+1)/2)) for j in range(h+1))/2
    def pairjet(m,M,A):
        sigma=(-1)**(m+1);mm=mp.mpf(m);b=(A+mm)/mm;ans=0
        for h in range(M+1):
            fn=zjet if sigma==1 else etazerojet
            bracket=mp.pi*mp.fsum((-1)**(r+1)/mp.sin(mp.pi*r/mm)*fn(h,(A+r)/mm) for r in range(1,m))
            if sigma==1:bracket+=1 if h==0 else (-1)**(h-1)*h*mp.stieltjes(h-1,b)
            elif h:bracket-=h*etaonejet(h-1,b)
            ans+=mp.binomial(M,h)*(-mp.log(mm))**(M-h)*bracket/mm
        return ans
    for m in [2,3]:
        for M in range(1,4):numerical(f'Stieltjes jet m={m} M={M}',pairjet(m,M,mp.mpf('.2')),contour((1,m),0,mp.mpf('.2'),jet=M))
    d2=mp.pi/2*mp.log(mp.gamma(mp.mpf(1)/4)/mp.gamma(mp.mpf(3)/4))-(mp.pi+1)*mp.log(2)/2
    numerical('printed quarter-Gamma jet',d2,contour((1,2),0,jet=1))
    d3=2*mp.pi/(3*mp.sqrt(3))*mp.log(mp.gamma(mp.mpf(1)/3)/mp.gamma(mp.mpf(2)/3))-2*mp.pi*mp.log(3)/(9*mp.sqrt(3))+(mp.euler-mp.log(3))/3
    numerical('printed third-Gamma jet',d3,contour((1,3),0,jet=1))
    with mp.workdps(100):
        def fN(N,x):
            y=mp.exp(x)
            if x < -2:return mp.fsum((-1)**k*y**(k+1)/(N+1+k) for k in range(180))
            R=-mp.log1p(y)-mp.fsum((-y)**k/k for k in range(1,N+1))
            return -(-y)**(-N)*R
        direct=-mp.quad(lambda x:fN(2,x)*fN(1,-2*x),[-80,-2,0,2,80])
        numerical('balanced harmonic remainder m=2 N=1',direct,remainder_master(2,1,1,1),tol='1e-30')
    for qs in [(1,1),(1,2),(1,2,3)]:
        tab=pole_table(qs);A=mp.mpf('.4')
        orders=[mp.mpc('.3','.1')+mp.mpf(j)/10 for j in range(len(qs))]
        deltas=[mp.mpf('0.006')*(-1)**j for j in range(len(qs))]
        coeff=unequal_coefficients(orders,deltas,24);W=sum(orders)
        approx=mp.fsum(coeff[n]*central(tab,W+n,A) for n in range(25))
        direct=contour(qs,W,shifts=[A+d for d in deltas],orders=orders)
        numerical(f'unequal-center expansion q={qs}',approx,direct,tol='1e-42')
    rates=[mp.mpf(1),mp.sqrt(2),mp.sqrt(3)];c=mp.mpf('.4')
    for N in [0,2,4]:
        def integrand(t):
            p=c+1j*t
            return mp.fprod((mp.pi/q)/mp.sin(mp.pi*p/q) for q in rates)*p**N
        direct=mp.quad(integrand,[-mp.inf,0,mp.inf])/(2*mp.pi)
        expected=mp.pi**2*mp.fsum(q**(-2) for q in rates)/12 if N==0 else (mp.mpf('.5') if N==2 else 0)
        numerical(f'irrational-rate parity N={N}',direct,expected)

if __name__=='__main__':
    parser=argparse.ArgumentParser();parser.add_argument('--part',choices=['exact','numeric','all'],default='all');args=parser.parse_args();start=time.time();failed=False
    try:
        if args.part in ('exact','all'):exact_suite()
        if args.part in ('numeric','all'):numeric_suite()
    except Exception:
        failed=True;raise
    finally:
        counts={k:sum(r['kind']==k for r in records) for k in ['exact','numerical','negative_control']}
        output={'part':args.part,'python':platform.python_version(),'sympy':sp.__version__,'mpmath':mp.__version__,'working_decimal_digits':55 if args.part!='exact' else None,'elapsed_seconds':round(time.time()-start,3),'counts':counts,'passed':not failed and all(r['passed'] for r in records),'records':records}
        dest=ROOT/'verification'/f'{args.part}-results.json';dest.write_text(json.dumps(output,indent=2)+'\n')
        print(json.dumps({k:v for k,v in output.items() if k!='records'},indent=2),flush=True)
