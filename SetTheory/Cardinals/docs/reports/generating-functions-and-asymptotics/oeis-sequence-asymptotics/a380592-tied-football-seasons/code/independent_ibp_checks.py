#!/usr/bin/env python3
"""Verify the first correction independently by Gaussian integration by parts.

Single-match logarithmic Taylor series, Stein recursions, and direct tilt
and determinant expansions provide an alternative to set-partition moments.
"""
import sympy as S
from functools import lru_cache
from collections import defaultdict
from output_support import write_result
import json

n,a,b,t,x,y,h,q,delta=S.symbols('n a b t x y h q delta')
P=S.symbols('P0:7')
# Direct Taylor expansion of log E exp(i h X), centered after taking log.
# This computes each single-match cumulant independently of the moment-cumulant recurrence.
mgf=sum(sum((S.I*h*z)**r/S.factorial(r) for r in range(7)) for z in (3*x,x+y,3*y))/3
z=S.expand(mgf-1)
logmgf=S.Integer(0)
# Polynomial multiplication with immediate truncation avoids massive expansions.
def trunc(expr,deg=6):
    return sum(c*h**pw[0] for pw,c in S.Poly(S.expand(expr),h).terms() if pw[0]<=deg)
power=S.Integer(1)
for j in range(1,7):
    power=trunc(power*z)
    logmgf+=(-1)**(j+1)*power/S.Integer(j)
logmgf=S.expand(logmgf-S.I*h*S.Rational(4,3)*(x+y))
L={}
single={}
for r in range(3,7):
    single[r]=S.expand(logmgf.coeff(h,r))
    # Two matches per unordered pair = sum over ordered distinct pairs.
    poly=S.Poly(single[r],x,y)
    L[r]=S.expand(sum(coef*(P[i]*P[j]-P[i+j]) for (i,j),coef in poly.terms()).subs(P[0],n))

# Exact IBP recurrence: E[P_d product P_e]. The covariance is a I + b J.
# Terms are polynomials in n,a,b, represented as sparse exponent dictionaries.
@lru_cache(None)
def moment(ds):
    zeros=ds.count(0)
    if zeros:
        return tuple(((pn+zeros,pa,pb),c) for (pn,pa,pb),c in moment(tuple(d for d in ds if d)))
    if not ds:return (((0,0,0),1),)
    if sum(ds)%2:return ()
    d,*rest=ds
    out=defaultdict(int)
    def add(degs,factor,da,db):
        if not factor:return
        for (pn,pa,pb),c in moment(tuple(sorted(degs))):
            out[pn,pa+da,pb+db]+=factor*c
    if d>=2:
        add([d-2]+rest,d-1,1,0)
        add([d-2]+rest,d-1,0,1)
    for k,e in enumerate(rest):
        others=rest[:k]+rest[k+1:]
        add([d+e-2]+others,e,1,0)
        add([d-1,e-1]+others,e,0,1)
    return tuple((key,c) for key,c in out.items() if c)

# Use exact covariance rational functions and direct Taylor expansion in t=1/n.
# Each monomial has a=(9t/28)/(1-t/14), b=(117t²/28)/((1-t)(1-t/14)).
@lru_cache(None)
def cov_series(pa,pb,degree):
    return tuple(S.expand(S.series((1-t/S.Integer(14))**(-pa-pb)*(1-t)**(-pb),t,0,degree+1).removeO()).coeff(t,j) for j in range(degree+1))

@lru_cache(None)
def Emon(ds,pn,order):
    out=defaultdict(lambda:S.Integer(0))
    for (pn2,pa,pb),c in moment(ds):
        exponent=pa+2*pb-pn-pn2
        if exponent>order:continue
        pref=c*S.Rational(9,28)**pa*S.Rational(117,28)**pb
        for j,v in enumerate(cov_series(pa,pb,order-exponent)):
            out[exponent+j]+=pref*v
    return tuple(sorted((e,S.factor(c)) for e,c in out.items() if c))

def expect(poly,order=1):
    out=S.Integer(0)
    for powers,c in S.Poly(S.expand(poly),n,*P[1:]).terms():
        ds=tuple(d for d,times in enumerate(powers[1:],1) for _ in range(times))
        out+=c*sum(v*t**e for e,v in Emon(ds,powers[0],order))
    return S.expand(out)

def series_mul(*polys,order=1):
    return S.series(S.prod(polys),t,0,order+1).removeO().expand()

names={'L4':L[4],'L6':L[6],'L3sq':L[3]**2,'L3L5':L[3]*L[5],
       'L4sq':L[4]**2,'L3sqL4':L[3]**2*L[4],'L3four':L[3]**4}
means={key:expect(poly,2) for key,poly in names.items()}
var4=S.expand(means['L4sq']-series_mul(means['L4'],means['L4'],order=2))
k334=S.expand(means['L3sqL4']-series_mul(means['L3sq'],means['L4'],order=2))
k3333=S.expand(means['L3four']-3*series_mul(means['L3sq'],means['L3sq'],order=2))
local=S.expand(means['L4']+means['L3sq']/2+means['L6']+means['L3L5']+var4/2+k334/2+k3333/24)

# Verify the omitted fourth cumulants at order 1/n, including all subtractions.
# κ(A,A,B,B)=E A²B²-E A² E B²-2(E AB)²-2 E B E A²B+2 E A²(E B)²; E A=E AB=0.
k3344=expect(L[3]**2*L[4]**2,1)-series_mul(means['L3sq'],means['L4sq'])-2*series_mul(means['L4'],means['L3sqL4'])+2*series_mul(means['L3sq'],means['L4'],means['L4'])
k3335=expect(L[3]**3*L[5],1)-3*series_mul(means['L3sq'],means['L3L5'])

# General-q leading C and its derivative.
beta=q*(1-q); alpha=(9-8*q-q*q)/2
d3=beta*(q+13)/12; b3=beta*(q+4)/2
A4=beta*(1-6*q+6*q*q);B4=54*beta*(2*q-1);C4=81*(1-q)*(3*q-2)
C=(3*A4+B4+3*C4)/(96*alpha**2)-3*d3**2/alpha**3-b3**2/(2*beta*alpha**2)
C0=S.factor(C.subs(q,S.Rational(1,3)))
Cd=S.factor(S.diff(C,q).subs(q,S.Rational(1,3)))

# Independently derive C(q) from the general-q one-match law and leading IBP moments.
general_mgf=sum(prob*sum((S.I*h*z)**r/S.factorial(r) for r in range(5))
                for prob,z in (((1-q)/2,3*x),(q,x+y),((1-q)/2,3*y)))
general_z=S.expand(general_mgf-1)
general_log=S.Integer(0);power=S.Integer(1)
for j in range(1,5):
    power=trunc(power*general_z,4)
    general_log+=(-1)**(j+1)*power/S.Integer(j)
general_log=S.expand(general_log)
general_L={}
for r in (3,4):
    general_L[r]=S.expand(sum(coef*(P[i]*P[j]-P[i+j])
                         for (i,j),coef in S.Poly(general_log.coeff(h,r),x,y).terms()).subs(P[0],n))
A,B=S.symbols('A B')
def leading_expectation(poly):
    result=S.Integer(0)
    for powers,c in S.Poly(S.expand(poly),n,*P[1:]).terms():
        ds=tuple(d for d,times in enumerate(powers[1:],1) for _ in range(times))
        for (pn,pa,pb),v in moment(ds):
            exponent=pa+2*pb-powers[0]-pn
            assert exponent>=0
            if exponent==0:result+=c*v*A**pa*B**pb
    return S.factor(result)
C_general_independent=S.factor(leading_expectation(general_L[4]+general_L[3]**2/2).subs({A:1/alpha,B:1/beta-1/alpha}))
assert S.factor(C_general_independent-C)==0
# Assert the first two local coefficients directly; replay compares all
# independently computed polynomials and moments with frozen exact fixtures.
assert local.coeff(t,0) == -S.Rational(7865,32928)
assert local.coeff(t,1) == S.Rational(1147975,45177216)

# Tilt and determinant expansions directly from their defining functions.
qstar=S.Rational(1,3)-delta*t/(1-t)
D=q*S.log(3*q)+(1-q)*S.log(3*(1-q)/2)
Dser=S.series(D.subs(q,S.Rational(1,3)+x),x,0,5).removeO()
rate=S.series(-(1-t)/t**2*Dser.subs(x,qstar-S.Rational(1,3)),t,0,2).removeO().expand()
lam=lambda z:alpha.subs(q,z)/t-beta.subs(q,z)
rho=lambda z:(1/t-1)*beta.subs(q,z)
# Expand the log determinant ratios to second order, because of factor (n-1).
logl=S.series(S.log(lam(qstar)/lam(S.Rational(1,3))),t,0,3).removeO()
logr=S.series(S.log(rho(qstar)/rho(S.Rational(1,3))),t,0,2).removeO()
determinant=S.series(-(1/t-1)*logl/2-logr/2,t,0,2).removeO().expand()
carrier=S.series(-S.log(1-t)/2-(1/t-1)*S.log(1-t/14)/2,t,0,2).removeO().expand()
Q=S.factor(local.coeff(t,1)-Cd*delta+rate.coeff(t,1)+determinant.coeff(t,1)+carrier.coeff(t,1))
expected=S.Rational(22180735,45177216)+S.Rational(98841,153664)*delta-S.Rational(5283,3136)*delta**2-S.Rational(9,8)*delta**3
assert S.expand(Q-expected)==0
assert S.expand(k3344)==0 and S.expand(k3335)==0
out={'method':'Direct logarithmic single-match Taylor series; Gaussian Stein/IBP power-sum recurrence; exact rational covariance series.',
     'single_match_log_terms':{str(k):str(v) for k,v in single.items()},
     'L':{str(k):str(v) for k,v in L.items()},
     'moments_through_n_minus_2':{k:str(v) for k,v in means.items()},
     'var_L4_through_n_minus_2':str(var4),'kappa_334_through_n_minus_2':str(k334),
     'kappa_3333_through_n_minus_2':str(k3333),
     'local_log_constant_and_n_minus_1':[str(local.coeff(t,i)) for i in range(2)],
     'omitted_kappa_3344_through_n_minus_1':str(S.expand(k3344)),
     'omitted_kappa_3335_through_n_minus_1':str(S.expand(k3335)),
     'C_general_independently_derived':str(C_general_independent),'C_general_matches':True,
     'C0':str(C0),'Cprime':str(Cd),'rate':str(rate),'determinant':str(determinant),
     'carrier':str(carrier),'Q':str(S.expand(Q)),'Q_matches':True}
write_result('independent_ibp_checks', out)
print(json.dumps(out,indent=2))
