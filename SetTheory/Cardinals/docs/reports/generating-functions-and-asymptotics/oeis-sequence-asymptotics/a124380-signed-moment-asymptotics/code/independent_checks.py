#!/usr/bin/env python3
"""Independent finite exact-symbolic checks; no network or source edits.
These corroborate algebra only; the analytic error proof is in the companion report.
"""
from pathlib import Path
import importlib.util
import hashlib
import json
import sys
import sympy as s

BASE=Path(__file__).resolve().parent
sys.path.insert(0,str(BASE))
from replay_coefficients import coefficients as positive
from replay_oscillatory import coefficients as negative
from replay_inverse import inverse_coefficients
R=4
L,y,h,p,c=s.symbols('L y h p c',real=True)
ll=sum((-1)**(k+1)*(h*y)**k/s.Integer(k) for k in range(1,R+4))
stirling=sum(s.bernoulli(2*r)/s.Integer(2*r*(2*r-1))*h**(2*r-1)*s.series((1+h*y)**(-(2*r-1)),h,0,R+1).removeO() for r in range(1,(R+1)//2+2))
phase={}
for sign in (1,-1):
    raw=(2/h**2+sign/h+sign*y+s.Rational(1,2))*ll+sign*y*L-2*y/h-y*y+sign*y-sign*stirling
    raw=s.series(raw-(-2*y*y+sign*(L+2)*y),h,0,R+1).removeO().expand()
    assert raw.coeff(h,0)==0
    phase[sign]=[s.Integer(0)]+[s.expand(raw.coeff(h,j)) for j in range(1,R+1)]
Lp,pp,qp,Pp=positive(R)
Lm,ym,pm,pn,qn=negative(R)
for j in range(1,R+1):
    assert s.expand(phase[1][j]-pp[j].subs({Lp:L, s.Symbol('y'):y}))==0
    assert s.expand(phase[-1][j]-pn[j].subs({Lm:L,ym:y,pm:p}))==0
    assert s.expand(phase[-1][j].subs(y,-y)-(-1)**j*phase[1][j])==0
print('PASS: both Bernoulli phase generators against direct Stirling expansion through order 4')

def gaussian_moment(k,mu):
    return sum(s.binomial(k,2*r)*s.factorial2(2*r-1)*s.Rational(1,4)**r*mu**(k-2*r) for r in range(k//2+1))

def independently_exponentiate(rr):
    out=[s.Integer(1)]+[s.Integer(0)]*R
    for j in range(1,R+1):
        factor=[s.Integer(0)]*(R+1)
        for m in range(R//j+1):factor[j*m]=rr[j]**m/s.factorial(m)
        out=[s.expand(sum(out[k]*factor[d-k] for k in range(d+1))) for d in range(R+1)]
    return out

for sign in (1,-1):
    integrand=independently_exponentiate(phase[sign])
    mu=(L+2)/4 if sign==1 else -(L+2)/4+s.I*p/4
    targets=qp if sign==1 else qn
    for j,Q in enumerate(integrand):
        got=s.expand(sum(co*gaussian_moment(ex[0],mu) for ex,co in s.Poly(Q,y).terms()))
        target=targets[j].subs({Lp:L,Lm:L,pm:p})
        assert s.expand(got-target)==0
print('PASS: both exponential/Gaussian generators against independent product and explicit moments through order 4')
for j in range(R+1):
    assert s.expand(qn[j].subs({Lm:L,pm:p})-(-1)**j*qp[j].subs(Lp,L-s.I*p))==0
print('PASS: qminus_j(L,p) = (-1)^j qplus_j(L-i*p), through order 4; all-order algebra proved separately')

# Verify inverse by direct formal series substitution rather than the generator's
# derivative-factor recurrence. Coefficients are kept generic until extraction.
Li,ci,di,bi=inverse_coefficients(R)
di=[d.subs({Li:L,ci:c}) for d in di]
D=s.symbols('D0:5')
v=sum(D[j]*h**(j+1) for j in range(R+1))
w=s.series(s.log(1+v),h,0,R+2).removeO()
res=(1+v)**2*(2*L+2*w-1)-(2*L-1)
res+=h*(1+v)*(L+w+1)+h*h*((L+w)**2/8+L+w+c)
for j in range(1,R):
    res+=h**(j+2)*s.series((1+v)**(-j),h,0,R+2-j).removeO()*Pp[j].subs(Lp,L+w)
res=s.series(res,h,0,R+2).removeO().expand()
for j in range(1,R+2):
    assert s.factor(res.coeff(h,j).subs(dict(zip(D,di))))==0
for j in range(R+1):
    assert s.factor(bi[j].subs({Li:L,ci:c})-4*di[j]-2*sum(di[k]*di[j-1-k] for k in range(j)))==0
print('PASS: independent formal inverse composition and n=2*x^2 conversion through b4')

# Fourier-Gaussian moments have generating function exp(i*p*z/H+z^2/(2H)).
z,H=s.symbols('z H',positive=True)
mu=[s.Integer(1),s.I*p/H]
for k in range(2,10):mu.append(s.expand(s.I*p/H*mu[-1]+s.Rational(k-1)/H*mu[-2]))
mgf=s.series(s.exp(s.I*p*z/H+z*z/(2*H)),z,0,10).removeO().expand()
for k in range(10):assert s.expand(s.factorial(k)*mgf.coeff(z,k)-mu[k])==0
assert s.expand(mu[3]/6-s.I*(p/(2*H**2)-p**3/(6*H**3)))==0
print('PASS: Fourier-Gaussian moment recurrence and first cosine correction')
print('ALL EXACT CHECKS PASSED')

# Check the actual coefficient formulas printed in the integrated appendix.
printedN2=-L**7-6*L**6-18*L**5+(24*c-35)*L**4+(24*c-12)*L**3+(-24*c+9)*L**2+7*L-3
printedN3=8*L**9+15*L**8+24*L**7+(-48*c-10)*L**6+(192*c*c-240*c+173)*L**4+(-192*c+88)*L**3+(144*c-42)*L**2-40*L+15
printedN4=9*L**13+75*L**12+105*L**11+(-240*c+1290)*L**10+(-960*c+2610)*L**9+(-2880*c+4418)*L**8+(2880*c*c-8400*c+3525)*L**7+(5760*c*c-11280*c+5040)*L**6+(2880*c*c-3600*c+1830)*L**5+(-8640*c*c+8160*c-4290)*L**4+(6000*c-2619)*L**3+(-3600*c+870)*L**2+945*L-315
printed=[-(L+1)/L,-(L**4+6*L**3+(8*c-5)*L**2-2*L+1)/(8*L**3),printedN2/(96*L**5),-printedN3/(1536*L**7),printedN4/(92160*L**9)]
for a,b in zip(printed,bi):assert s.factor(a-b.subs({Li:L,ci:c}))==0
print('PASS: all five printed inverse appendix polynomials match the independently composition-checked generator')
V=sum(qp[j].subs(Lp,L)*h**j for j in range(1,R+1))
logV=s.series(sum((-1)**(k+1)*V**k/s.Integer(k) for k in range(1,R+1)),h,0,R+1).removeO().expand()
for j in range(1,R+1):assert s.factor(logV.coeff(h,j)-Pp[j].subs(Lp,L))==0
print('PASS: logarithmic coefficients against independent finite log-series extraction through order 4')
print('ALL INTEGRATED COEFFICIENT CHECKS PASSED')
