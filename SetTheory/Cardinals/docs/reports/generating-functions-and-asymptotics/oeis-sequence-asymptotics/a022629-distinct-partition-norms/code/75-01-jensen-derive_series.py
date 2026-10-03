#!/usr/bin/env python3
"""Exact symbolic reproduction of inverse-log coefficients and inversion.

Requires SymPy. P denotes pi**2/s**2 and z denotes the reciprocal logarithm.
This file checks finite rational algebra; it is not a proof of asymptotic errors.
The article supplies the all-order coefficient recipe separately.
"""
from pathlib import Path
import sympy as S
z,a,P=S.symbols('z a P')
v=S.symbols('v')
u_der={}
for k in (1,3,5,7):
    f=a+sum((-1)**j*v**(j-1)/S.Integer(j) for j in range(2,k+1))
    ud=S.factor(S.factorial(k-1)*S.series(f**(-k),v,0,k).removeO().coeff(v,k-1))
    u_der[k]=ud
    print('u',k,ud,flush=True)
N=8
h=1/(2*z)-1
for r,k in enumerate((1,3,5,7)):
    eta_factor=S.simplify(2*(1-S.Rational(1,2)**(2*r+1))*S.zeta(2*r+2)/S.pi**(2*r+2))
    h+=eta_factor*P**(r+1)*u_der[k].subs(a,1/z-1)
tr=lambda f,n=N:S.series(f,z,0,n).removeO().expand()
h=tr(h)
B=tr((h-z*z*S.diff(h,z))/(1/z-1))
C=tr(h+B/z)
print('h',S.collect(h,z),flush=True)
print('2B',S.collect(2*B,z),flush=True)
logB=tr(S.log(2*B)/2)
d=S.Integer(0)
for i in range(3):
    d=tr(-logB.subs(z,z/(1+z*d)),N-1)
    print('d iteration',i,S.collect(d,z),flush=True)
G=tr(C/S.sqrt(2*B))
Gell=tr(G.subs(z,z/(1+z*d)),N-2)
print('Gell',S.collect(Gell,z),flush=True)
R=Gell-(1/z-1)
vv=S.Integer(0)
for i in range(3):
    res=tr(S.exp(vv)*(1+z*(vv-1)+z*R.subs(z,z/(1+z*vv)))-(1-z),N-2)
    den=tr(S.exp(vv)*(1+z*vv+z*(R.subs(z,z/(1+z*vv))- (z/(1+z*vv))**2*S.diff(R,z).subs(z,z/(1+z*vv)))),N-2)
    vv=tr(vv-res/den,N-2)
    print('inverse log ratio',i,S.collect(vv,z),flush=True)
print('inverse n ratio',S.collect(tr(S.exp(2*vv),N-2),z),flush=True)
open(Path(__file__).resolve().parent.parent / 'data' / 'symbolic.txt','w').write('\n'.join([f'h={h}',f'B={B}',f'G={Gell}',f'logNratio={vv}',f'nratio={tr(S.exp(2*vv),N-2)}']))

expected_G=(1/z-1+P*z/6+P*z**2/6+(P/6-P**2/72)*z**3
    +(P/6+P**2/40)*z**4+(P/6+41*P**2/180+P**3/432)*z**5)
expected_inverse=(1-P*z**2/3-P*z**3/3+(P**2/9-P/3)*z**4
    +(P**2/30-P/3)*z**5)
assert S.expand(Gell-expected_G)==0
assert S.expand(tr(S.exp(2*vv),N-2)-expected_inverse)==0
print('All displayed forward and inverse coefficients verified exactly.')
