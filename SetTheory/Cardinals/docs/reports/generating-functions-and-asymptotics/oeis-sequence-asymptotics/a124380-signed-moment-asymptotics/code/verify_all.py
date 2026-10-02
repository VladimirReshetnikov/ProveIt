#!/usr/bin/env python3
"""Portable exact-symbolic and high-precision A124380 diagnostics.
Run from any directory. Requires sympy and mpmath. No network calls.
Numeric tests are diagnostics, not proofs or interval certificates.
"""
from pathlib import Path
import contextlib, io, json, runpy
import sympy as s
import mpmath as mp
from replay_coefficients import coefficients
from replay_inverse import inverse_coefficients
root=Path(__file__).resolve().parent
L,phase,q,P=coefficients(4)
with contextlib.redirect_stdout(io.StringIO()):
    independent=runpy.run_path(str(root/'derive_real_laplace.py'))
for j in range(1,5):
    assert s.expand(phase[j]-independent['P'][j-1])==0
    assert s.expand(q[j]-independent['rels'][j])==0
    assert s.expand(P[j]-independent['logs'][j])==0
print('PASS independent direct phase and Gaussian expansion through order 4')
L,c,d,b=inverse_coefficients(4)
# Independent direct composition of the logarithmic asymptotic formula,
# using symbolic h and generic delta coefficients before substitution.
h=s.symbols('h');ds=s.symbols('d0:5')
v=sum(ds[j]*h**(j+1) for j in range(5))
w=s.series(s.log(1+v),h,0,6).removeO()
K=(1+v)**2*(2*L+2*w-1)-(2*L-1)+h*(1+v)*(L+w+1)+h*h*((L+w)**2/8+L+w+c)
for j in range(1,4):
    K+=h**(j+2)*s.series((1+v)**(-j),h,0,6-j-2).removeO()*P[j].subs(L,L+w)
K=s.series(K,h,0,6).removeO().expand()
for j in range(1,6):
    assert s.factor(K.coeff(h,j).subs(dict(zip(ds,d))))==0
for j in range(5):
    assert s.factor(b[j]-(4*d[j]+2*sum(d[i]*d[j-1-i] for i in range(j))))==0
print('PASS independent inverse composition and conversion through b4')
N=1000;older=[1];old=[0,1];values=[1,1]
for n in range(2,N+1):
    row=[0]+[(old[k-1] if k-1<len(old) else 0)+k*(older[k-1] if k-1<len(older) else 0) for k in range(1,n+1)]
    values.append(sum(row));older,old=old,row
assert values[:15]==[1,1,2,4,9,22,57,157,453,1368,4296,13995,47138,163779,585741]
print('PASS exact recurrence and 15 OEIS initial terms')
mp.mp.dps=70
for n in [0,1,2,3,4,5,10]:
    I=mp.quad(lambda t:mp.exp((n+2*t+1)*mp.log(t)-t*t-mp.loggamma(1+t)),[0,1,2,4,8,mp.inf])
    J=mp.quad(lambda t:mp.exp((n-2*t+1)*mp.log(t)-t*t)*mp.rgamma(1-t),[0,1,2,4,8,mp.inf])
    assert abs((I+(-1)**n*J)/values[n]-1)<mp.mpf('1e-60')
print('PASS signed-moment identity to 60 relative digits for n=0,1,2,3,4,5,10')
pf=[s.lambdify(L,pol,'mpmath') for pol in P]
bf=[s.lambdify((L,c),pol,'mpmath') for pol in b]
for n in [50,100,200,500,1000]:
    x=mp.sqrt(mp.mpf(n)/2);ell=mp.log(x)
    exact=mp.log(values[n]); base=x*x*(2*ell-1)+x*(ell+1)+ell*ell/8+ell+mp.mpf('.5')-mp.log(2)
    fe=[];approx=base
    for j in range(5):
        if j:approx+=pf[j](ell)/x**j
        fe.append(exact-approx)
    X=mp.sqrt(exact/mp.lambertw(exact/mp.e));LL=mp.log(X);C=mp.mpf('.5')-mp.log(2)
    inv=2*X*X;ie=[]
    for j in range(5):
        inv+=bf[j](LL,C)*X**(1-j)
        ie.append(n-inv)
    tau=mp.findroot(lambda t:(n+2*t+1)/t+2*mp.log(t)-2*t-mp.digamma(1+t),x+(ell+2)/4)
    phi=lambda t:(n+2*t+1)*mp.log(t)-t*t-mp.loggamma(1+t)
    H=-mp.diff(phi,tau,2);la={j:mp.diff(phi,tau,j) for j in range(3,7)}
    C1=la[4]/(8*H**2)+5*la[3]**2/(24*H**3)
    C2=la[6]/(48*H**3)+7*la[3]*la[5]/(48*H**4)+35*la[4]**2/(384*H**4)+35*la[3]**2*la[4]/(64*H**5)+385*la[3]**4/(1152*H**6)
    saddle=phi(tau)+mp.log(2*mp.pi/H)/2
    se=[mp.expm1(exact-saddle-mp.log(z)) for z in [1,1+C1,1+C1+C2]]
    print(json.dumps({'n':n,'log_errors_R0_to_R4':[mp.nstr(z,12) for z in fe],
          'inverse_errors_b0_to_b4':[mp.nstr(z,12) for z in ie],
          'saddle_relative_errors_R0_to_R2':[mp.nstr(z,12) for z in se]}))
print('All checks passed. All numeric errors above are non-certified diagnostics.')
