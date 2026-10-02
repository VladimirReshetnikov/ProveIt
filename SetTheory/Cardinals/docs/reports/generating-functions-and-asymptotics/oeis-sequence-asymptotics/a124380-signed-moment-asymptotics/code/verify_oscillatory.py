#!/usr/bin/env python3
"""Independent symbolic and quadrature checks of the smaller signed sector.
All displayed errors are amplitude-scaled, not divided by the sine.
The quadrature interval has its Gaussian tails truncated 20 units from the
saddle; this is a diagnostic, not an interval-arithmetic certificate.
"""
import json
import sympy as s
import mpmath as mp
from replay_oscillatory import coefficients
from replay_coefficients import coefficients as plus_coefficients
L,y,p,phase,q=coefficients(4)
LL,_,qp,_=plus_coefficients(4)
for j in range(5):
    assert s.expand(q[j]-(-1)**j*qp[j].subs(LL,L-s.I*p))==0
print('PASS all-order complex-shift relation checked exactly through order 4')
h=s.symbols('h');t=1/h+y
logt=L+s.series(s.log(1+h*y),h,0,7).removeO()
rho=(2/h**2-t+s.Rational(1,2))*logt-t*t-t+s.Rational(1,12)/t-s.Rational(1,360)/t**3+s.Rational(1,1260)/t**5
E=s.series(rho-((2*L-1)/h**2-(L+1)/h+L/2),h,0,5).removeO().expand()
assert s.expand(E.coeff(h,0)-(-2*y*y-(L+2)*y))==0
for j in range(1,5):assert s.expand(E.coeff(h,j)-phase[j])==0
print('PASS independent direct negative-sector Stirling expansion through order 4')
mp.mp.dps=65
qf=[s.lambdify((L,p),z,'mpmath') for z in q]
for n in [50,100,200,500,1000,5000,10000]:
    x=mp.sqrt(mp.mpf(n)/2);ell=mp.log(x)
    psi=lambda t:(n-2*t+1)*mp.log(t)-t*t+mp.loggamma(t)
    dp=lambda t:(n+1)/t-2*mp.log(t)-2-2*t+mp.digamma(t)
    sigma=mp.findroot(dp,(x*.8,x))
    lo=max(mp.mpf(0),sigma-20);hi=sigma+20
    pts=[lo]+[sigma+k for k in range(-19,20) if lo<sigma+k<hi]+[hi]
    integral=mp.quad(lambda t:mp.exp(psi(t)-psi(sigma))*mp.sin(mp.pi*t)/mp.pi if t>0 else mp.mpf(0),pts)
    logM=mp.mpf('.5')-mp.pi**2/8+ell+x*x*(2*ell-1)-x*(ell+1)+ell*ell/8
    exact=integral*mp.exp(psi(sigma)-logM)
    theta=mp.pi*x-mp.pi*(ell+2)/4
    series=mp.mpc(0);errs=[]
    for j in range(5):
        series+=qf[j](ell,mp.pi)/x**j
        errs.append(exact-mp.im(mp.exp(mp.j*theta)*series))
    print(json.dumps({'n':n,'J_over_Mminus':mp.nstr(exact,14),'errors_R0_to_R4':[mp.nstr(z,12) for z in errs]}),flush=True)
print('All symbolic checks passed. Quadrature values are non-certified diagnostics.')
