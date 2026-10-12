"""Finite exact identities and independent Fourier diagnostics for matched jets.

These checks do not prove the uniform analytic remainder. That proof is in
chapters/01-joint-coefficients.tex. Floating-point quadrature is non-interval.
"""
from pathlib import Path
import json
import mpmath as mp
import sympy as sp
from sympy.functions.combinatorial.numbers import stirling

x,q,e,z,t,w,Z,A=sp.symbols('x q e z t w Z A')
degree=5
h=sum((e*x)**j*z**(j+1)/sp.factorial(j+1) for j in range(degree))
exponent=-x*q*t*t*h/2
poly=sp.Poly(sp.series(sp.exp(exponent),x,0,degree+1).removeO(),x)
exact=[]
for r in [3,4,5,6]:
    for j in range(degree+1):
        direct=sp.expand(t**r*poly.nth(j))
        predicted=t**r if j==0 else sum(stirling(j,k,kind=2)*(-q/2)**k*e**(j-k)*z**j*t**(2*k+r)
                    for k in range(1,j+1))/sp.factorial(j)
        assert sp.expand(direct-predicted)==0
        exact.append(dict(derivative=r,log_degree=j,passed=True))

theta=sp.symbols('theta'); denom=A*(1+2*Z+3*Z**2)
G0=(w+w**2+w**3)/denom
G1=G0+theta*((w-Z)**3+Z**3)/denom
jet=[sp.simplify(sp.diff(G1-G0,w,j).subs(w,Z)) for j in range(4)]
assert jet==[theta*Z**3/denom,0,0,6*theta/denom]
assert sp.simplify(sp.diff(G1,w).subs(w,Z)-1/A)==0
assert sp.simplify(G1.subs(w,0))==0
central=2**(2+x/2)*(-2-x/2)*(-1-x/2)*(-x/2)/sp.gamma(1-x/2)
assert sp.diff(central,x).subs(x,0)==-4
controls=[sp.expand(t**3*poly.nth(1)-q*t**5*z/2)!=0,
          sp.expand(t**3*poly.nth(1)+q*t**2*z/2)!=0,
          sp.expand(poly.nth(2)-(-q*t*t*e*z*z/2+q*q*t**4*z*z/4))!=0,
          sp.expand(poly.nth(2)-(-q*t*t*z*z/4+q*q*t**4*z*z/8))!=0]
assert all(controls)

mp.mp.dps=75
fourier=[]
for xi in [-1,0,1]:
    for order,jet_order in [(3,0),(5,1),(7,2)]:
        f=lambda a: mp.exp(-mp.mpf(xi)**2/4)*mp.pcfd(a,-xi)/mp.sqrt(2*mp.pi)
        cylinder=mp.diff(f,order,jet_order)
        def integrand(y):
            if not y: return mp.mpf(0)
            log=mp.log(y)-1j*mp.pi/2
            return mp.re(mp.exp(-1j*xi*y-y*y/2+order*log)*log**jet_order)/mp.pi
        quad=mp.quad(integrand,[0,mp.mpf('.2'),1,3,10,mp.inf])
        error=abs(quad-cylinder)
        assert error<mp.mpf('1e-60')
        fourier.append(dict(xi=xi,order=order,order_derivative=jet_order,
                            absolute_difference=mp.nstr(error,12),passed=True))
out=dict(passed=True,exact_transport_identities=exact,matched_cubic_jet=[str(v) for v in jet],
         central_H5_order_derivative=-4,corruption_controls_detected=controls,
         fourier_dps=75,fourier_comparisons=fourier,
         scope='Finite exact symbolic identities and non-interval Fourier diagnostics; analytic uniformity is proved in the manuscript.')
Path(__file__).with_name('matched-endpoint-identities.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
print('PASS: 24 exact transport identities, cubic endpoint identities, four corruption controls, nine independent Fourier comparisons.')
