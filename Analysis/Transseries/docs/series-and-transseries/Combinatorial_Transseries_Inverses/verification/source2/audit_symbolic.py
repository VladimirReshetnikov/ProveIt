#!/usr/bin/env python3
"""Additional independent checks of displayed formulas and exact moment models.

This script complements verify.py. It checks formal residuals, several exact
integer identities, numerical integral identities, and a graph remainder using
rational arithmetic. It does not numerically certify all asymptotic theorems.
"""
from __future__ import annotations
from fractions import Fraction
from math import comb, factorial
from pathlib import Path
import sympy as sp
import mpmath as mp
from verify import (endpoint_coefficients, log_coefficients, connected_graphs,
                    reciprocal_graph_coeffs)

mp.mp.dps=100
out=[]
t,ell=sp.symbols('t ell', nonzero=True)
z0=-2/ell
z1=2/ell**2-2/ell**3
z2=-sp.Rational(7,12)/ell-1/ell**3+sp.Rational(14,3)/ell**4-4/ell**5
z=z0+z1*t+z2*t*t
phase=ell*z/2+((1+t*z)*sp.log(1+t*z)-t*z)/(2*t)+sp.sqrt(1+t*z)+sp.Rational(7,24)*t*t/sp.sqrt(1+t*z)
assert sp.simplify(sp.series(phase,t,0,3).removeO())==0
out.append('Involution inverse phase cancels exactly through t^2.')
a=endpoint_coefficients('motzkin_plus',3)
assert log_coefficients(a,2)==[-sp.Rational(39,16),sp.Rational(143,64)]
out.append('Motzkin logarithmic coefficients: -39/16, 143/64.')

# The polynomial gamma continuation agrees with the unsigned Stirling values.
x,z=sp.symbols('x z')
for n in range(1,9):
    polynomial=sp.prod(z+j for j in range(n)).expand()
    # Recompute unsigned Stirling values by the cycle insertion rule.
    row=[1]
    for m in range(1,n+1):
        row=[0]+[ (row[k-1] if k-1<len(row) else 0) +
                  (m-1)*(row[k] if k<len(row) else 0)
                  for k in range(1,m+1)]
    assert all(polynomial.coeff(z,k)==row[k] for k in range(n+1))
out.append('Unsigned Stirling gamma-polynomial identity: n=1,...,8.')

# Exact numerical moment identities. Split at a midpoint when a density has
# square-root endpoint singularities. No coefficient expansion is used here.
A=3-2*mp.sqrt(2); B=3+2*mp.sqrt(2)
for n in range(6):
    mot=sum(comb(n,2*j)*comb(2*j,j)//(j+1) for j in range(n//2+1))
    mi=mp.quad(lambda u: (1+2*mp.cos(u))**n*2*mp.sin(u)**2/mp.pi,[0,mp.pi/2,mp.pi])
    assert abs(mi-mot)<mp.mpf('1e-85')
    de=sum(comb(n,j)*comb(n+j,j) for j in range(n+1))
    di=mp.quad(lambda u: (3+2*mp.sqrt(2)*mp.cos(u))**n/mp.pi,[0,mp.pi/2,mp.pi])
    assert abs(di-de)<mp.mpf('1e-85')
# Schroder recurrence from S=1+zS+zS^2.
sch=[1]
for n in range(1,6):
    sch.append(sch[n-1]+sum(sch[j]*sch[n-1-j] for j in range(n)))
for n in range(6):
    si=mp.quad(lambda u: (3+2*mp.sqrt(2)*mp.cos(u))**(n-1)*4*mp.sin(u)**2/mp.pi,
               [0,mp.pi/2,mp.pi])
    assert abs(si-sch[n])<mp.mpf('1e-85')
out.append('Motzkin, Delannoy, and Schroder exact moments: n=0,...,5, error < 1e-85.')

# The two Gaussian integrals, with integer powers, reconstruct I_n.
for n in range(6):
    ip=sum(factorial(n)//(2**j*factorial(j)*factorial(n-2*j)) for j in range(n//2+1))
    ap=mp.quad(lambda u:u**n*mp.exp(-(u-1)**2/2)/mp.sqrt(2*mp.pi),[0,1,4,mp.inf])
    am=mp.quad(lambda u:u**n*mp.exp(-(u+1)**2/2)/mp.sqrt(2*mp.pi),[0,1,4,mp.inf])
    assert abs(ap+(-1)**n*am-ip)<mp.mpf('1e-85')
out.append('Involution two-integral identity: n=0,...,5, error < 1e-85.')

# Check the first coefficient for generalized harmonic inversion symbolically.
s=sp.symbols('s',positive=True)
D1=-(s-1)*s/sp.Integer(24)
h1=-(-1/(s-1))*D1
assert sp.simplify(h1+s/24)==0
out.append('Generalized harmonic inverse coefficient h_{s,1}=-s/24.')

# Exact graph remainder ratios, avoiding loss of tiny sectors to rounding.
cg=connected_graphs(80)
b=reciprocal_graph_coeffs(5)
for K in [2,4]:
    ratios=[]
    for n in [20,40,80]:
        normalized=Fraction(cg[n],2**(n*(n-1)//2))
        approx=sum((Fraction(comb(n,k)*b[k]*2**(k*(k+1)//2),2**(k*n)) for k in range(K+1)),Fraction(0))
        scale=Fraction(n**(K+1),2**((K+1)*n))
        val=(normalized-approx)/scale
        ratios.append((n,mp.nstr(mp.mpf(val.numerator)/val.denominator,12)))
    out.append(f'Graph relative remainder / (n^(K+1) 2^(-(K+1)n)), K={K}: {ratios}')

out.append('All additional assertions passed.')
text='\n'.join(out)+'\n'
Path(__file__).with_name('symbolic_audit_report.txt').write_text(text)
print(text)
