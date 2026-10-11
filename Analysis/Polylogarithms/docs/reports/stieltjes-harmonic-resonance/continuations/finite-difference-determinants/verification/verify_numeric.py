#!/usr/bin/env python3
"""Independent numerical diagnostics, not interval certificates.

Mellin-integral moments are compared against finite endpoint determinants.
Cutoff resonance checks use exact finite boundary formulas, not enumeration
of a huge cutoff. All tolerances and discrepancies are recorded.
"""
from __future__ import annotations
from math import comb, factorial
from pathlib import Path
import json, time
import mpmath as mp
import sympy as sp
ROOT=Path(__file__).resolve().parents[1]
mp.mp.dps=60
start=time.time();rows=[]

def E(r,k,s,a):
 d=2*r-2
 return -mp.fsum((-1)**j*comb(d,j)*mp.fsum(mp.mpf(l-j)**k*(a+l)**(-s)
                  for l in range(j)) for j in range(1,d+1))/factorial(d)
def uv(r,s,a):
 es=[E(r,k,s,a) for k in range(2*r-1)]
 return mp.det(mp.matrix([[es[i+j] for j in range(r)] for i in range(r)])),\
        mp.det(mp.matrix([[es[i+j] for j in range(r-1)] for i in range(r-1)]))
def spectral(r,s,a):
 u,v=uv(r,s,a);return u+v*mp.zeta(s,a)
def finite_moment(r,k,N,s,a):
 d=2*r-2
 h=(mp.digamma(N+a+1)-mp.digamma(a)) if s==1 else mp.zeta(s,a)-mp.zeta(s,N+a+1)
 upper=mp.fsum((-1)**j*comb(d,j)*mp.fsum(mp.mpf(N+l-j)**k*(N+l+a)**(-s)
                 for l in range(1,j+1)) for j in range(1,d+1))/factorial(d)
 return E(r,k,s,a)+(h if k==d else 0)+upper

def finite_partition(r,N,s,a):
 es=[finite_moment(r,k,N,s,a) for k in range(2*r-1)]
 return mp.det(mp.matrix([[es[i+j] for j in range(r)] for i in range(r)]))
def check(name,actual,expected,tol,details=None):
 err=abs(actual-expected);rel=err/max(abs(expected),mp.mpf('1e-42'))
 if rel>tol: raise AssertionError((name,mp.nstr(rel,12),mp.nstr(tol,12),actual,expected))
 print(name, mp.nstr(rel,4), flush=True)
 rows.append({'name':name,'absolute_error':mp.nstr(err,15),'relative_error':mp.nstr(rel,15),
              'relative_tolerance':mp.nstr(tol,8),'details':details or {}})

# Integral numerator: sum n^k q^n = numerator_k(q)/(1-q)^(k+1).
q=sp.symbols('q');g=1/(1-q);polys=[]
for k in range(9):
 polys.append(sp.Poly(sp.cancel(g*(1-q)**(k+1)),q))
 g=sp.cancel(q*sp.diff(g,q))

def mellin_moment(r,k,s,a):
 d=2*r-2
 coeff=[mp.mpf(str(c)) for c in polys[k].all_coeffs()]
 def integrand(t):
  qq=mp.exp(-t);one=-mp.expm1(-t)
  return t**(s-1)*mp.exp(-a*t)*one**(d-k-1)*mp.polyval(coeff,qq)
 return mp.quad(integrand,[0,1,4,12,mp.inf])/(factorial(d)*mp.gamma(s))

for r in (2,3,4):
 for s,a in ((mp.mpf('2.5'),mp.mpf('0.7')),
             (mp.mpc('3.2','0.35'),mp.mpc('1.1','0.2')),
             (mp.mpf(4),mp.mpf('1.5'))):
  vals=[mellin_moment(r,k,s,a) for k in range(2*r-1)]
  integ=mp.det(mp.matrix([[vals[i+j] for j in range(r)] for i in range(r)]))
  check('Mellin determinant',integ,spectral(r,s,a),mp.mpf('1e-38'),
        {'r':r,'s':str(s),'a':str(a),'method':'quadrature of elementary Mellin moment kernels'})

# Independent shift/order polarization for r=2, using independent Mellin moments.
for s,t,a,b in ((mp.mpf('2.4'),mp.mpf('3.1'),mp.mpf('0.8'),mp.mpf('1.3')),
                (mp.mpc('2.7','0.2'),mp.mpf('3.4'),mp.mpc('1.2','0.1'),mp.mpf('0.6'))):
 xs=[mellin_moment(2,k,s,a) for k in range(3)]
 ys=[mellin_moment(2,k,t,b) for k in range(3)]
 actual=(xs[0]*ys[2]+ys[0]*xs[2]-2*xs[1]*ys[1])/2
 xe=[E(2,k,s,a) for k in range(3)];ye=[E(2,k,t,b) for k in range(3)]
 expected=(xe[0]*ye[2]+ye[0]*xe[2]-2*xe[1]*ye[1]+xe[0]*mp.zeta(t,b)+ye[0]*mp.zeta(s,a))/2
 check('Mixed spectral-shift Mellin identity',actual,expected,mp.mpf('1e-38'))

# Direct cutoff moment sums at ordinary convergent integer orders.
for r,m,N in ((2,2,1200),(2,3,500),(3,2,600),(3,3,400)):
 d=2*r-2;a=mp.mpf(1)
 mus=[mp.mpf(0) for _ in range(d+1)]
 for n in range(N+1):
  w=mp.fsum((-1)**j*comb(d,j)/(mp.mpf(n+1+j)**m) for j in range(d+1))/factorial(d)
  for k in range(d+1): mus[k]+=mp.mpf(n)**k*w
 direct=mp.det(mp.matrix([[mus[i+j] for j in range(r)] for i in range(r)]))
 check('Direct finite cutoff versus boundary formula',direct,finite_partition(r,N,mp.mpf(m),a),mp.mpf('1e-42'),
       {'r':r,'m':m,'N':N,'not_an_infinite_sum_comparison':True})

# Resonant hard cutoff. Extra precision protects the upper-boundary cancellations.
with mp.workdps(150):
 for r,a in ((2,mp.mpf(1)),(2,mp.mpf('1.5')),(3,mp.mpf(1)),(4,mp.mpf(1))):
  d=2*r-2;N=10**20;U,V=uv(r,mp.mpf(1),a)
  actual=finite_partition(r,N,mp.mpf(1),a)-V*mp.log(N+a)
  expected=U+V*(-mp.digamma(a)-mp.harmonic(d))
  check('Hard cutoff constant',actual,expected,mp.mpf('1e-17'),{'r':r,'a':str(a),'N':str(N)})

# All-jet coefficient formula against differentiated large-cutoff brackets for r=2.
# Derivatives are local complex derivatives of a holomorphic finite expression.
with mp.workdps(100):
 for a in (mp.mpf(1),mp.mpf('1.5')):
  r=2;d=2;N=10**18
  def U(s):return -a**(-2*s)/2+(a*(a+1))**(-s)/4
  def V(s):return (a**(-s)-(a+1)**(-s))/2
  def c(s):return s*(s+1)/2
  def B(s):return (1-c(s))*V(s)
  def finiteT(s):
   h=mp.digamma(N+a+1)-mp.digamma(a) if s==1 else mp.zeta(s,a)-mp.zeta(s,N+a+1)
   return finite_partition(2,N,s,a)-c(s)*V(s)*h
  for k in range(4 if a==1 else 2):
   # step method with 140 digits is sufficient for k<=3 and boundary cancellation.
   actual=mp.diff(finiteT,mp.mpf(1),k,addprec=40)
   expected=mp.diff(U,1,k)+mp.diff(B,1,k+1)/(k+1)
   expected+=mp.fsum(comb(k,j)*mp.diff(B,1,j)*(-1)**(k-j)*(mp.stieltjes(k-j) if a==1 else mp.euler+2*mp.log(2)-2) for j in range(1,k+1))
   check('Ordinary Stieltjes bracket derivative',actual,expected,mp.mpf('1e-12'),
         {'r':2,'a':str(a),'k':k,'N':str(N),'finite_cutoff_diagnostic':True})

# The explicit polylog generator, independent direct finite-cutoff determinants.
for z in (mp.mpf('0.25'),mp.mpf('0.65'),mp.mpc('0.3','0.2')):
 P=lambda M: -mp.mpf(7)/16-mp.mpf(3)/(4*(M+2))+mp.mpf(7)/(4*(M+2)**2)+mp.mpf(7)/(8*(M+1)**2)-mp.mpf(1)/(2*(M+1)**4)
 Q=lambda M:mp.mpf(3)/8-mp.mpf(1)/(2*(M+1)**2)+mp.mpf(1)/(2*(M+2)**2)
 hm=mp.mpf(0);direct=mp.mpf(0);li22=mp.mpf(0)
 for M in range(1,700):
  li22+=z**M*hm/M**2;hm+=mp.mpf(1)/M**2
  direct+=z**M*(P(M)+Q(M)*hm)
 expected=(1-z)/(2*z*z)*li22+(10-7*z)/(8*z*z*(1-z))*mp.polylog(2,z)+(4*z-7)/(4*z*z)*mp.polylog(1,z)-mp.polylog(4,z)/(2*z)+1/(2*z)-mp.mpf(7)/(16*(1-z))
 check('Depth-two cutoff generator',direct,expected,mp.mpf('1e-42'),{'z':str(z),'terms':699})

# Anchored gamma primitive (the m=0 Stieltjes case).
a0=mp.mpf('0.8');a1=mp.mpf('1.4')
actual=mp.quad(lambda x:-mp.digamma(x),[a0,1,a1])
expected=-mp.loggamma(a1)+mp.loggamma(a0)
check('Anchored Gamma primitive',actual,expected,mp.mpf('1e-45'),{'m':0})

out={'status':'passed','working_decimal_digits':60,'extra_digits_for_cutoffs':150,
     'diagnostics':len(rows),'rows':rows,'elapsed_seconds':round(time.time()-start,3),
     'not_interval_certified':True,'not_a_proof_of_infinite_families':True}
(ROOT/'results/numerical_checks.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({'status':out['status'],'diagnostics':len(rows),'elapsed_seconds':out['elapsed_seconds'],
     'max_relative_error':max(float(x['relative_error']) for x in rows)},indent=2))
