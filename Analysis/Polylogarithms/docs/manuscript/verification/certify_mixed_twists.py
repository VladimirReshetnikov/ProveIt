"""Independent exact partial fractions and separate mixed-twist diagnostics."""
from pathlib import Path
import json,sympy as s,mpmath as mp
V=Path(__file__).resolve().parent
x,h=s.symbols('x h',nonzero=True);checks=0
for r in range(1,9):
 for t in range(1,9):
  rhs=sum((-1)**(r-j)*s.binomial(r+t-j-1,r-j)/h**(r+t-j)/x**j for j in range(1,r+1))+sum((-1)**r*s.binomial(r+t-k-1,t-k)/h**(r+t-k)/(x+h)**k for k in range(1,t+1))
  assert s.cancel(rhs-1/(x**r*(x+h)**t))==0
  checks+=1
assert s.cancel(1/(h*x)-1/(h*(x+h))-1/(x*(x+h)))==0
assert s.cancel(1/(h*x)+1/(h*(x+h))-1/(x*(x+h)))!=0
mp.mp.dps=60;rows=[]
for theta,phi in [(mp.mpf('0.25'),mp.mpf('0.5')),(mp.mpf('0.37'),mp.mpf('0.72'))]:
 for a,b in [(mp.mpf('1.5'),mp.mpf('1.25')),(mp.mpc('1.25','0.2'),mp.mpc('1.75','-0.15'))]:
  for n in [-3,-1,0,2]:
   A=2*mp.pi*1j*(n+theta);B=2*mp.pi*1j*(n+phi)
   value=mp.quad(lambda u:u**(a-1)*(1-u)**(b-1)*(u*A+(1-u)*B)**(-a-b),[0,mp.mpf('.5'),1])/mp.beta(a,b)
   target=A**(-a)*B**(-b);err=abs(value-target)
   assert err<mp.mpf('1e-50')
   rows.append(dict(kind='fractional-beta-mixture',theta=str(theta),phi=str(phi),mode=n,alpha=str(a),beta=str(b),absolute_residual=mp.nstr(err,14)))
 for z in [mp.mpf('.23'),mp.mpf('.5'),mp.mpf('.81')]:
  def k(t,u):return mp.exp(-2*mp.pi*1j*t*u)/(1-mp.exp(-2*mp.pi*1j*t))
  value=mp.quad(lambda y:k(theta,y)*k(phi,z-y),[0,z])+mp.quad(lambda y:k(theta,y)*k(phi,1+z-y),[z,1])
  target=(k(theta,z)-k(phi,z))/(2*mp.pi*1j*(phi-theta));err=abs(value-target)
  assert err<mp.mpf('1e-50')
  rows.append(dict(kind='ordinary-wrapped-convolution',theta=str(theta),phi=str(phi),argument=str(z),absolute_residual=mp.nstr(err,14)))
# Integer orders also allow twists in different frequency intervals.
theta=mp.mpf('-0.25');phi=mp.mpf('1.5')
for z in [mp.mpf('.23'),mp.mpf('.5'),mp.mpf('.81')]:
 value=mp.quad(lambda y:k(theta,y)*k(phi,z-y),[0,z])+mp.quad(lambda y:k(theta,y)*k(phi,1+z-y),[z,1])
 target=(k(theta,z)-k(phi,z))/(2*mp.pi*1j*(phi-theta));err=abs(value-target)
 assert err<mp.mpf('1e-50')
 rows.append(dict(kind='ordinary-wrapped-convolution',theta=str(theta),phi=str(phi),argument=str(z),absolute_residual=mp.nstr(err,14)))
result=dict(status='PASS',exact_partial_fraction_checks=checks,corruption_controls=1,numerical_diagnostics=dict(working_decimal_digits=60,interval_certified=False,cases=rows),scope='Finite exact rational identities, scalar Fourier beta integrals including zero and negative modes, and independent wrapped ordinary convolutions. General identities are proved analytically.')
(V/'mixed-twist-results.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
print('PASS',checks,'exact partial fractions and',len(rows),'non-interval diagnostics.')
