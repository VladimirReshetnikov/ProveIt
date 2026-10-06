#!/usr/bin/env python3
"""Finite marked, Newton and boundary diagnostics. Not interval certificates."""
import json
import mpmath as mp
mp.mp.dps=55
checks=[]
def require(ok,label):
    if not ok: raise RuntimeError('CHECK FAILED: '+label)
    checks.append(label)
def text(x): return mp.nstr(x,20)
def h(y): return mp.sqrt(4-y)*mp.rgamma(5-y) if y!=4 else mp.mpf(0)
def r1(x): return x*(x-1)/2

def integral(n):
    n=mp.mpf(n); L=mp.log(n)
    def f(y):
        if y in (0,4): return mp.mpf(0)
        s=4-y
        return mp.exp(-L*y)*mp.sqrt(y)*h(y)*mp.exp(mp.loggamma(n+s)-mp.loggamma(n+1)-(s-1)*L)
    return mp.quad(f,[0,1,2,3,4])

def logG(t,J):
    L=mp.log(t)
    def f(y,derive):
        p=1+r1(4-y)/t if J else mp.mpf(1)
        if derive: p=-y*p-(r1(4-y)/t if J else 0)
        return mp.exp(-L*y)*mp.sqrt(y)*h(y)*p
    S=mp.quad(lambda y:f(y,False),[0,1,2,3,4])
    Sd=mp.quad(lambda y:f(y,True),[0,1,2,3,4])
    return mp.loggamma(t+1)+3*L-mp.log(2*mp.pi)+mp.log(S),mp.digamma(t+1)+3/t+Sd/(t*S)

# A separate derivation of the marked prefactor at u=1 and cumulant derivatives.
require(abs(mp.gamma(mp.mpf('1.5'))/(4*mp.pi*mp.gamma(4))-1/(48*mp.sqrt(mp.pi)))<mp.mpf('1e-50'),'marked leading normalization')
logpref=lambda u:-mp.mpf('1.5')*mp.log(u)-mp.loggamma(4*u)
c1=lambda u:mp.mpf('1.5')*(mp.digamma(4*u)+1/(8*u))
D=lambda f,u:u*mp.diff(f,u)
require(abs(D(logpref,1)+mp.mpf('1.5')+4*mp.digamma(4))<mp.mpf('1e-50'),'mean constant')
require(abs(D(lambda u:D(logpref,u),1)+4*mp.digamma(4)+16*mp.polygamma(1,4))<mp.mpf('1e-50'),'variance constant')
require(abs(D(c1,1)-(6*mp.polygamma(1,4)-mp.mpf(3)/16))<mp.mpf('1e-50'),'mean inverse-log coefficient')
require(abs(D(lambda u:D(c1,u),1)-(6*mp.polygamma(1,4)+24*mp.polygamma(2,4)+mp.mpf(3)/16))<mp.mpf('1e-50'),'variance inverse-log coefficient')
inversion=[]
for n in [256,4096]:
    I=integral(n);L=mp.log(n)
    y=mp.loggamma(n+1)+3*L-mp.log(2*mp.pi)+mp.log(I)
    t0=y/mp.lambertw(y/mp.e)
    require(abs(t0*(mp.log(t0)-1)-y)<mp.mpf('1e-45'),'Lambert identity '+str(n))
    for J in [0,1]:
        ss=[t0]
        for r in range(3):
            v,d=logG(ss[-1],J)
            ss.append(ss[-1]-(v-y)/d)
        residual=logG(ss[-1],J)[0]-y
        require(abs(residual)<mp.mpf('1e-20'),'Newton residual '+str((n,J)))
        inversion.append({'n':n,'J':J,'errors_against_s3':[text(s-ss[-1]) for s in ss[:3]],'s3_minus_n':text(ss[-1]-n),'scaled_inverse_error':text((ss[-1]-n)*mp.mpf(n)**(J+1)*L),'log_residual':text(residual)})
ell=mp.digamma(4)+mp.mpf(1)/8
boundary=[]
for n in [256,4096,65536]:
    L=mp.log(n);norm=integral(n)*L**mp.mpf('1.5')
    def g(t): return mp.sqrt(t)*mp.exp(-t)/mp.gamma(mp.mpf('1.5'))
    def density(t):
        if t<=0 or t>=4*L:return mp.mpf(0)
        s=4-t/L
        gr=mp.exp(mp.loggamma(n+s)-mp.loggamma(n+1)-(s-1)*L)
        return mp.exp(-t)*mp.sqrt(t)*mp.sqrt(s)*mp.rgamma(s+1)*gr/norm
    cuts=[0,mp.mpf('1.5'),4,8,16,4*L]
    cuts=sorted(set(t for t in cuts if t<=4*L))
    mass=mp.quad(density,cuts)
    require(abs(mass-1)<mp.mpf('1e-45'),'boundary mass '+str(n))
    correction=lambda t:g(t)*(1+ell*(t-mp.mpf('1.5'))/L)
    # Locate sign changes before integrating absolute values. This avoids
    # quadrature across a cusp; it remains a noncertified floating diagnostic.
    def absolute_integral(other):
        delta=lambda t:density(t)-other(t)
        points=[4*L*mp.mpf(i)/128 for i in range(1,129)]
        roots=[]
        for left,right in zip(points,points[1:]):
            if delta(left)*delta(right)<0:
                root=mp.findroot(delta,(left,right),solver='bisect',tol=mp.mpf('1e-45'),maxsteps=200)
                roots.append(root)
        split=sorted(set(cuts+roots))
        return sum(abs(mp.quad(delta,[left,right])) for left,right in zip(split,split[1:])),roots
    tail=mp.gammainc(mp.mpf('1.5'),4*L,mp.inf)/mp.gamma(mp.mpf('1.5'))
    leading_integral,leading_roots=absolute_integral(g)
    corrected_integral,corrected_roots=absolute_integral(correction)
    require(len(leading_roots)==2 and len(corrected_roots)==3,'boundary sign-change diagnostic '+str(n))
    zeroth=leading_integral+tail
    first=corrected_integral+mp.quad(lambda t:abs(correction(t)),[4*L,mp.inf])
    require(zeroth>0 and first>0,'positive boundary diagnostic '+str(n))
    boundary.append({'n':n,'mass':text(mass),'leading_L1_error':text(zeroth),'corrected_L1_error':text(first),'scaled_corrected_L1_error':text(first*L*L),'leading_crossings':[text(t) for t in leading_roots],'corrected_crossings':[text(t) for t in corrected_roots]})
require(abs(mp.quad(lambda t:mp.sqrt(t)*mp.exp(-t)*(t-mp.mpf('1.5'))/mp.gamma(mp.mpf('1.5')),[0,1,mp.inf]))<mp.mpf('1e-50'),'centered boundary correction')
print(json.dumps({'status':'PASS','checks':checks,'precision_decimal_digits':mp.mp.dps,'mpmath_version':mp.__version__,'inversion':inversion,'boundary':boundary,'classification':'Noncertified finite diagnostics. No remainder constants, interval digits, onsets, or discrete rounding certified.'},indent=2,sort_keys=True))
