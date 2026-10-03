#!/usr/bin/env python3
"""Test the exact finite-contour identity/bound and inverse without phase generation."""
import json, math
from pathlib import Path
import mpmath as mp
mp.mp.dps=90
P=Path(__file__).parent
r=json.loads((P/'numerical_results.json').read_text())
C=mp.mpf(r['constants']['C']); D=mp.mpf(r['constants']['D'])
co=list(map(mp.mpf,r['coefficients']))
def integer_value(m,n):
    row=[1]
    for j in range(1,m+1):
        row=[0]+[k*((row[k] if k<len(row) else 0)+row[k-1]) for k in range(1,j+1)]
    return sum(v*k**n for k,v in enumerate(row))
def saddle(lam):
    def X(y): return mp.log1p(mp.exp(-y))
    y=mp.findroot(lambda y:y/(1+mp.exp(y))/X(y)-1/lam,(mp.mpf('0.1')/lam,2/lam),solver='bisect',maxsteps=400)
    return X(y),y
cont=[]
for m,n,Tmult in [(1,1,9),(2,3,5),(3,2,5),(10,10,1),(20,20,1),(40,40,1),(10,20,1),(20,10,1),(30,20,1)]:
    x,y=saddle(mp.mpf(m)/n); T=Tmult*mp.pi
    scale=x**(-m)*y**(-n)
    def fun(t):
        z=y+1j*t
        return (mp.log(1+mp.exp(-z))/x)**(-m)*(z/y)**(-n-2)
    # Integrate conjugate pairs; scale before evaluating.
    cuts=[mp.mpf(0)]+[min(k*mp.pi/4,T) for k in range(1,4*Tmult+1)]
    trunc=mp.mpf(n+1)/m/(mp.pi*y**2)*mp.re(mp.quad(fun,cuts))
    true=mp.mpf(integer_value(m,n))/mp.factorial(m)/mp.factorial(n)/scale
    bound=(y/mp.sqrt(y*y+T*T))**n/(mp.pi*m*T)
    err=abs(trunc-true)
    assert err<=bound*(1+mp.mpf('1e-60'))
    cont.append({'m':m,'n':n,'T_over_pi':Tmult,'normalized_true':str(true),'normalized_contour_error':str(err),'normalized_certified_bound':str(bound),'error_over_bound':str(err/bound)})
inv=[]
for n in [10,20,40,80,160,320,640,800]:
    L=mp.log(integer_value(n,n)); w=mp.lambertw(L*mp.sqrt(D)/(2*mp.e)); start=L/(2*w)
    first=start-(mp.log(start)/2+mp.log(2*mp.pi*C))/(2*(w+1))
    for J in [0,1,2,4,6]:
        def H(v):
            return 2*mp.loggamma(v+1)+v*mp.log(D)-mp.log(v)/2+mp.log(C)+mp.log(mp.fsum(co[j]/v**j for j in range(J+1)))
        v=start; steps=math.ceil(math.log2(J+2))
        for k in range(steps):
            v-=(H(v)-L)/mp.diff(H,v)
        assert abs(v-n)*mp.mpf(n)**(J+1)*mp.log(n) < 10
        inv.append({'n':n,'J':J,'iterations':steps,'initializer_error':str(start-n),'first_formula_scaled_error':str((first-n)*n*mp.log(n)),'inverse_error':str(v-n),'inverse_scaled_error':str((v-n)*mp.mpf(n)**(J+1)*mp.log(n))})
result={'contour_checks':cont,'inverse_checks':inv}
(P/'contour_inverse_results.json').write_text(json.dumps(result,indent=2)+'\n')
print('PASS:',len(cont),'contour identities/tail bounds and',len(inv),'inverse checks')
for row in inv[-5:]:print(row)
