#!/usr/bin/env python3
"""Independent numerical diagnostics for the analytic moment theorems.

These checks are not claimed as proofs or interval certificates. For the
separate exact cubic enclosure run certify_cubic.py.
"""
import json
import math
from pathlib import Path
import mpmath as mp
import numpy as np

mp.mp.dps=180
tau=mp.findroot(lambda t:-t*mp.digamma(1-t)-1,(mp.mpf('.45'),mp.mpf('.55')))
rho=tau/mp.gamma(1-tau)
alpha=-mp.log(rho)
v=1+tau*tau*mp.polygamma(1,1-tau)
C=tau/mp.sqrt(2*mp.pi*v)
k3=1+3*tau**2*mp.polygamma(1,1-tau)-tau**3*mp.polygamma(2,1-tau)
k4=1+7*tau**2*mp.polygamma(1,1-tau)-6*tau**3*mp.polygamma(2,1-tau)+tau**4*mp.polygamma(3,1-tau)
beta1=-1/(2*v)+k3/(2*v**2)+k4/(8*v**2)-5*k3**2/(24*v**3)

def coeff(k):
    b=[mp.euler]+[mp.zeta(j) for j in range(2,k)]
    a=[mp.mpf(1)]
    for m in range(1,k):
        a.append(k*mp.fsum(b[j-1]*a[m-j] for j in range(1,m+1))/m)
    return a[-1]/k

ck={k:coeff(k) for k in range(1,65)}
coefficient_rows=[]
for k in [10,30,100,300]:
    c=ck[k] if k in ck else coeff(k)
    leading=C*rho**(-k)/mp.mpf(k)**mp.mpf('1.5')
    coefficient_rows.append({'k':k,'c_k':mp.nstr(c,60),
        'ratio_to_leading':mp.nstr(c/leading,40),
        'ratio_to_first_correction':mp.nstr(c/(leading*(1+beta1/k)),40)})

moment_rows=[]
for n in [8,20,40,80]:
    K=int(mp.floor(n/alpha-mp.sqrt(n)))
    partial=mp.fsum((-1)**(k-1)*ck[k]/mp.mpf(k)**n for k in range(1,K+1))
    # x=exp(-t) removes the singular endpoint.  Integration is split around
    # the Gamma(n+1,1) density's peak, independent of inverse-Gamma coefficients.
    def integrand(t):
        if mp.isinf(t): return mp.mpf(0)
        lg=t+mp.loggamma(1+mp.exp(-t))
        return mp.exp(-t)*lg**n/mp.factorial(n)
    breaks=sorted(set([mp.mpf(0),mp.mpf(1),alpha,mp.mpf(n)/4,
                       mp.mpf(n)/2,mp.mpf(n),mp.mpf(3*n)/2,mp.mpf(2*n)]))
    value=mp.quad(integrand,breaks+[mp.inf])
    actual=abs(value-partial)
    bound=(1/mp.sqrt(2*mp.pi*n)+tau/(alpha*mp.sqrt(2*mp.pi))+tau*mp.exp(2*alpha**2))*(mp.e*alpha/n)**n
    sharper=alpha**n/mp.factorial(n)*(1+n*tau/(n-K*alpha))
    sharper+=tau*rho**(-K-1)/(K+1)**n*mp.gammainc(n,(K+1)*alpha,mp.inf)/mp.gamma(n)
    assert actual<sharper<bound
    moment_rows.append({'n':n,'K':K,'normalized_moment':mp.nstr(value,150),
        'observed_absolute_remainder':mp.nstr(actual,40),
        'incomplete_gamma_bound':mp.nstr(sharper,40),
        'simple_bound':mp.nstr(bound,40)})

M3=mp.quad(lambda x:mp.loggamma(x)**3,[0,mp.mpf('.5'),1])
cert=json.loads(Path(__file__).with_name('cubic_certificate.json').read_text())
assert mp.mpf(cert['lower'])<M3<mp.mpf(cert['upper'])
L=mp.log(2*mp.pi); A=mp.euler+L
z2p=mp.diff(mp.zeta,2); z2pp=mp.diff(mp.zeta,2,2)
base=L**3/8+mp.pi**2*L/32+3*mp.zeta(3)/16+3*L/(4*mp.pi**2)*(A*A*mp.zeta(2)-2*A*z2p+z2pp)
R_from_moment=(M3-base)*8*mp.pi**2/3
N=5000
logs=np.log(np.arange(1,N+1,dtype=np.float64))
parts=[]
for q in range(2,N+1):
    m=np.arange(1,q,dtype=np.float64)
    numerator=(float(A)+logs[q-1])**2-(logs[q-1]-logs[:q-1])*(logs[q-1]-logs[q-2::-1])
    parts.append(float(np.sum(numerator/(m*(q-m)*q))))
R_N=math.fsum(parts)
u=mp.log(N)
P=(1+u)*(A+u)**2
P1=(A+u)**2+2*(1+u)*(A+u)
P2=4*(A+u)+2*(1+u)
P3=6
R_tail=2/mp.mpf(N)*(P+P1+P2+P3)
assert R_N<float(R_from_moment)<R_N+float(R_tail)
result={
 'status':'Numerical diagnostics; theorem proof and cubic rational certificate are separate',
 'mpmath_decimal_precision':mp.mp.dps,
 'constants':{name:mp.nstr(value,80) for name,value in [('tau',tau),('rho',rho),('alpha',alpha),('v',v),('C',C),('beta1',beta1)]},
 'coefficient_rows':coefficient_rows,'moment_rows':moment_rows,
 'cubic':{'independent_quadrature':mp.nstr(M3,150),'inside_certified_interval':True,
          'Tornheim_operator_from_cubic':mp.nstr(R_from_moment,80),
          'triangular_N':N,'triangular_float_sum':R_N,'proved_analytic_tail_upper':mp.nstr(R_tail,60),
          'diagnostic_bracket_passed':True}
}
Path(__file__).with_name('moment_diagnostics.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
