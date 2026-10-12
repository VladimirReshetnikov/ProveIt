#!/usr/bin/env python3
"""Independent quadrature checks of Gamma moment determinants.
Numerical diagnostics only; no proof is inferred from decimal agreement.
"""
import json
import time
from pathlib import Path
import mpmath as mp
mp.mp.dps = 42
OUT = (Path(__file__).resolve().parent.parent / 'evidence' / 'gamma_normalization_checks.json')
rows=[]

def integral(f):
    return mp.quad(f,[0,mp.mpf("0.25"),1,3,7,15,mp.inf])

def add(label,lhs,rhs):
    err=abs(lhs-rhs)/max(1,abs(rhs))
    row={"label":label,"lhs":mp.nstr(lhs,42),"rhs":mp.nstr(rhs,42),"relative_error":mp.nstr(err,8)}
    rows.append(row)
    print(json.dumps(row),flush=True)
    assert err < mp.mpf("1e-30"),row
    OUT.write_text(json.dumps({"working_dps":mp.mp.dps,"checks":rows},indent=2)+"\n")

def moments(pars,n):
    def weight(x):
        return mp.fprod(mp.gamma(a+mp.j*x/2)*mp.gamma(a-mp.j*x/2) for a in pars)
    return mp.matrix([[integral(lambda x:x**(2*r-1)*mp.sinh(mp.pi*k*x)*weight(x)) for k in range(1,n+1)] for r in range(1,n+1)])

def rhs(pars,n):
    return 2**(2*n*n)*mp.pi**(n*(n+1))*mp.fprod(mp.gamma(pars[i]+pars[j]) for i in range(len(pars)) for j in range(i+1,len(pars)))/mp.gamma(sum(pars))

for n in (1,2,3):
    pars=[mp.mpf(1)/4]*(2*n+2)
    add("ascending_equal_quarter_n_"+str(n),mp.det(moments(pars,n)),rhs(pars,n))

for pars,n,label in [([mp.mpf('0.2'),mp.mpf('0.3'),mp.mpf('0.4'),mp.mpf('0.7')],1,"unequal_real_n1"),([mp.mpf('0.2')+mp.j/9,mp.mpf('0.3'),mp.mpf('0.4')-mp.j/12,mp.mpf('0.7')],1,"unequal_complex_n1"),([mp.mpf('0.16'),mp.mpf('0.23'),mp.mpf('0.35'),mp.mpf('0.45'),mp.mpf('0.6'),mp.mpf('0.7')],2,"unequal_real_n2")]:
    add(label,mp.det(moments(pars,n)),rhs(pars,n))

for m in (1,2,3):
    def W(x): return abs(mp.gamma(mp.mpf(1)/4+mp.j*x/2))**(4*m)
    def P(x,j): return mp.sinh(mp.pi*(m-j)*x) if j<m else mp.tanh(mp.pi*x)
    T=mp.matrix([[4/mp.factorial(2*r)*integral(lambda x:mp.im((x+mp.j/2)**(2*r))*P(x,j)*W(x)) for j in range(1,m+1)] for r in range(1,m+1)])
    K=2**(2*m*m+2)*mp.factorial(m-1)*mp.pi**(mp.mpf(m*(4*m-1))/2)/(mp.gamma(mp.mpf(m)/2)*mp.fprod(mp.factorial(2*r) for r in range(1,m+1)))
    add("full_source_K_"+str(m),(-1)**(m*(m-1)//2)*mp.det(T),K)

u=mp.mpf('0.08')
v=mp.mpf('0.11')
a=mp.mpf(1)/4
pars=[a+u,a-u,a+v,a-v]
add("two_pair_reflection_n1",mp.det(moments(pars,1))/(4*mp.pi**5),1/(mp.cos(mp.pi*(u+v))*mp.cos(mp.pi*(u-v))))

weight=lambda x:x*mp.sinh(mp.pi*x)*abs(mp.gamma(a+mp.j*x/2))**8
add("scalar_trigamma",integral(lambda x:weight(x)*mp.re(mp.polygamma(1,a+mp.j*x/2))),2*mp.pi**7)
add("scalar_third_polygamma_and_square",integral(lambda x:weight(x)*(mp.re(mp.polygamma(3,a+mp.j*x/2))+12*mp.re(mp.polygamma(1,a+mp.j*x/2))**2)),16*mp.pi**9)
add("scalar_digamma",integral(lambda x:weight(x)*mp.re(mp.digamma(a+mp.j*x/2))),-4*mp.pi**5*(mp.euler+3*mp.log(2)))
add("scalar_digamma_square",integral(lambda x:weight(x)*mp.re(mp.digamma(a+mp.j*x/2))**2),4*mp.pi**5*((mp.euler+3*mp.log(2))**2+mp.pi**2/12))
print("All checks passed",flush=True)
