#!/usr/bin/env python3
"""Independent finite-primitive and exponential-generator diagnostics."""
from pathlib import Path
import json
import mpmath as mp
from identity_moments_verify import moment,numeric,oriented

mp.mp.dps=95
OUT=Path(__file__).resolve().parents[1]/'results'/'identity_generator_checks.json'

def g(a,b,u):
    if not u: return mp.mpf('0')
    return mp.coth(u/2)/2*mp.fsum(mp.zeta(b-2*j)*u**(2*j)/mp.factorial(2*j) for j in range(1,b//2+1))

def low(a,b,t):
    return mp.fsum(numeric(oriented(a,b,d))*t**d/mp.factorial(d) for d in range(1,a,2))

def A_integral(a,b,t):
    return low(a,b,t)+t**a/mp.factorial(a-1)*mp.quad(lambda v:(1-v)**(a-1)*g(a,b,t*v),[0,1])

def L(k,t):
    return mp.factorial(k)*mp.zeta(k+1)-mp.fsum(mp.factorial(k)/mp.factorial(k-h)*t**(k-h)*mp.polylog(h+1,mp.exp(-t)) for h in range(k+1))

def R(a,m,t):
    return t**(a+m)/(2*mp.factorial(a+m))+mp.fsum((-1)**r*mp.binomial(a-1,r)*t**(a-1-r)*L(m+r,t) for r in range(a))/(mp.factorial(m)*mp.factorial(a-1))

def A_polylog(a,b,t):
    return low(a,b,t)+mp.fsum(mp.zeta(b-2*j)*R(a,2*j,t) for j in range(1,b//2+1))

def main():
    tolerance=mp.mpf('1e-80')
    coefficient_count=65
    checks=[]
    for a,b,t in ((2,2,mp.mpf('.4')),(2,4,mp.mpf('1.3')),(4,6,mp.mpc('.5','.4'))):
        v1=(A_integral(a,b,t)+A_integral(b,a,t))/(2*mp.sinh(t/2))
        v2=(A_polylog(a,b,t)+A_polylog(b,a,t))/(2*mp.sinh(t/2))
        v3=mp.fsum(numeric(moment(a,b,M))*t**(2*M)/mp.factorial(2*M) for M in range(coefficient_count))
        errors=(abs(v1-v2),abs(v3-v1))
        checks.append({'a':a,'b':b,'t':str(t),'anchor_integral_vs_polylog':mp.nstr(errors[0],8),
                       'moment_series_M0_to64_vs_integral':mp.nstr(errors[1],8),'value':mp.nstr(v1,60),
                       'passed':all(error<=tolerance for error in errors)})
    o={'decimal_precision':mp.mp.dps,
       'method':'Anchored quadrature vs explicit polylog primitive vs 65 moment coefficients computed by the exact rational formula. These coefficients are numerical series input, not 65 additional exact identity assertions. Observed floating-point agreement, no interval enclosure.',
       'taylor_coefficients_used':coefficient_count,'numerical_case_count':len(checks),
       'absolute_tolerance':mp.nstr(tolerance,5),'checks':checks}
    OUT.write_text(json.dumps(o,indent=2)+'\n')
    assert all(q['passed'] for q in checks), 'A generator diagnostic exceeded the declared tolerance'
    print(json.dumps(o,indent=2))

if __name__=='__main__': main()
