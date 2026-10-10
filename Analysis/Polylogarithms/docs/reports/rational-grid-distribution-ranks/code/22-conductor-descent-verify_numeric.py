#!/usr/bin/env python3
"""Independent high-precision smoke tests. NOT interval certificates or proofs."""
from __future__ import annotations
import json,pathlib,time
from functools import lru_cache
from math import gcd
import mpmath as m
ROOT=pathlib.Path(__file__).resolve().parents[1]
m.mp.dps=45
checks=[]

def record(name,lhs,rhs):
    error=abs(lhs-rhs)
    assert error<m.mpf('1e-38'),(name,lhs,rhs,error)
    checks.append(dict(name=name,lhs=str(lhs),rhs=str(rhs),absolute_error=str(error),
                       working_decimal_digits=m.mp.dps,rigorous_interval=False))

@lru_cache(maxsize=None)
def stieltjes_table(q,n):
    return tuple(m.stieltjes(n,m.mpf(a)/q) for a in range(1,q+1))

def trace_jet(q,n,chi=lambda a:1):
    # Pole-subtracted finite Fourier jets; avoid black-box differentiation
    # through the removable gamma/zeta cancellation inside polylog near s=1.
    units=[a for a in range(1,q) if gcd(a,q)==1]
    weights=[m.fsum(chi(a)*m.exp(2*m.pi*m.j*a*b/q) for a in units)
             for b in range(1,q+1)]
    return (-1)**n/m.mpf(q)*m.fsum(
        weights[b-1]*m.fsum(m.binomial(n,j)*m.log(q)**(n-j)*stieltjes_table(q,j)[b-1]
                           for j in range(n+1)) for b in range(1,q+1))

for n in (0,1,2):
    rhs=0 if n<2 else -2*m.log(2)*m.log(3)*m.log(5)
    record(f'principal trace q=30 derivative={n}',trace_jet(30,n),rhs)
chi4=lambda a: 1 if a%4==1 else -1
record('chi4 trace q=20 order 0',trace_jet(20,0,chi4),0)
record('chi4 trace q=20 order 1',trace_jet(20,1,chi4),-m.j*m.pi*m.log(5)/2)
# Entire-function conductor descent at a nonintegral complex order.
s0=m.mpc('1.7','0.3')
chi3=lambda a:1 if a%3==1 else -1
for q,f,chi,B in [(12,4,chi4,1+m.power(3,1-s0)),
                  (12,3,chi3,m.power(4,1-s0)+m.power(2,1-s0))]:
    def P(d):return m.fsum(chi(a)*m.polylog(s0,m.exp(2*m.pi*m.j*a/d))
                          for a in range(1,d) if gcd(a,d)==1)
    record(f'polylog conductor descent q={q},f={f}',P(q),B*P(f))
# Gamma jet evaluation via the master formula; compare finite character sums.
def gamjet(n,k,a):
    def germ(eps):
        return (-1)**k*m.rf(1+eps,k)*m.zeta(k+1+eps,a)
    return (-1)**n*m.diff(germ,m.mpf(0),n)
def G(d,chi,n,k):
    return m.fsum(chi(a)*gamjet(n,k,m.mpf(a)/d)
                  for a in range(1,d+1) if gcd(a,d)==1)
record('Stieltjes descent chi3 q=12 n=2 k=1',G(12,chi3,2,1),
       20*G(3,chi3,2,1)-72*m.log(2)*G(3,chi3,1,1)+68*m.log(2)**2*G(3,chi3,0,1))
record('Stieltjes descent chi4 q=12 n=2 k=1',G(12,chi4,2,1),
       10*G(4,chi4,2,1)-18*m.log(3)*G(4,chi4,1,1)+9*m.log(3)**2*G(4,chi4,0,1))
# S4 remains a conjecture; this test records evidence, not proof.
def gab(a,b):
    return m.im(m.quad(lambda t:(-m.log(t))**(a-1)*m.j*m.polylog(b,m.j*t)/(1-m.j*t),
                       [0,m.mpf('.5'),1])/m.factorial(a-1))
S4=-m.quad(lambda t:(-m.log(t))**3*m.log(1+t*t)/(1+t*t),[0,m.mpf('.5'),1])/6
rhs=(4*gab(4,1)-3*gab(3,2)-9*gab(2,3))/7 +m.pi**5/224-27*m.catalan*m.zeta(3)/224-2*m.im(m.polylog(4,m.j))*m.log(2)
record('S4 candidate: numerical evidence only',S4,rhs)
report=dict(mpmath=m.__version__,checks=checks,all_passed=True,
            warning='These are high-precision floating-point smoke tests, not interval certificates. Analytic proofs are in article.tex. S4 is not proved here.')
(ROOT/'certificates/numerical_checks.json').write_text(json.dumps(report,indent=2)+'\n')
print(f'PASS: {len(checks)} high-precision smoke tests; largest residual {max(m.mpf(c["absolute_error"]) for c in checks)}')
