#!/usr/bin/env python3
"""Independent subtracted quadrature for low-order Stieltjes products.
Uses the classical parameter Taylor series about 1, not the correlation
closure, to evaluate gamma_1 and gamma_2. Floating-point diagnostics only.
"""
import json
from pathlib import Path
import mpmath as mp
mp.mp.dps=45
TERMS=140
H=mp.mpf(0); H2=mp.mpf(0)
c={0:[mp.euler],1:[mp.stieltjes(1)],2:[mp.stieltjes(2)]}
for k in range(1,TERMS+1):
    H+=mp.mpf(1)/k; H2+=mp.mpf(1)/k**2
    z=mp.zeta(k+1); z1=mp.diff(mp.zeta,k+1); z2=mp.diff(mp.zeta,k+1,2)
    c[0].append((-1)**k*z)
    c[1].append((-1)**(k+1)*(z1+H*z))
    c[2].append((-1)**k*(z2+2*H*z1+(H*H-H2)*z))

def T(n,y):
    return mp.polyval(list(reversed(c[n])),y)

def fp(m,n):
    a=mp.mpf(1)/2
    gm,gn=T(m,-a),T(n,-a)
    def f(x):
        return mp.log(x)**m/x*(T(n,x-a)-gn)+T(m,x)*T(n,x-a)
    def g(x):
        return mp.log(x)**n/x*(T(m,x-a)-gm)+T(n,x)*T(m,x-a)
    return mp.quad(f,[0,a])+mp.quad(g,[0,a])+gn*mp.log(a)**(m+1)/(m+1)+gm*mp.log(a)**(n+1)/(n+1)

z2,z3,z4=mp.zeta(2),mp.zeta(3),mp.zeta(4)
g=[mp.stieltjes(k,mp.mpf(1)/2) for k in range(4)]
cases=[(1,0,mp.mpf(3)/2*g[2]+2*z2*g[0]-z3),
       (1,1,g[3]+4*z2*g[1]+2*z3*g[0]-z2*z2-z4),
       (2,0,mp.mpf(4)/3*g[3]+4*z2*g[1]+2*z3*g[0]-z2*z2-3*z4)]
checks=[]
for m,n,rhs in cases:
    lhs=fp(m,n);err=abs(lhs-rhs)
    passed=err<mp.mpf('1e-30')
    print(m,n,mp.nstr(lhs,25),mp.nstr(err,8),passed,flush=True)
    assert passed
    checks.append({'m':m,'n':n,'shift':'1/2','lhs':mp.nstr(lhs,45),'rhs':mp.nstr(rhs,45),'absolute_residual':mp.nstr(err,12),'passed':passed})
result={'status':'PASS','dps':45,'Taylor_terms':TERMS,'number_of_checks':len(checks),'scope':'Independent non-interval numerical quadrature; analytic proof is separate.','checks':checks}
(Path(__file__).resolve().parents[1]/'results'/'stieltjes_pair_verification.json').write_text(json.dumps(result,indent=2)+'\n')
