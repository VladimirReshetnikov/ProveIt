#!/usr/bin/env python3
"""Exact Fraction checks of the finite enclosure on a rational three-atom measure."""
from fractions import Fraction as F

x=[F(1),F(1,3),F(1,9)]
r=[F(99,100),F(33,100)]
q=lambda t:(t-r[0])*(t-r[1])
# Force both orthogonality equations exactly, with positive weights.
a=[x[1]-x[2], -(x[0]-x[2]), x[0]-x[1]]
w=[a[i]/q(x[i]) for i in range(3)]
assert all(u>0 for u in w)
assert sum(w[i]*q(x[i]) for i in range(3))==0
assert sum(w[i]*x[i]*q(x[i]) for i in range(3))==0
h=sum(w[i]*q(x[i])**2 for i in range(3))
nu=[w[i]*q(x[i])**2/h for i in range(3)]
tau=lambda k:sum(nu[i]*x[i]**k for i in range(3))
assert tau(0)==1
for j in range(2):
    rr=r[j]; delta=x[j]-rr; S=lambda t:t-r[1-j]
    s2=sum(w[i]*S(x[i])**2 for i in range(3))
    v=h/s2; M=w[j]*S(x[j])**2/s2
    I=sum(nu[i]/(rr-x[i]) for i in range(3) if i!=j)
    assert delta*M==v*I
    assert sum(w[i]*(x[i]-rr)*S(x[i])**2 for i in range(3))==0
    g=min(abs(rr-x[i]) for i in range(3) if i!=j)
    eta=v/g**2
    assert 0<eta<1 and M>=1-eta
    lo=v/rr*max(0,1-tau(1)*(1/g+1/rr))
    hi=v/rr*(1+tau(1)/g)/(1-eta)
    assert lo<=delta<=hi
    if j==0: assert delta>=v/rr
    for k in range(4):
        P=sum(tau(l)/rr**l for l in range(k+1))
        E=tau(k+1)/(rr**k*g)+min(tau(1)/rr,eta/(1-eta))*sum((x[0]/rr)**l for l in range(k+1))
        lo=v/rr*max(0,P-E); hi=v/rr*(P+E)/(1-eta)
        assert lo<=delta<=hi,(j,k,lo,delta,hi)
    print('rank',j+1,'exact error',delta,'variance',v,'gap',g,'all bounds verified')
print('PASS: exact identities and all finite enclosures at both ranks.')
