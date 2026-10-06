#!/usr/bin/env python3
"""Exact formal-series checks for the kernel anchor and finite orbit quotient."""
if not __debug__:
 raise RuntimeError("Auxiliary producer scripts require ordinary Python; run the active-guard companion with python3 checks/verify.py")
from fractions import Fraction
from math import comb
import json
from pathlib import Path
from verify_model import dp
P=Path.cwd()
K=65
ZERO=[0]*(K+1); ONE=ZERO.copy(); ONE[0]=1

def add(a,b): return [x+y for x,y in zip(a,b)]
def neg(a): return [-x for x in a]
def sub(a,b): return add(a,neg(b))
def mul(a,b):
    c=ZERO.copy()
    for i,x in enumerate(a):
        if x:
            for j,y in enumerate(b[:K+1-i]):
                if y: c[i+j]+=x*y
    return c

def z(a): return [0]+a[:-1]
def divz(a):
    assert a[0]==0
    return a[1:]+[0]
def inv(a):
    assert a[0] in (1,-1)
    c=ZERO.copy(); c[0]=a[0]
    for n in range(1,K+1): c[n]=-sum(a[i]*c[n-i] for i in range(1,n+1))*c[0]
    return c

def divide(a,b):
    c=[Fraction(0)]*(K+1)
    for n in range(K+1): c[n]=Fraction(a[n]-sum(b[i]*c[n-i] for i in range(1,n+1)),b[0])
    return c

def phi(x):
    t=inv(sub(ONE,z(x)))
    return add(ONE,mul(z(x),mul(t,t)))
def cd(x):
    y=phi(x); d=mul(divz(sub(x,y)),inv(x)); c=sub(ONE,mul(sub(ONE,z(x)),d))
    return y,c,d

def evalH(hs,x):
    out=ZERO.copy(); powers=[ONE]
    for a in range(1,K+1): powers.append(mul(powers[-1],x))
    for n,h in enumerate(hs[:K+1]):
        for a,v in enumerate(h):
            if v:
                for m in range(K+1-n): out[n+m]+=v*powers[a][m]
    return out

if __name__=='__main__':
    totals,hs,_=dp(K)
    R=[comb(3*n,n)//(2*n+1) for n in range(K+1)]
    assert R==add(ONE,z(mul(mul(R,R),R)))
    X=mul(R,R); Y=phi(X)
    assert Y==add(sub(X,R),ONE)
    _,c,d=cd(X)
    assert c[:K]==ZERO[:K] and d[:K]==R[:K]
    HY=evalH(hs,Y)
    assert HY==R
    # H(x_m)=p_m*F+q_m; H(y_m)=v_m, y_0=Y and v_0=R.
    # F_m=(v_m-q_m)/p_m differs from F only at order z^(m+2).
    x=ONE; y=Y; p=ONE; q=ZERO; v=R
    outcomes=[]
    for m in range(31):
        Fm=divide(sub(v,q),p)
        exact_through=m+1
        assert Fm[:exact_through+1]==totals[:exact_through+1], m
        delta=[Fm[n]-totals[n] for n in range(exact_through+2)]
        outcomes.append({'iterations':m,'matched_through_n':exact_through,
                         'first_unmatched_coefficient_n':exact_through+1,
                         'difference_at_next_n':str(delta[-1])})
        x,c,d=cd(x); p=mul(c,p); q=add(mul(c,q),d)
        y,c,d=cd(y); v=add(mul(c,v),d)
    result={'kernel_root_equation':'R=1+zR^3, X=R^2',
            'anchor_argument':'Y=phi(X)=R^2-R+1',
            'kernel_and_anchor_exact_through_n':K-1,
            'finite_orbit_coefficient_checks':outcomes}
    (P/'verification_orbit.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))
