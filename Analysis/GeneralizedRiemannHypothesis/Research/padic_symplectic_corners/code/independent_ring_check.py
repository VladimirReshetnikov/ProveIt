#!/usr/bin/env python3
"""Independent exhaustive check via pairing-one frames, not group sampling."""
from collections import Counter
from fractions import Fraction as F
from itertools import product
import json

def check(name, order, q, e, add, neg, mul, valuation):
    def sub(a,b): return add(a,neg(b))
    counts=Counter()
    vec=list(product(range(order), repeat=4))
    for x in vec:
        for y in vec:
            t=add(sub(mul(x[0],y[1]),mul(x[1],y[0])),sub(mul(x[2],y[3]),mul(x[3],y[2])))
            if t==1:
                counts[(x[0],y[0],x[1],y[1])]+=1
    total=sum(counts.values()); uniform=F(1,order**4)
    assert total==q**(7*e)*(1-F(1,q**4))
    d=1-F(1,q**4); alpha=(1-F(1,q**2))/d
    seen=Counter(); tv=F(0)
    for a,b,c,dentry in product(range(order), repeat=4):
        mat=(a,b,c,dentry)
        defect=sub(1,sub(mul(a,dentry),mul(b,c)))
        v=valuation(defect)
        f=(1-F(1,q**2))*sum((F(1,q)**r for r in range(min(v,e-1)+1)),F(0))
        if defect==0: f+=F(1,q**e)
        h=f/d
        actual=F(counts[mat],total)
        assert actual==uniform*h, (name,mat,actual,uniform*h)
        tv+=abs(actual-uniform)/2
        seen[str(v)]+=1
    expected=(1-F(1,q)+F(1,q**3))*F(q*q-1,q**4-1)
    assert tv==expected
    return dict(ring=name,q=q,e=e,frames=total,matrices=order**4,tv=str(tv),alpha=str(alpha),defect_classes=dict(seen),status='all exact counts agree')

def v2(x,e):
    return e if x==0 else min(e,(x&-x).bit_length()-1)

def poly_mul(a,b,mod):
    ans=0
    while b:
        if b&1:ans^=a
        b>>=1;a<<=1
    degree=mod.bit_length()-1
    while ans.bit_length()>degree:
        ans^=mod<<(ans.bit_length()-degree-1)
    return ans

out=[]
out.append(check('Z/4Z',4,2,2,lambda a,b:(a+b)%4,lambda a:-a%4,lambda a,b:a*b%4,lambda a:v2(a,2)))
out.append(check('F2[t]/(t^2)',4,2,2,lambda a,b:a^b,lambda a:a,lambda a,b:poly_mul(a,b,4),lambda a:v2(a,2)))
out.append(check('F4',4,4,1,lambda a,b:a^b,lambda a:a,lambda a,b:poly_mul(a,b,7),lambda a:1 if a==0 else 0))
print(json.dumps(out,indent=2))
