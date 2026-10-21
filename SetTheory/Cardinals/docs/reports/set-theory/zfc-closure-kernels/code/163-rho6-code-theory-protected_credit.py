#!/usr/bin/env python3
"""Exact finite protected-prefix credit for the native candidate scheduler.
The all-natural justification is in protected_credit.md. No binary simulator.
"""
from functools import cache
from math import isqrt
import json

def unpair(n):
    assert isinstance(n, int) and n >= 0
    s = (isqrt(8*n+1)-1)//2
    y = n-s*(s+1)//2
    return s-y,y

def second(n): return unpair(n)[1]

@cache
def summary(n):
    tag,y=unpair(n)
    r=second(y) if tag<3 else second(second(second(y)))
    first=(0,1,-1)[tag] if tag<3 else 10
    if r:
        assert 0 <= r-1 < n
        balance,minimum,length=summary(r-1)
    else:
        balance=minimum=length=0
    return first+balance, min(0,first+minimum), length+1

def credit(n):
    """Minimal credit for the conservative (MP delta0) schedule from cutoff n."""
    s=(isqrt(8*n+1)-1)//2
    end=max(6,(s+1)*(s+2)//2)
    balance=minimum=0
    for k in range(n,end):
        b,m,_=summary(k)
        minimum=min(minimum,balance+m)
        balance+=b
    return -minimum

def root_credit(np,pl=0):
    if not pl:return credit(np)
    b,m,_=summary(pl-1)
    return max(0,-m,credit(np)-b)

if __name__=='__main__':
    # Independent finite support check against an explicit recursive command word.
    def explicit(n):
        tag,y=unpair(n)
        r=second(y) if tag<3 else second(second(second(y)))
        e=(0,1,-1)[tag] if tag<3 else 10
        return [e]+(explicit(r-1) if r else [])
    for n in range(10000):
        w=explicit(n);v=0;lo=0
        for e in w:v+=e;lo=min(lo,v)
        assert summary(n)==(v,lo,len(w))
    # Verify each of the first 2000 whole diagonal statements arithmetically.
    bglobal=0;lowest=0
    for s in range(2000):
        local=0;low=0
        for n in range(s*(s+1)//2,(s+1)*(s+2)//2):
            b,m,_=summary(n);low=min(low,local+m);local+=b
        assert s<3 or low>=0
        lowest=min(lowest,bglobal+low);bglobal+=local
    assert lowest==0
    result={'status':'FINITE_SUPPORT_CHECK_PASS','explicit_words':10000,
            'diagonals':2000,'maximum_candidate_exclusive':2000*2001//2,
            'initial_credits':[{'np':n,'credit':credit(n)} for n in range(64)],
            'scope':'Exact finite checks support the separate induction; no new machine or universal binary runtime claim.'}
    print(json.dumps(result,indent=2))
