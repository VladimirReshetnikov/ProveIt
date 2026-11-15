#!/usr/bin/env python3
"""Sanity-check the countervaluation in exchange_and_brouwer.tex.

The unbounded schema proof is algebraic in that note. This finite run is
supplementary evidence, not a replacement for its uniform argument.
The countermodel proves nonderivability of old B/explosion from the new
basis; because numerical code 1 is assigned True, it does NOT prove the
consistency or inconsistency of the replacement calculus.
"""
from functools import lru_cache
from itertools import product
from math import isqrt
import json

def pair(a,b): return (a+b)*(a+b+1)//2+b
def unpair(n):
    s=(isqrt(8*n+1)-1)//2
    b=n-s*(s+1)//2
    return s-b,b
def I(a,b): return 4*pair(a,b)
def M(a,b): return I(a,b)+1
def U(a,b): return I(b,a)+2
def E(a,b): return I(a,b)+3
def N(a): return I(a,1)
def Ex(a,b): return N(U(a,N(b)))
def And(a,b): return N(I(a,N(b)))
@lru_cache(None)
def value(n):
    if n==0: return True
    a,b=unpair(n//4)
    tag=n%4
    if tag==0: return (not value(a)) or value(b)
    if tag==1: return (a,b)==(0,0)
    if tag==2: return value(a)
    return False
def gate(a,b,c):
    v=I(M(a,b),U(c,M(a,b)))
    p=I(c,M(c,b))
    s=U(b,And(I(M(a,b),p),I(M(c,b),c)))
    q=U(c,I(s,N(p)))
    return N(I(v,q))
def main():
    counts={k:0 for k in ('h2','h3','h4','h5','h6','gamma','gate','rho8','T','dualB')}
    for a,b,c in product(range(6),repeat=3):
        tests={
          'h2':I(U(a,U(b,c)),U(b,U(a,c))),
          'h3':I(M(c,a),I(E(c,b),M(b,a))),
          'h4':I(E(c,a),I(M(b,c),M(b,a))),
          'h5':Ex(a,E(c,a)),
          'h6':I(U(a,b),I(U(a,I(b,c)),U(a,c))),
          'gamma':I(c,U(c,c)),
          'T':I(U(a,c),c),
          'dualB':I(c,U(a,N(U(a,N(c)))))
        }
        if c!=a and c!=b: tests['gate']=gate(a,b,c)
        for k,v in tests.items():
            if not value(v): raise AssertionError((k,a,b,c,v))
            counts[k]+=1
        for d in range(a+1):
            r=I(I(I(c,d),a),I(I(a,c),I(b,c)))
            if not value(r): raise AssertionError(('rho8',a,b,c,d))
            counts['rho8']+=1
    h=M(1,0)
    old=I(Ex(0,U(0,h)),h)
    explosion=I(1,h)
    assert value(0) and value(1) and not value(h)
    assert not value(old) and not value(explosion)
    print(json.dumps({'schema_instances_passed':counts,
      'false_old_B':{'D':0,'H':h,'code':old},
      'false_explosion':{'H':h,'code':explosion},
      'claim':'nonderivability of old B and explosion from replacement basis',
      'scope':'finite supplementary check; uniform algebraic proof in accompanying TeX'},indent=2))
if __name__=='__main__': main()
