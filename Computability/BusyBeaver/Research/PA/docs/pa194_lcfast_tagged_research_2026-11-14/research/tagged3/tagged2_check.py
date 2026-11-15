#!/usr/bin/env python3
"""Finite checks for the unimplemented shared-first-operand tagged2 variant."""
from functools import lru_cache
from pathlib import Path
import json
from recoding import Constructors,C4,pair,unpair

class BinaryConstructors(Constructors):
    def I(self,a,b):return 2*pair(2*a,b)
    def U(self,a,b):return 2*pair(2*b+1,a)
    def M(self,a,b):return 2*pair(2*a,b)+1
    def E(self,a,b):return 2*pair(2*a+1,b)+1
C2=BinaryConstructors()

@lru_cache(None)
def f(n):
    if n==0:return 0
    a,b=unpair(n//4);tag=n%4
    if tag==0:return C2.I(f(a),f(b))
    if tag==1:return C2.M(f(a),f(b))
    if tag==2:return C2.U(f(b),f(a))
    return C2.E(f(a),f(b))

@lru_cache(None)
def g(n):
    if n==0:return 0
    c,b=unpair(n//2);a=c//2
    if n%2==0:
        return C4.I(g(a),g(b)) if c%2==0 else C4.U(g(b),g(a))
    return C4.M(g(a),g(b)) if c%2==0 else C4.E(g(a),g(b))

def main():
    for n in range(5000):
        assert g(f(n))==n
        assert f(g(n))==n
    cases=0
    for a in range(16):
        for b in range(16):
            for name in ['I','U','M','E']:
                assert f(getattr(C4,name)(a,b))==getattr(C2,name)(f(a),f(b))
                assert g(getattr(C2,name)(a,b))==getattr(C4,name)(g(a),g(b))
                cases+=2
    heads=0
    for d in range(4):
        for a in range(4):
            for h in range(4):
                assert [f(x) for x in C4.heads(d,a,h)]==C2.heads(f(d),f(a),f(h))
                assert [g(x) for x in C2.heads(d,a,h)]==C4.heads(g(d),g(a),g(h))
                assert f(C4.gate(d,a,h))==C2.gate(f(d),f(a),f(h))
                assert g(C2.gate(d,a,h))==C4.gate(g(d),g(a),g(h))
                heads+=14
    for n in range(16):
        assert f(C4.Gamma(n))==C2.Gamma(f(n))
        assert g(C2.Gamma(n))==C4.Gamma(g(n))
    r={'status':'PASS; encoding only, no source or table constructed',
       'inverse_values_each_direction':5000,'constructor_cases':cases,
       'head_and_gate_cases':heads,'diagonal_cases':32,
       'first_24_forward':[f(n) for n in range(24)],
       'constructors':{'I':'2*p(2*a,b)','U':'2*p(2*body+1,binder)',
                       'M':'2*p(2*a,b)+1','E':'2*p(2*a+1,b)+1'},
       'implementation_status':'Unimplemented further-research variant; no state count asserted.'}
    Path(__file__).with_name('tagged2_checks.json').write_text(json.dumps(r,indent=2)+'\n')
    print(json.dumps(r,indent=2))
if __name__=='__main__':main()
