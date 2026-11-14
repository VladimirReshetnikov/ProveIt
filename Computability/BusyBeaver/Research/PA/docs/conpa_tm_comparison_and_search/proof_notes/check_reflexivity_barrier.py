#!/usr/bin/env python3
"""Regression check for reflexivity_barrier.md; not a formal proof.

Upstream coding and heads: jamesyc/BusyBeaver
407cdc356f6b586635e71ac92be394255f4bfea4, PA196/Logic/Basic.lean.
"""
from functools import lru_cache
from itertools import product
from math import isqrt
import json

def pair(a,b):return (a+b)*(a+b+1)//2+b
def unpair(n):
    s=(isqrt(8*n+1)-1)//2
    b=n-s*(s+1)//2
    return s-b,b
def I(a,b):return 4*pair(a,b)
def M(a,b):return 4*pair(a,b)+1
def U(a,b):return 4*pair(b,a)+2
def E(a,b):return 4*pair(a,b)+3
def N(a):return I(a,1)
def A(a,b):return N(I(a,N(b)))
def Ex(a,b):return N(U(a,N(b)))
def implies(a,b):return not a or b
@lru_cache(None)
def J(n):
    if n==0:return True
    a,b=unpair(n//4)
    assert a<n and b<n
    tag=n%4
    if tag==0:return implies(J(a),J(b))
    if tag==1:return False if a==b else J(a)
    if tag==2:return J(a)  # U reverses the pairing components.
    return a==b
def heads(d,h,a):
    return [I(Ex(d,U(d,h)),h),I(U(d,U(a,h)),U(a,U(d,h))),
        I(M(h,d),I(E(h,a),M(a,d))),I(E(h,d),I(M(a,h),M(a,d))),
        E(h,h),I(U(d,a),I(U(d,I(a,h)),U(d,h)))]
def gate(a,b,c):
    eqvac=I(E(a,b),U(c,E(a,b)))
    memvac=I(M(a,b),U(c,M(a,b)))
    point=I(c,M(c,b))
    sep=U(b,A(I(M(a,b),point),I(M(c,b),c)))
    q=U(c,I(sep,N(point)))
    return N(I(eqvac,I(memvac,q)))
def run(bound=4):
    assert [J(i) for i in range(4)]==[True,False,True,True]
    for a,b in product(range(32),repeat=2):
        assert unpair(pair(a,b))==(a,b)
        assert J(I(a,b))==implies(J(a),J(b))
        assert J(M(a,b))==(False if a==b else J(a))
        assert J(U(a,b))==J(b)
        assert J(E(a,b))==(a==b)
    checked_heads=checked_gates=0
    largest_bits=0
    for d,h,a in product(range(bound),repeat=3):
        hh=heads(d,h,a)
        assert all(J(n) for n in hh)
        checked_heads+=len(hh)
        largest_bits=max(largest_bits,max(n.bit_length() for n in hh))
        if a!=d and a!=h:
            f=gate(h,d,a);assert J(f)
            checked_gates+=1;largest_bits=max(largest_bits,f.bit_length())
    for a,b,c,u in product([False,True],repeat=4):
        assert implies(implies(implies(c,u),a),implies(implies(a,c),implies(b,c)))
    assert not J(Ex(0,E(1,0)))
    return {'parameter_bound_exclusive':bound,'modified_head_instances':checked_heads,
        'guarded_gate_instances':checked_gates,'constructor_instances_each':1024,
        'propositional_boolean_instances':16,'largest_test_code_bit_length':largest_bits,
        'original_witness_counterexample':{'D':0,'H':1,'value':False},'all_checks_passed':True}
if __name__=='__main__':print(json.dumps(run(),indent=2))
