#!/usr/bin/env python3
"""Finite independent checks supporting the all-natural pairing theorem.

The proof is in pairing_change.md. These tests do not replace that proof.
"""
from functools import cache
from math import isqrt
from pathlib import Path
import json

def cantor(a,b):return (a+b)*(a+b+1)//2+b
def uncantor(n):
    s=(isqrt(8*n+1)-1)//2;b=n-s*(s+1)//2
    return s-b,b
def dyadic(a,b):return ((2*b+1)<<a)-1
def undyadic(n):
    q=n+1;a=(q&-q).bit_length()-1
    return a,((q>>a)-1)//2
@cache
def phi(n):
    if not n:return 0
    a,b=uncantor(n//4)
    assert a<n and b<n
    return 4*dyadic(phi(a),phi(b))+n%4
@cache
def psi(n):
    if not n:return 0
    a,b=undyadic(n//4)
    assert a<n and b<n
    return 4*cantor(psi(a),psi(b))+n%4

if __name__=='__main__':
    for n in range(100000):
        a,b=undyadic(n)
        assert dyadic(a,b)==n and b<=n//2
        assert a<=n and b<=n
    for a in range(10):
        for b in range(64):
            n=dyadic(a,b)
            assert undyadic(n)==(a,b) and n>=max(a,b)
    for n in range(512):
        assert psi(phi(n))==n
        assert phi(psi(n))==n
    for a in range(16):
        for b in range(16):
            for tag in range(4):
                assert phi(4*cantor(a,b)+tag)==4*dyadic(phi(a),phi(b))+tag
    assert [phi(n)for n in range(4)]==list(range(4))
    assert phi(16)==20 and phi(20)==16
    out={'status':'FINITE_SUPPORT_CHECK_PASS','inverse_codes':100000,
         'pair_rectangular_cases':640,'bidirectional_recoding_cases':512,
         'constructor_intertwining_cases':1024,
         'order_counterexample':{'old_le':[16,20],'recoded':[20,16]},
         'scope':'Finite arithmetic support; separate all-natural proof and separate native theorem certificate'}
    rendered=json.dumps(out,indent=2)+'\n'
    Path(__file__).with_name('dyadic_pairing_check.json').write_text(rendered)
    print(rendered,end='')
