#!/usr/bin/env python3
"""Check the finite certificate premise of the pairing-change theorem.

The all-natural isomorphism is proved in report.tex and research/pairing_change.md.
The inherited forward checker verifies every zero/subterm bound structurally;
this check therefore does not need to evaluate gigantic dyadic term codes.
"""
from pathlib import Path
from functools import cache
from math import isqrt
import json,sys
import check_classical_compact as certificate

HERE=Path(__file__).resolve().parent
def cantor_unpair(n):
    s=(isqrt(8*n+1)-1)//2;b=n-s*(s+1)//2
    return s-b,b
def dyadic(a,b):return (1<<a)*(2*b+1)-1
@cache
def recode(n):
    if not n:return 0
    a,b=cantor_unpair(n//4)
    assert a<n and b<n
    return 4*dyadic(recode(a),recode(b))+n%4
def check():
    result=certificate.check(HERE/'dominated_rho8_full_certificate.json')
    assert result['verified'] and result['proof_nodes']==3728 and result['shared_terms']==5160
    assert recode(16)==20 and recode(20)==16
    return {'status':'PASS','certificate':result,'order_counterexample':{'phi16':20,'phi20':16},
            'scope':'Full structural check of the inherited finite recovery certificate; ordinary hereditary-recoding theorem supplied separately.'}
if __name__=='__main__':
    assert __debug__ and not sys.flags.optimize
    print(json.dumps(check(),indent=2))
