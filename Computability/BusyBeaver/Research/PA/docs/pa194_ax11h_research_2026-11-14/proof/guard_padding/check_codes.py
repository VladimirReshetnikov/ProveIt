#!/usr/bin/env python3
"""Exact numeral checks supporting the variable-alias counterinterpretation.

This checks the stated finite code calculations. Universal validity and
nonderivability are proved in guard_padding_obstruction.tex, not inferred
from a finite experiment.
"""
from functools import lru_cache
from math import isqrt
import json


def pair(a, b):
    return (a+b)*(a+b+1)//2+b


def unpair(n):
    s=(isqrt(8*n+1)-1)//2
    b=n-s*(s+1)//2
    return s-b,b


def imp(a,b):
    return 4*pair(a,b)


def mem(a,b):
    return 4*pair(a,b)+1


def fresh_wrapper(a,b,c):
    atom=mem(a,b)
    return imp(imp(atom,atom),c)


@lru_cache(None)
def support(n):
    if n==0:
        return frozenset()
    a,b=unpair(n//4)
    tag=n%4
    if tag==0:
        assert a<n and b<n
        return support(a)|support(b)
    if tag==2:
        assert a<n
        return support(a)|{b}
    return frozenset((a,b))


def alias(i):
    return 1 if i==4 else i


assert mem(0,0)==1
assert imp(1,0)==4
assert support(1)==frozenset((0,))
assert support(4)==frozenset((0,))
assert imp(1,1)==16
assert fresh_wrapper(0,0,0)==544
assert alias(1)==alias(4)==1

result={
    'status':'PASS',
    'scope':'Exact finite numeral checks only; see written proof for universal statements.',
    'M_0_0':mem(0,0),
    'I_1_0':imp(1,0),
    'support_1':sorted(support(1)),
    'support_4':sorted(support(4)),
    'I_1_1':imp(1,1),
    'F_0_0_0':fresh_wrapper(0,0,0),
    'alias_1':alias(1),
    'alias_4':alias(4),
}
print(json.dumps(result,indent=2))
