#!/usr/bin/env python3
"""Small independent integer polynomial kernel used only by auditors.

Representation: a dictionary from sorted tuples of variable indices to integer
coefficients.  The empty tuple denotes the constant monomial.  This module has
no dependency on any source compiler, factorizer, optimizer, or artifact.
"""
import json
from collections import defaultdict

def need(condition, message):
    if not condition:
        raise ValueError(message)

def norm(terms):
    result=defaultdict(int)
    for coefficient, monomial in terms:
        result[tuple(sorted(monomial))]+=coefficient
    return {m:c for m,c in result.items() if c}

def mul(left, right):
    result=defaultdict(int)
    for m,c in left.items():
        for n,d in right.items():
            result[tuple(sorted(m+n))]+=c*d
    return {m:c for m,c in result.items() if c}

def sub(polynomial, variable, restoration):
    result=defaultdict(int)
    for monomial, coefficient in polynomial.items():
        term={():coefficient}
        for v in monomial:
            term=mul(term,restoration if v==variable else {(v,):1})
        for m,c in term.items():
            result[m]+=c
    return {m:c for m,c in result.items() if c}

def canon(value):
    return (json.dumps(value,sort_keys=True,separators=(',',':'))+'\n').encode()
