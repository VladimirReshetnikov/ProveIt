#!/usr/bin/env python3
"""Executable old/new formula recoding for the nested binary proposal.

The unbounded correctness argument is in nested_binary_code.tex.  This file
provides concrete constructors/decoders, the two recursive bijections, and
bounded inverse diagnostics. It constructs no accepted smaller Turing machine.
"""

from functools import cache
from math import isqrt
import argparse
import json


def pair(a, b):
    return (a+b)*(a+b+1)//2 + b


def unpair(n):
    s = (isqrt(8*n+1)-1)//2
    b = n-s*(s+1)//2
    return s-b, b


def old(tag, a, b):
    # For U, arguments are (binder,body), unlike Cantor's order.
    return 4*pair(b, a)+2 if tag == "U" else 4*pair(a, b)+{"I":0,"M":1,"E":3}[tag]


def new(tag, a, b):
    j = lambda x, y: 2*pair(x, y)
    if tag == "I": return j(a, b)
    if tag == "U": return j(b, a+1)+1
    if tag == "M": return j(j(a,b),0)+1
    if tag == "E": return j(j(a,b)+1,0)+1
    raise ValueError(tag)


def decode_old(n):
    assert n > 0
    a, b = unpair(n//4)
    tag = "IMUE"[n % 4]
    return (tag,b,a) if tag == "U" else (tag,a,b)


def decode_new(n):
    assert n > 0
    if n % 2 == 0:
        a,b = unpair(n//2)
        return "I",a,b
    r,s = unpair((n-1)//2)
    if s:
        return "U",s-1,r
    a,b = unpair(r//2)
    return ("M" if r % 2 == 0 else "E"),a,b


@cache
def forward(n):
    if n == 0: return 0
    tag,a,b = decode_old(n)
    return new(tag,forward(a),forward(b))


@cache
def backward(n):
    if n == 0: return 0
    tag,a,b = decode_new(n)
    return old(tag,backward(a),backward(b))


def main():
    ap=argparse.ArgumentParser()
    ap.add_argument("--bound",type=int,default=10000)
    args=ap.parse_args()
    assert args.bound > 0
    for n in range(args.bound):
        assert backward(forward(n)) == n
        assert forward(backward(n)) == n
        if n:
            for decoder,constructor in ((decode_old,old),(decode_new,new)):
                tag,a,b=decoder(n)
                assert a<n and b<n
                assert constructor(tag,a,b)==n
    assert forward(0)==0 and forward(1)==1 and forward(2)==5 and forward(4)==2
    print(json.dumps({"bound":args.bound,"bounded_inverse_checks":2*args.bound,
                      "bounded_decoder_checks":2*(args.bound-1),
                      "small_forward_values":[forward(i) for i in range(16)],
                      "proof":"Course-of-values recursion and constructor induction; see nested_binary_code.tex.",
                      "state_count_claim":None},indent=2))


if __name__=="__main__":
    if not __debug__: raise SystemExit("Assertions must remain enabled.")
    main()
