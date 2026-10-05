#!/usr/bin/env python3
"""Exact polynomial certificate for the order-six left factor (stdlib only).

After the order-three and order-four factors act on the canonical analytic
completion, e*c(n)/n! = P(n)/(4*n). The returned zero polynomial proves that
the displayed order-six factor annihilates this expression. This is NOT a
proof of the guessed recurrence for the combinatorial integer sequence.
"""
from __future__ import annotations
from math import comb
from pathlib import Path

# Ascending coefficient order.
P = [4, 39956, 99549, 94552, 45249, 11926, 1745, 132, 4]


def add(a, b):
    c = [0]*max(len(a), len(b))
    for i, x in enumerate(a): c[i] += x
    for i, x in enumerate(b): c[i] += x
    while len(c)>1 and c[-1]==0: c.pop()
    return c


def mul(a, b):
    c = [0]*(len(a)+len(b)-1)
    for i, x in enumerate(a):
        for j, y in enumerate(b): c[i+j] += x*y
    while len(c)>1 and c[-1]==0: c.pop()
    return c


def shift(a, h):
    return [sum(a[j]*comb(j,k)*h**(j-k) for j in range(k,len(a)))
            for k in range(len(a))]


def certificate():
    # 4*ell_k(n), k=1..6, from the OEIS factorization.
    ell = [[-22,-7],[-2],[3,-1],[-75,-8],[-44,-4],[4]]
    result = [-4*x for x in P]
    rising = [1]
    for k in range(1,7):
        if k>=2: rising=mul(rising,[k-1,1])
        result=add(result,mul(ell[k-1],mul(rising,shift(P,k))))
    assert result==[0], result
    return result


if __name__=='__main__':
    result=certificate()
    text=('PASS exact: the cleared polynomial certificate is '+str(result)+'.\n'
          'Identity: -4 P(n) + sum_{k=1}^6 4 ell_k(n) (n+1)^(rising k-1) P(n+k) = 0.\n'
          'Scope: the canonical analytic completion only; not the integer count.\n')
    print(text,end='')
    root=Path(__file__).resolve().parents[1]
    (root/'data'/'factor_certificate.txt').write_text(text)
