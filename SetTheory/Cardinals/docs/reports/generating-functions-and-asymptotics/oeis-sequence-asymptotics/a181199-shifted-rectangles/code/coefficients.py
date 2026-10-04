#!/usr/bin/env python3
"""Exact all-order fixed-height coefficients for shifted rectangular tableaux.

Pure Python rational arithmetic. No fitted recurrence or OEIS terms are used.
The output is in two normalizations documented in the accompanying article.
"""
from __future__ import annotations
from collections import defaultdict
from fractions import Fraction as F
from functools import lru_cache
from itertools import permutations
from math import comb, factorial, prod
import argparse
import json
from pathlib import Path


def mul(a: tuple[F, ...], b: tuple[F, ...], J: int) -> tuple[F, ...]:
    out = [F(0)] * (J + 1)
    for i, ai in enumerate(a[:J + 1]):
        if ai:
            for j, bj in enumerate(b[:J + 1 - i]):
                if bj:
                    out[i + j] += ai * bj
    return tuple(out)


def exp_series(a: tuple[F, ...], J: int) -> tuple[F, ...]:
    assert not a[0]
    out = [F(1)] + [F(0)] * J
    for j in range(1, J + 1):
        out[j] = sum(k * a[k] * out[j-k] for k in range(1, j+1)) / j
    return tuple(out)


@lru_cache(None)
def cumulant(k: int) -> int:
    """Cumulants of a symmetric +/-1 random variable."""
    if k == 0:
        return 0
    moment = 1 if k % 2 == 0 else 0
    return moment - sum(comb(k-1, j-1) * cumulant(j) *
                        (1 if (k-j) % 2 == 0 else 0)
                        for j in range(1, k))


@lru_cache(None)
def moment(k: int, J: int) -> tuple[F, ...]:
    """E[(n^-1/2 sum_{i=1}^n eps_i)^k] in z=1/n, modulo z^(J+1)."""
    if k == 0:
        return (F(1),) + (F(0),) * J
    if k % 2:
        return (F(0),) * (J+1)
    out = [F(0)] * (J+1)
    for b in range(2, k+1, 2):
        shift = b//2 - 1
        if shift > J:
            break
        c = comb(k-1, b-1) * cumulant(b)
        tail = moment(k-b, J)
        for j in range(J+1-shift):
            out[j+shift] += c * tail[j]
    return tuple(out)


def multiply_y(a: dict[tuple[int,...], int], b: dict[tuple[int,...], int]):
    out = defaultdict(int)
    for ia, ca in a.items():
        for ib, cb in b.items():
            out[tuple(i+j for i,j in zip(ia,ib))] += ca*cb
    return dict(out)


def denominator_polys(m: int, J: int) -> list[dict[tuple[int,...], int]]:
    """h_r((y_i+y_j)^2: i<j), r=0..J; integer monomial dictionaries."""
    zero = (0,)*m
    h = [{zero:1}] + [{} for _ in range(J)]
    for i in range(m):
        for j in range(i+1,m):
            a={}
            for k in range(3):
                ex=[0]*m; ex[i]=k; ex[j]=2-k
                a[tuple(ex)] = comb(2,k)
            # Ascending updates multiply the generating series by (1-a*t)^-1.
            for r in range(1,J+1):
                add=multiply_y(a,h[r-1])
                for ex,c in add.items():
                    h[r][ex]=h[r].get(ex,0)+c
    return h


def signature(p: tuple[int,...]) -> int:
    return (-1)**sum(p[i]>p[j] for i in range(len(p)) for j in range(i+1,len(p)))


def coefficients(m: int, J: int) -> tuple[list[F], list[F]]:
    """Return c_j in M J_m/(4n)^d, and b_j in K_m m^(mn)n^-alpha."""
    if m < 1 or J < 0:
        raise ValueError('m must be positive and J nonnegative')
    h=denominator_polys(m,J)
    perms=[(tuple(i+p[i] for i in range(m)), signature(p))
           for p in permutations(range(m))]
    out=[F(0)]*(J+1)
    Jm=prod(factorial(i) for i in range(m))
    # Symmetry collapses the two determinant expansions to m! terms;
    # the normalizing Gaussian integral cancels this m!.
    for r in range(J+1):
        L=J-r
        aggregated=defaultdict(int)
        for base,sgn in perms:
            for ex,c in h[r].items():
                powers=tuple(a+b for a,b in zip(base,ex))
                if any(k%2 for k in powers):
                    continue
                aggregated[tuple(sorted(powers))]+=sgn*c
        answer=[F(0)]*(L+1)
        for powers,c in aggregated.items():
            if c == 0: continue
            p=(F(1),)+(F(0),)*L
            for k in powers:
                p=mul(p,moment(k,L),L)
            for j in range(L+1):answer[j]+=c*p[j]
        for j in range(L+1):out[r+j]+=answer[j]/(4**r*Jm)
    # Stirling's series for (mn)!/(n!)^m, after removing its leading term.
    logst=[F(0)]*(J+1)
    for j in range(1,J+1,2):
        logst[j]=bernoulli(j+1)/(j*(j+1))*(F(1,m**j)-m)
    stir=exp_series(tuple(logst),J)
    full=mul(tuple(out),stir,J)
    return out,list(full)


@lru_cache(None)
def bernoulli(n: int) -> F:
    if n==0:return F(1)
    return -sum(F(comb(n+1,k))*bernoulli(k) for k in range(n))/F(n+1)


def main() -> None:
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--height',type=int,default=5)
    parser.add_argument('--order',type=int,default=4)
    parser.add_argument('--output',type=Path)
    args=parser.parse_args()
    c,b=coefficients(args.height,args.order)
    result={'height':args.height,'order':args.order,
            'multinomial_normalization':[str(x) for x in c],
            'elementary_normalization':[str(x) for x in b]}
    text=json.dumps(result,indent=2)
    print(text)
    if args.output:
        args.output.parent.mkdir(parents=True,exist_ok=True)
        args.output.write_text(text+'\n',encoding='utf-8')

if __name__=='__main__':main()
