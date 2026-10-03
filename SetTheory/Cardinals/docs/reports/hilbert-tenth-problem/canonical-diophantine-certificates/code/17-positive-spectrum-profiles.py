#!/usr/bin/env python3
"""Exact, horizon-independent sign profiles for positive-base exponential polynomials.

Standard library only. A horizon of None means all nonnegative integers.
Integer arithmetic is exact; values can have a number of bits linear in the horizon.
"""
from __future__ import annotations
from dataclasses import dataclass
from functools import lru_cache
from math import comb
from typing import Callable, Optional


def sign(x: int) -> int:
    return (x > 0) - (x < 0)


@dataclass(frozen=True)
class Run:
    lo: int
    hi: Optional[int]
    sign: int

    def contains(self, n: int) -> bool:
        return self.lo <= n and (self.hi is None or n <= self.hi)


class ExpPoly:
    """sum_base P_base(n)*base**n; coefficient lists use ascending degrees."""
    def __init__(self, terms: dict[int, list[int] | tuple[int, ...]]):
        clean = {}
        for base, coeffs in sorted(terms.items()):
            if not isinstance(base, int) or base < 1:
                raise ValueError("Bases must be positive integers")
            c = list(coeffs)
            if not all(isinstance(x, int) for x in c):
                raise TypeError("Coefficients must be integers")
            while c and c[-1] == 0:
                c.pop()
            if c:
                clean[base] = tuple(c)
        self.terms = clean
        self.evaluations = 0

    @lru_cache(maxsize=None)
    def value(self, n: int) -> int:
        if n < 0 or not isinstance(n, int):
            raise ValueError("Index must be a nonnegative integer")
        self.evaluations += 1
        result = 0
        for b, cs in self.terms.items():
            p = 0
            for c in reversed(cs):
                p = p*n + c
            result += p * pow(b, n)
        return result

    def eventual_sign(self) -> int:
        if not self.terms:
            return 0
        return sign(self.terms[max(self.terms)][-1])

    def difference(self, a: int) -> ExpPoly:
        terms = {}
        for b, c in self.terms.items():
            terms[b] = [b*sum(comb(h,k)*c[h] for h in range(k,len(c)))
                        - a*c[k] for k in range(len(c))]
        return ExpPoly(terms)

    def shifted_constant(self, delta: int) -> ExpPoly:
        d = {b:list(c) for b,c in self.terms.items()}
        d.setdefault(1,[0])[0] += delta
        return ExpPoly(d)


def annihilator(shape: dict[int,int]) -> list[int]:
    """shape maps a base to its allowed degree (zero coefficients are permitted)."""
    if not shape or any(b<1 or d<0 for b,d in shape.items()):
        raise ValueError("Nonempty shape with positive bases and nonnegative degrees required")
    return [b for b,d in sorted(shape.items()) for _ in range(d+1)]


def make_chain(f: ExpPoly, shape: dict[int,int]) -> tuple[list[ExpPoly],list[int]]:
    for b,c in f.terms.items():
        if b not in shape or len(c)>shape[b]+1:
            raise ValueError("Polynomial does not fit its declared shape")
    aa = annihilator(shape)
    chain = [f]
    for a in aa:
        chain.append(chain[-1].difference(a))
    assert not chain[-1].terms
    return chain, aa


def _first_true(pred: Callable[[int], bool], lo: int,
                hi: Optional[int], eventual: bool) -> Optional[int]:
    if pred(lo):
        return lo
    if hi is None:
        if not eventual:
            return None
        step = 1
        right = lo+step
        while not pred(right):
            step *= 2
            right = lo+step
    else:
        right = hi
        if not pred(right):
            return None
    left = lo+1
    while left < right:
        mid = (left+right)//2
        if pred(mid):
            right = mid
        else:
            left = mid+1
    return left


def _monotone_runs(f: ExpPoly, lo: int, hi: Optional[int], direction: int) -> list[Run]:
    if direction == 0:
        return [Run(lo,hi,sign(f.value(lo)))]
    # f(n)/a**n is monotone, but f itself need not be. Only its sign is used.
    sf = lambda n: direction * sign(f.value(n))
    tail = direction*f.eventual_sign()
    ge = _first_true(lambda n:sf(n)>=0,lo,hi,tail>=0)
    gt = _first_true(lambda n:sf(n)>0,lo,hi,tail>0)
    out = []
    if ge is None:
        return [Run(lo,hi,-direction)]
    if lo < ge:
        out.append(Run(lo,ge-1,-direction))
    if gt is None:
        out.append(Run(ge,hi,0))
    else:
        if ge < gt:
            out.append(Run(ge,gt-1,0))
        out.append(Run(gt,hi,direction))
    return out


def _append_run(out: list[Run], r: Run) -> None:
    if r.hi is not None and r.lo>r.hi:
        return
    if not out:
        out.append(r)
        return
    p = out[-1]
    if p.hi is None:
        raise AssertionError("An infinite interval must be last")
    if r.lo == p.hi:
        if r.sign != p.sign:
            raise AssertionError("Inconsistent overlapping endpoint")
        out[-1] = Run(p.lo,r.hi,p.sign)
    elif r.lo == p.hi+1:
        if r.sign == p.sign:
            out[-1] = Run(p.lo,r.hi,p.sign)
        else:
            out.append(r)
    else:
        raise AssertionError("Intervals do not form an adjacent cover")


def build_profiles(chain: list[ExpPoly], horizon: Optional[int]) -> list[list[Run]]:
    if horizon is not None and horizon < 0:
        raise ValueError("Horizon must be nonnegative or None")
    profiles: list[list[Run]] = [[] for _ in chain]
    profiles[-1] = [Run(0,horizon,0)]
    D = len(chain)-1
    for j in reversed(range(D)):
        out: list[Run] = []
        for child in profiles[j+1]:
            upper = None if child.hi is None else child.hi+1
            if horizon is not None:
                upper = min(upper,horizon)  # child.hi is finite in this mode
            for r in _monotone_runs(chain[j],child.lo,upper,child.sign):
                _append_run(out,r)
        assert len(out)<=2*(D-j)-1
        profiles[j] = out
    return profiles


def verify_profiles(chain: list[ExpPoly], profiles: list[list[Run]],
                    horizon: Optional[int]) -> bool:
    """Local verifier: uses endpoints and eventual signs, never scans the horizon."""
    D = len(chain)-1
    if len(profiles)!=len(chain):
        return False
    for j,rows in enumerate(profiles):
        cap = 1 if j==D else 2*(D-j)-1
        if not rows or len(rows)>cap or rows[0].lo != 0:
            return False
        for k,r in enumerate(rows):
            if r.sign not in (-1,0,1) or r.lo<0:
                return False
            if r.hi is not None and r.hi<r.lo:
                return False
            if k+1<len(rows):
                if r.hi is None or rows[k+1].lo!=r.hi+1 or rows[k+1].sign==r.sign:
                    return False
        if rows[-1].hi != horizon:
            return False
    if profiles[-1] != [Run(0,horizon,0)]:
        return False
    for j in reversed(range(D)):
        f = chain[j]
        if horizon is None and profiles[j][-1].sign != f.eventual_sign():
            return False
        samples = []
        for child in profiles[j+1]:
            samples.append(child.lo)
            if child.hi is not None:
                u = child.hi+1
                samples.append(u if horizon is None else min(u,horizon))
        for r in profiles[j]:
            points = [r.lo]
            if r.hi is not None:
                points.append(r.hi)
            points.extend(x for x in samples if r.contains(x))
            if any(sign(f.value(x))!=r.sign for x in points):
                return False
    return True


def brute_profile(f: ExpPoly,T:int) -> list[Run]:
    out: list[Run] = []
    for n in range(T+1):
        _append_run(out,Run(n,n,sign(f.value(n))))
    return out


def restrict_profile(profile: list[Run],T:int) -> list[Run]:
    return [Run(r.lo,T if r.hi is None else min(r.hi,T),r.sign)
            for r in profile if r.lo<=T]


def first_negative(profile:list[Run]) -> Optional[int]:
    return next((r.lo for r in profile if r.sign<0),None)


def profile_json(profiles:list[list[Run]]) -> list[list[dict]]:
    return [[{'lo':r.lo,'hi':r.hi,'sign':r.sign} for r in rows] for rows in profiles]


if __name__ == '__main__':
    import json
    f=ExpPoly({1:[64],2:[-20],4:[1]})
    chain,_=make_chain(f,{1:0,2:0,4:0})
    for T in (6,None):
        p=build_profiles(chain,T)
        assert verify_profiles(chain,p,T)
        print(json.dumps({'horizon':T,'profiles':profile_json(p)},indent=2))
