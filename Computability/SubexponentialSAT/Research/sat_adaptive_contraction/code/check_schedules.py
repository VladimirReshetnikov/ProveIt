#!/usr/bin/env python3
"""Exact capacity and sufficient-margin checks for the report's schedules.

Finite checks accompany, and do not replace, the uniform proofs. Small
lambda can legitimately require the theorem's exhaustive fallback. Large
symbolic margins avoid constructing integers with 10^12 bits.
"""
from __future__ import annotations

import argparse
from fractions import Fraction
import json
from math import isqrt
from pathlib import Path


def require(ok, message):
    if not ok:
        raise ArithmeticError(message)


def ceil_log2(n: int) -> int:
    if n < 1:
        raise ValueError("positive integer required")
    return (n - 1).bit_length()


def ceil_sqrt(n: int) -> int:
    q = isqrt(n)
    return q + (q*q != n)


def capacity(base: int, multiplier: int, lam: int) -> int:
    """Largest j with base^(multiplier*j) <= 2^lam, integer only."""
    if base < 2 or multiplier < 1 or lam < 0:
        raise ValueError("invalid capacity parameters")
    low, high = 0, lam // (multiplier*(base.bit_length()-1)) + 1
    target = 1 << lam
    while low + 1 < high:
        middle = (low + high)//2
        if pow(base, multiplier*middle) <= target:
            low = middle
        else:
            high = middle
    return low


def schedule(lam: int, kind: str, depth: int) -> dict:
    if lam < 1 or depth < 0:
        raise ValueError("positive lambda and nonnegative depth required")
    guard = ceil_sqrt(lam)
    buffer = ceil_log2(lam**6)
    if kind == "streaming":
        budget = max(0, (lam-guard)//80)
        u = [budget] + [(3*budget)//(4**d) for d in range(1, depth+1)]
        cap = 2*budget
    elif kind == "adaptive":
        budget = max(0, capacity(9, 20, lam)-guard)
        u = [budget//(2**d) for d in range(depth+1)]
        cap = 2*budget
    elif kind == "low_degree":
        budget = max(0, capacity(162, 1, lam)-guard)
        u = [(33*budget*17**d)//(50**(d+1)) for d in range(depth+1)]
        cap = budget
    else:
        raise ValueError("unknown schedule")
    a, partial = [], 0
    for d, value in enumerate(u):
        partial += value
        a.append(partial+(d+1)*buffer)
    require(sum(u) <= cap, "retained range exceeds its exact budget")
    return {"lambda":lam,"kind":kind,"depth":depth,"buffer":buffer,
            "inward_guard":guard,"budget":budget,"total_capacity":cap,
            "u":u,"a":a,"all_listed_u_positive":all(x>0 for x in u)}


def symbolic_margins(lam: int) -> dict:
    """Conservative exponent gaps using proven rational logarithm bounds."""
    h=ceil_log2(lam)
    depth=h+2  # deliberately exceeds each actual coarse depth bound
    g=ceil_sqrt(lam)
    buffer=ceil_log2(lam**6)
    G=(depth+1)*buffer
    # log2(9) in [3,16/5]; log2(162) in [7,37/5].
    # The extra 10 absorbs ceiling constants; 3h absorbs lambda^3 factors.
    stream_row=Fraction(g,10)-4*G-3*h-10
    stream_fresh=Fraction(31,40)*lam-9*G-3*h-10
    adaptive_row=6*g-Fraction(32,5)*G-3*h-10
    adaptive_fresh=Fraction(23,30)*lam-Fraction(37,5)*G-3*h-10
    low_packet=7*g-Fraction(37,5)*G-3*h-10
    low_original=Fraction(23,444)*lam-Fraction(32,5)*G-3*h-10
    values={"stream_retained_row":stream_row,"stream_fresh_and_rounding":stream_fresh,
            "adaptive_root_and_retained_row":adaptive_row,
            "adaptive_fresh_and_rounding":adaptive_fresh,
            "low_created_degree_and_rounding":low_packet,
            "low_original_degree":low_original}
    require(all(x>0 for x in values.values()), "sufficient symbolic margins fail")
    return {"lambda":lam,"hypothetical_depth_bound":depth,
            "lower_bounds_on_negative_base2_exponent":{k:str(v) for k,v in values.items()}}


def main():
    parser=argparse.ArgumentParser()
    parser.add_argument('--output',type=Path)
    args=parser.parse_args()
    capacities=[]
    for base,multiplier in [(9,20),(162,1),(13,10),(17,20)]:
        for lam in [1,8,64,256,1024,4096,16384]:
            value=capacity(base,multiplier,lam)
            target=1<<lam
            require(pow(base,multiplier*value)<=target,"capacity too large")
            require(pow(base,multiplier*(value+1))>target,"capacity not maximal")
            capacities.append({"base":base,"multiplier":multiplier,"lambda":lam,"capacity":value})
    require(9**5<2**16 and 9>=2**3,"log9 bounds")
    require(162**5<2**37 and 162>=2**7,"log162 bounds")
    schedules=[schedule(lam,kind,8) for lam in [256,4096,16384]
               for kind in ['streaming','adaptive','low_degree']]
    # Polynomial precision guard p/(MD/u)=O(lambda^4/2^b).
    for lam in [64,256,1024,4096]:
        b=ceil_log2(lam**6)
        require((1<<b)>=lam**6,"additive precision guard rounded down")
        require(Fraction(lam**4,1<<b)<=Fraction(1,lam**2),"precision guard")
    result={"status":"PASS","scope":"Exact capacities, floors, and conservative finite sufficient margins; the asymptotic proof is in the report.",
            "capacity_cases":capacities,"schedule_fixtures":schedules,
            "large_symbolic_margins":[symbolic_margins(10**12),symbolic_margins(10**14)],
            "fallback_note":"A zero retained range in a small fixture is expected and invokes direct contraction; no practical crossover is claimed."}
    payload=json.dumps(result,indent=2)+'\n'
    if args.output:
        args.output.parent.mkdir(parents=True,exist_ok=True)
        args.output.write_text(payload)
    print(payload)


if __name__=='__main__':
    main()
