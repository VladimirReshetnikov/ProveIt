#!/usr/bin/env python3
"""Evaluate Rudin--Shapiro correlations and certified peak locations.

The maximizer formula relies on the theorem and exact certificate in article.pdf.
This module uses only Python integers and the standard library.
"""
from __future__ import annotations
from dataclasses import dataclass
import argparse
import json
import sys
from typing import Tuple

U = ((1,0,2),(-1,0,2),(0,1,0))
V = ((0,1,0),(0,-1,0),(1,0,0))
BASE = (1,-1,1)
EXCEPTION_DELTAS = {3:-2,5:-8,7:-34,8:2,9:22,10:8,12:34,13:86,
                    14:136,15:-8,17:1110,19:4352,20:2,22:8,24:34,
                    25:-2,27:-8,29:-34,32:2,34:8,39:-2}

def _level(m: int) -> None:
    if isinstance(m,bool) or not isinstance(m,int) or m<1:
        raise ValueError('The level must be a positive integer.')

def _mv(a,v):
    return tuple(sum(x*y for x,y in zip(row,v)) for row in a)

def _mm(a,b):
    return tuple(tuple(sum(a[i][k]*b[k][j] for k in range(3))
                       for j in range(3)) for i in range(3))

def _power_apply(a,n,v):
    while n:
        if n&1:
            v=_mv(a,v)
        a=_mm(a,a)
        n>>=1
    return v

def autocorrelation(m: int,k: int) -> int:
    """Return C_m(k) exactly, including the main lobe and negative shifts."""
    _level(m)
    if isinstance(k,bool) or not isinstance(k,int):
        raise ValueError('The shift must be an integer.')
    k=abs(k)
    if k==0:
        return 1<<m
    if k >= 1<<m:
        return 0
    if k%2==0:
        return 0
    if m==1:
        return 1
    coordinate=int(k > 1<<(m-1))
    if coordinate:
        k=(1<<m)-k
    outer=[]
    for level in range(m,2,-1):
        if k < 1<<(level-2):
            outer.append(V)
        else:
            outer.append(U)
            k=(1<<(level-1))-k
    if k!=1:
        raise RuntimeError('Internal address invariant failed.')
    state=BASE
    for matrix in reversed(outer):
        state=_mv(matrix,state)
    return state[coordinate]

@dataclass(frozen=True)
class Maximum:
    level: int
    value: int
    shifts: Tuple[int,...]
    correlations: Tuple[int,...]

def maximum(m: int) -> Maximum:
    """Return the peak sidelobe level and every positive maximizing shift.

    For m >= 40, the peak value uses O(log m) 3x3 integer matrix products.
    The bit cost must also include the size of the resulting integers.
    """
    _level(m)
    if m==1:
        return Maximum(1,1,(1,),(1,))
    if m==2:
        return Maximum(2,1,(1,3),(1,-1))
    shift=((1<<(m+1))+(-1)**m)//3+EXCEPTION_DELTAS.get(m,0)
    value=(_power_apply(U,m-2,BASE)[1] if m>=40
           else autocorrelation(m,shift))
    return Maximum(m,abs(value),(shift,),(value,))

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('level',type=int)
    parser.add_argument('--shift',type=int,help='evaluate a specified shift instead')
    args=parser.parse_args()
    # Explicit large-index evaluation may legitimately exceed Python's
    # default decimal-conversion limit. This CLI handles locally computed integers.
    if hasattr(sys,'set_int_max_str_digits'):
        sys.set_int_max_str_digits(0)
    if args.shift is not None:
        print(autocorrelation(args.level,args.shift))
    else:
        result=maximum(args.level)
        print(json.dumps(result.__dict__,indent=2))

if __name__=='__main__':
    try:
        main()
    except (ValueError,RuntimeError) as error:
        print(f'ERROR: {error}',file=sys.stderr)
        sys.exit(1)
