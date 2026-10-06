#!/usr/bin/env python3
"""Exact iterated Euler transforms; Python 3.11+, standard library only."""
import argparse
import json
from math import comb

MAX_INDEX=640

def bounded_index(n):
    if isinstance(n,bool) or not isinstance(n,int) or not 0 <= n <= MAX_INDEX:
        raise ValueError('index/height must be an integer from 0 to 640')
    return n

def decimal(value):
    """Render an integer locally without changing the global digit limit."""
    if isinstance(value,bool) or not isinstance(value,int):
        raise ValueError('integer required')
    if value == 0: return '0'
    sign='-' if value<0 else ''; value=abs(value); chunks=[]
    while value:
        value,part=divmod(value,10**9);chunks.append(part)
    return sign+str(chunks[-1])+''.join(f'{v:09d}' for v in reversed(chunks[:-1]))

def validate_row(row):
    if not isinstance(row,list) or not row:
        raise ValueError('nonempty coefficient list required')
    bounded_index(len(row)-1)
    if row[0] != 0 or any(isinstance(v,bool) or not isinstance(v,int) or v<0 for v in row):
        raise ValueError('F row must have constant zero and nonnegative integer entries')

def euler_step(row):
    """Return F_{h+1} coefficients from those of F_h at the same degree."""
    validate_row(row); N=len(row)-1; divisor=[0]*(N+1)
    for d in range(1,N+1):
        v=d*row[d]
        for j in range(d,N+1,d): divisor[j]+=v
    nxt=[1]+[0]*N
    for n in range(1,N+1):
        value=sum(divisor[j]*nxt[n-j] for j in range(1,n+1))
        quotient,remainder=divmod(value,n)
        if remainder: raise ArithmeticError('Euler division is not integral')
        nxt[n]=quotient
    nxt[0]=0
    return nxt

def product_step(row):
    """Independent finite product method, intentionally capped at degree 20."""
    validate_row(row); N=len(row)-1
    if N>20: raise ValueError('independent product implementation is capped at degree 20')
    result=[1]+[0]*N
    for d in range(1,N+1):
        exponent=row[d]
        if not exponent: continue
        factor=[comb(exponent+k-1,k) for k in range(N//d+1)]
        out=[0]*(N+1)
        for a,v in enumerate(result):
            for k in range((N-a)//d+1): out[a+k*d]+=v*factor[k]
        result=out
    result[0]=0
    return result

def coefficients(degree,height):
    """F_height through degree; the ordinary constant term is zero."""
    bounded_index(degree);bounded_index(height)
    row=[0]*(degree+1)
    if degree: row[1]=1
    for _ in range(height): row=euler_step(row)
    return row

def diagonal(limit):
    """A290354, including its separate a_0=1 convention."""
    bounded_index(limit);row=[0]*(limit+1);out=[1]
    if limit: row[1]=1
    for height in range(1,limit+1):
        row=euler_step(row);out.append(row[height])
    return out

def array_entry(n,m):
    """A290353 A(n,m), with conventional A(0,m)=1."""
    bounded_index(n);bounded_index(m)
    return 1 if n==0 else coefficients(n,m)[n]

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--max-index',type=int,default=20)
    ap.add_argument('--height',type=int,help='print A(n,height), n=0..max-index')
    args=ap.parse_args()
    try:
        if args.height is None:
            result={'sequence':'A290354','max_index':args.max_index,
                    'values':[decimal(x) for x in diagonal(args.max_index)]}
        else:
            row=coefficients(args.max_index,args.height);row[0]=1
            result={'array':'A290353','height':args.height,'max_index':args.max_index,
                    'values':[decimal(x) for x in row]}
    except ValueError as exc: ap.error(str(exc))
    print(json.dumps(result,sort_keys=True,indent=2))

if __name__=='__main__': main()
