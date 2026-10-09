#!/usr/bin/env python3
"""Rigorous palette, parity, and finite Gaussian upper bounds for A275672.

All inequalities deciding an integer upper bound use exact integer/rational
arithmetic. The Gaussian certificate is proved and independently checked by
verify_gaussian_certificate.py. No external Python packages are required.
"""
from fractions import Fraction as F
from math import isqrt
import argparse, json

KAPPA = F(48755553510102913673137, 10**24)
SCALE = 10**60

def palette_bits(n):
    if n < 1:
        return 0
    squares = sum(1 << (j*j) for j in range(n))
    pairs = 0
    for j in range(n):
        pairs |= squares << (j*j)
    triples = 0
    for j in range(n):
        triples |= pairs << (j*j)
    return triples & ~1

def palette(n):
    bits=palette_bits(n)
    out=[]
    while bits:
        bit=bits & -bits
        out.append(bit.bit_length()-1)
        bits-=bit
    return out

def palette_and_parity_upper(n):
    if n==0:
        return {'n':0, 'distance_count':0, 'odd_distances':0,
                'palette_upper':0, 'parity_upper':0}
    bits=palette_bits(n)
    count=bits.bit_count()
    # Avoid quadratic repeated large-integer extraction for larger n.
    # Build alternating mask independently from its exact finite geometric sum.
    digits=(bits.bit_length()+1)//2
    odd_mask=2*((4**digits-1)//3)
    odd=(bits & odd_mask).bit_count()
    even=count-odd
    raw=(1+isqrt(1+8*count))//2
    upper=raw
    while not any(k*(upper-k)<=odd and
                  upper*(upper-1)//2-k*(upper-k)<=even
                  for k in range(upper//2+1)):
        upper-=1
    return {'n':n,'distance_count':count,'odd_distances':odd,
            'palette_upper':raw,'parity_upper':upper}

def ceildiv(a,b):
    return -((-a)//b)

def exp_negative_interval(x):
    """Outward rational enclosure of exp(-x), 0<=x<=64.

    Reduce to y=x/128<=1/2. Alternate Taylor degrees31 and30,
    then seven directed fixed-point squarings.
    """
    x=F(x)
    assert 0<=x<=64
    y=x/128
    pn=pd=fact=1
    lo=hi=0
    for k in range(32):
        if k:
            pn*=y.numerator; pd*=y.denominator; fact*=k
        a=SCALE*pn; b=pd*fact
        lower=a//b; upper=ceildiv(a,b)
        if k%2:
            lo-=upper
            if k<=30: hi-=lower
        else:
            lo+=lower
            if k<=30: hi+=upper
    assert 0<lo<=hi<=SCALE
    for _ in range(7):
        lo=lo*lo//SCALE; hi=ceildiv(hi*hi,SCALE)
    return F(lo,SCALE),F(hi,SCALE)

def infinite_admissible_laplace_upper(n):
    """Upper bound for sum_{r admissible, r>=1} exp(-10*r/(n-1)^2).

    Excluded classes 4^a(8b+7) are disjoint. Subtract any finite
    number of their infinite geometric series from the all-integer series.
    """
    assert n>=2
    delta=F(10,(n-1)**2)
    _,qhi=exp_negative_interval(delta)
    if qhi >= 1:
        raise ArithmeticError("Increase SCALE to resolve the exponential interval.")
    result=qhi/(1-qhi)
    power=1
    classes=0
    # Once an excluded class starts past exponent56, remaining classes
    # may simply be left unsubtracted: this enlarges the upper bound.
    while 7*delta*power<=56:
        numlo,_=exp_negative_interval(7*delta*power)
        denqlo,_=exp_negative_interval(8*delta*power)
        result-=numlo/(1-denqlo)
        power*=4; classes+=1
    assert result>0
    return result,classes

def gaussian_upper(n):
    if n<=1:
        return n,0
    w,classes=infinite_admissible_laplace_upper(n)
    # Largest integer satisfying kappa*m^2-m <= 2*w. Monotonic for m>=11.
    lo=0; hi=max(32,3*n+100)
    while KAPPA*hi*hi-hi<=2*w:
        hi*=2
    while lo+1<hi:
        mid=(lo+hi)//2
        if KAPPA*mid*mid-mid<=2*w:lo=mid
        else:hi=mid
    return lo,classes

def row(n):
    r=palette_and_parity_upper(n)
    r['gaussian_upper'],r['excluded_classes_subtracted']=gaussian_upper(n)
    r['combined_upper']=min(r['parity_upper'],r['gaussian_upper'])
    return r

if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('n',type=int,nargs='*',default=list(range(31)))
    p.add_argument('--output')
    args=p.parse_args()
    assert all(n>=0 for n in args.n)
    rows=[row(n) for n in args.n]
    value=json.dumps(rows,indent=2)+'\n'
    if args.output:
        with open(args.output,'w') as f:f.write(value)
    print(value)
