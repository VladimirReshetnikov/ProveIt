"""Independent geometric checks on the normalization at all dilations 0..d."""
from collections import defaultdict
from math import factorial
from verify_ehrhart import normalized_coords


def side_counts(dimension, k):
    """Count vectors by signed sum and l1 length, then sum lengths <= k."""
    layer={(0,0):1}
    for _ in range(dimension):
        nxt=defaultdict(int)
        for (total,length),count in layer.items():
            budget=k-length
            for v in range(-budget,budget+1):
                nxt[total+v,length+abs(v)]+=count
        layer=nxt
    out=defaultdict(int)
    for (total,length),count in layer.items():
        out[total]+=count
    return out


def ehrhart_count(m,n,k):
    left=side_counts(m,k)
    right=side_counts(n,k)
    return sum(v*right[-j] for j,v in left.items())


def rotate(poly,degree,w):
    return sum(c*w**k*(-1)**((degree-k)//2)
               for k,c in enumerate(poly) if c)


def from_core(m,n,k):
    r=m-1
    a,b=normalized_coords(r,n)
    w=2*k+1
    qprev,q=1,w
    for j in range(1,n):
        qprev,q=q,w*q+j*j*qprev
    numerator=rotate(a,r,w)*q + rotate(b,r-1,w)*qprev
    denominator=4**r*factorial(n+r)
    assert numerator%denominator==0
    return numerator//denominator


if __name__=='__main__':
    if not __debug__:
        raise RuntimeError('Run without -O to enable certificate assertions')
    for m,n in ((2,2),(3,5),(6,6),(7,9)):
        d=m+n-1
        for k in range(d+1):
            assert from_core(m,n,k)==ehrhart_count(m,n,k)
        print(f'K({m},{n}): geometric and polynomial counts agree at all {d+1} interpolation points')
