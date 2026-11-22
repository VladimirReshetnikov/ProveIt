"""Exact enclosure of the period and dyadic checks for a square-root modulus."""
from fractions import Fraction as Q
from math import isqrt

def period(m):
    # Imaginary part of the increment on the positively oriented diamond.
    nodes = [Q(2*j+1,2*m) for j in range(m)]
    den = lambda u: (1-u)**2 + u*u
    real = sum((2*u-1)/den(u) for u in nodes)
    assert real == 0
    mid = 4*sum(1/den(u) for u in nodes)/m
    width = Q(16,m)
    return max(Q(4),mid-width), min(Q(8),mid+width), mid

def lower_sqrt(x,k):
    a = (x.numerator * (1<<(2*k))) // x.denominator
    return Q(isqrt(a),1<<k)

def main():
    low,high,mid = period(128)
    l2,h2,med = period(256)
    assert low<=l2<=h2<=high and 4<low<high<8
    print("Im(period) in",float(l2),float(h2),"(endpoints displayed as decimals)")
    # The exact inequalities below, rather than the rounded display, are tested.
    assert Q(62,10)<l2<h2<Q(64,10)
    for n in range(5):
        scale = 1<<(2*n+4)
        for i in range(0,scale):
            x,y = Q(i,scale),Q(i+1,scale)
            for k in (n+2,n+5):
                for ell in (n+2,n+4):
                    assert abs(lower_sqrt(x,k)-lower_sqrt(y,ell)) <= Q(1,1<<n)
    print("square-root demand tested for all adjacent grid pairs, n=0..4")

if __name__ == "__main__":
    main()
