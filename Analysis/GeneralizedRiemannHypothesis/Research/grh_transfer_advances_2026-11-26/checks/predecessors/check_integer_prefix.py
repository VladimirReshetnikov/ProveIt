"""Compute the loss from requiring one set to work at every prefix."""
from fractions import Fraction
from functools import lru_cache
from itertools import combinations
from math import isqrt, lcm

def all_edges(N, rational):
    triples = []
    for i,k in combinations(range(1,N+1),2):
        j = isqrt(i*k)
        if j*j == i*k and (rational or j % i == 0):
            triples.append((i,j,k))
    return triples

def max_weight(N, weights, edges):
    """Minimum-weight vertex cover by branching on an uncovered triple."""
    incident = [0]*(N+1)
    for i,triple in enumerate(edges):
        for v in triple:
            incident[v] |= 1<<i
    @lru_cache(None)
    def cover(mask):
        if not mask:
            return 0
        low = mask & -mask
        triple = edges[low.bit_length()-1]
        return min(weights[v]+cover(mask & ~incident[v]) for v in triple)
    return sum(weights)-cover((1<<len(edges))-1)

def deficit(N, rational):
    triples = all_edges(N,rational)
    prefix = sum(Fraction(max_weight(k,[0]+[1]*k,
                         [e for e in triples if e[-1]<=k]),k*(k+1))
                 for k in range(1,N+1))
    denom = lcm(*range(1,N+2))
    weights = [0]+[denom//a-denom//(N+1) for a in range(1,N+1)]
    return prefix-Fraction(max_weight(N,weights,triples),denom)

def primes_upto(n):
    sieve = bytearray([1])*(n+1)
    for p in range(2,isqrt(n)+1):
        if sieve[p]:
            sieve[p*p::p] = bytes((n-p*p)//p+1)
    return [p for p in range(2,n+1) if sieve[p]]

def lower_gap(loss,Y):
    ceiling = 100000
    scale = 10**12
    product = Fraction(1)
    upper_tail = Fraction(1,ceiling)
    for p in primes_upto(ceiling):
        if p<=Y:
            product *= Fraction(p-1,p)
        else:
            upper_tail += Fraction((scale+p*p-1)//(p*p),scale)
    return product*loss-upper_tail

if __name__=='__main__':
    for rational in (True,False):
        N,Y = 80,(293 if rational else 83)
        loss=deficit(N,rational)
        bound=lower_gap(loss,Y)
        print('rational ratios' if rational else 'integer ratios')
        assert loss == (Fraction(1553,45360) if rational else Fraction(16567,132300))
        assert bound > Fraction(2836 if rational else 13336,10**6)
        print(f'N={N}, exact prefix deficit: {loss}')
        print(f'Y={Y}, gap strictly exceeds {int(bound*10**6)}/1000000')
