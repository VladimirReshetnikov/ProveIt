"""Exact finite checks for natural versus upper density. Standard library only."""
from fractions import Fraction as Q
from itertools import combinations

def binary_product(a, b):
    result = 0
    while b:
        if b & 1:
            result ^= a
        a <<= 1
        b >>= 1
    return result

def binary_cutoffs():
    square_roots = {binary_product(a, a): a for a in range(1, 16)}
    edges = []
    for a, c in combinations(range(1, 16), 2):
        b = square_roots.get(binary_product(a, c))
        if b is not None:
            edges.append(sum(1 << (i-1) for i in (a,b,c)))
    feasible = [mask for mask in range(1 << 15)
                if all(mask & edge != edge for edge in edges)]
    maxima = []
    for degree in range(4):
        low = (1 << (2**(degree+1)-1)) - 1
        maxima.append(max((mask & low).bit_count() for mask in feasible))
    nested = [mask for mask in feasible if (mask & 7).bit_count() == 3
              and (mask & 127).bit_count() == 5]
    assert maxima == [1,3,5,12]
    assert max(mask.bit_count() for mask in nested) == 11
    print('Binary ball optima:', maxima, 'best final size preserving first three:', 11)

def quantitative(q, T):
    counts = {}
    rough_density = Q(1)
    for d in range(1,T+1):
        numerator = q**d - sum(e*n for e,n in counts.items() if d % e == 0)
        assert numerator % d == 0
        counts[d] = numerator // d
        rough_density *= (1-Q(1,q**d))**counts[d]
    return (1-Q(1,q))*rough_density/q**3-Q(1,(T+1)*(q-1)*q**T)

if __name__ == '__main__':
    binary_cutoffs()
    for q,T,bound in [(2,8,3660),(3,5,2149),(4,4,1192),(5,4,715),(7,4,297)]:
        assert quantitative(q,T)>Q(bound,10**6)
        print(f'q={q}, T={T}: gap > {bound}/1000000')
