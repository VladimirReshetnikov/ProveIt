"""Independent exponential Kauffman-bracket oracle for very small closed braids.

The result is the normalized Laurent polynomial in A (not in t). This oracle
is for regression cross-checking, not for certifying unknot from polynomial 1.
"""
from math import comb


def jones_braid(strands, word, max_crossings=14):
    if len(word) > max_crossings: raise ValueError('state-cube limit')
    m = len(word); coefficients = {}
    for mask in range(1 << m):
        parent = list(range((m+1)*strands))
        def find(a):
            while a != parent[a]:
                parent[a] = parent[parent[a]]; a = parent[a]
            return a
        def join(a, b):
            a, b = find(a), find(b)
            if a != b: parent[b] = a
        power = 0
        for stage, crossing in enumerate(word):
            i = abs(crossing)-1; cup = (mask >> stage) & 1
            power += (1 if crossing > 0 else -1) * (1-2*cup)
            top, bottom = stage*strands, (stage+1)*strands
            for j in range(strands):
                if not cup or j not in (i, i+1): join(top+j, bottom+j)
            if cup:
                join(top+i, top+i+1); join(bottom+i, bottom+i+1)
        for j in range(strands): join(j, m*strands+j)
        k = len({find(j) for j in range(len(parent))})-1
        for h in range(k+1):
            degree = power+2*k-4*h
            coefficients[degree] = coefficients.get(degree, 0)+(-1)**k*comb(k,h)
    writhe = sum(1 if x > 0 else -1 for x in word)
    return {e-3*writhe: ((-1)**writhe)*c for e,c in coefficients.items() if c}
