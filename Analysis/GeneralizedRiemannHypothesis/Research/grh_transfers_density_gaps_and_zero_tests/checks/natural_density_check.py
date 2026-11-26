"""Exact checks of the smoothness estimate and small weighted signed-step optima."""
from fractions import Fraction
from itertools import combinations, product


def smooth_check(q, max_degree):
    # I[d] from the unique factorization identity q^d = sum_(k|d) k I[k].
    I = [0]
    for d in range(1, max_degree + 1):
        I.append((q**d - sum(k * I[k] for k in range(1, d) if d % k == 0)) // d)
    cases = 0
    for m in range(1, max_degree + 1):
        # Add I[m] geometric-series factors via their logarithmic derivative.
        rates = [sum(d * I[d] for d in range(1, m + 1) if k % d == 0)
                 for k in range(max_degree + 1)]
        counts = [1]
        for k in range(1, max_degree + 1):
            numer = sum(rates[i] * counts[k-i] for i in range(1, k+1))
            assert numer % k == 0
            counts.append(numer // k)
        probs = [Fraction(x, q**d) for d, x in enumerate(counts)]
        for k in range(1, max_degree + 1):
            assert m * abs(probs[k] - probs[k-1]) <= 1
            cases += 1
    return cases


def ternary(n):
    while n:
        if n % 3 == 2:
            return False
        n //= 3
    return True


def weighted(q, L, degrees=(1,1)):
    # Smooth exponent vectors in the degree cutoff. Multiply every weight by q^L.
    def vectors(ds, budget):
        if not ds:
            yield ()
            return
        for k in range(budget//ds[0]+1):
            for v in vectors(ds[1:], budget-k*ds[0]):
                yield (k,)+v
    def total(v):
        return sum(a*b for a,b in zip(degrees,v))
    pts = sorted(vectors(degrees,L), key=total)
    indices = {v: i for i, v in enumerate(pts)}
    links = [[] for _ in pts]
    for a, c in combinations(pts, 2):
        summed = tuple(x+y for x, y in zip(a, c))
        if any(x % 2 for x in summed):
            continue
        b = tuple(x//2 for x in summed)
        i, j, k = sorted(indices[x] for x in [a, b, c])
        links[j].append((1 << i, 1 << k))
    weights = [q**(L-total(v)) for v in pts]
    greedy = sum(w for v,w in zip(pts,weights) if all(map(ternary,v)))
    best = greedy
    def branch(taken, available, score, potential):
        nonlocal best
        if potential <= best:
            return
        if not available:
            best = score
            return
        bit = available & -available
        i = bit.bit_length() - 1
        rest = available ^ bit
        removed = 0
        for earlier, later in links[i]:
            if earlier & taken:
                removed |= later
        removed &= rest
        with_i_potential = potential
        without_removed = rest ^ removed
        while removed:
            b = removed & -removed
            with_i_potential -= weights[b.bit_length()-1]
            removed ^= b
        branch(taken|bit, without_removed, score+weights[i], with_i_potential)
        branch(taken, rest, score, potential-weights[i])
    branch(0, (1 << len(pts))-1, 0, sum(weights))
    return greedy, best

if __name__ == '__main__':
    for q in [2, 3, 4, 5]:
        print(f'q={q}, smoothness comparisons passed: {smooth_check(q,48)}')
    for q, L in product([2,3], range(2,9)):
        g,b = weighted(q,L)
        print(f'q={q}, two linear primes, degree <= {L}, scaled greedy={g}, optimum={b}')

    degrees, L, q = (1,1,2), 12, 2
    greedy, optimum = weighted(q,L,degrees)
    assert optimum == greedy == 14853
    counts = [1]+[0]*L
    normalizer = Fraction(1)
    for d in degrees:
        normalizer *= 1-Fraction(1,q**d)
        for n in range(d,L+1):
            counts[n] += counts[n-d]
    bound = 1-normalizer*(sum(Fraction(v,q**n) for n,v in enumerate(counts))-
                          Fraction(optimum,q**L))
    assert bound == Fraction(2797,4096)
    print(f'For q=2, degree <=12 weighted optimum 14853/4096 gives b <= {bound}.')
