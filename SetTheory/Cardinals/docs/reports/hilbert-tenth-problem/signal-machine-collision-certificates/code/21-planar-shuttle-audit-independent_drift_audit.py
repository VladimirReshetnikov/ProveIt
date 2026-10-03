#!/usr/bin/env python3
"""Independent checks of vertical drift and exact original-rule arrival times."""
from math import isqrt
from independent_audit import PATS, component_step, norm, sub, section, T, formula_visited

def A(k, N):
    alpha = 2 * k - 10
    return max(0, (isqrt(alpha * alpha + 4 * (N + 1)) - alpha) // 2)

def B(k, N):
    beta = 2 * k - 9
    return max(0, 1 + (isqrt(beta * beta + 4 * (N - k + 5)) - beta) // 2)

def C(k, N):
    return 4 * (N + 1) - 3 * A(k, N) - B(k, N)

def arrival(k, n, x):
    K = k + n
    if x in {0, 3, 4}:
        return T(k, n)
    if x == K:
        return 0 if n == 0 else T(k, n) - (K - 6)
    if x == 2:
        return T(k, n) + 2 * K - 11
    if not 5 <= x <= K - 2:
        raise RuntimeError('Audit check failed: 5 <= x <= K - 2')
    return T(k, n) + x - 4

def main():
    for name, (P, Q) in PATS.items():
        if not max((norm(sub(p, (r[0], r[1] + 1))) for p in P for r in P | Q)) + 2 <= 6:
            raise RuntimeError('Audit check failed: max((norm(sub(p, (r[0], r[1] + 1))) for p in P for r in P | Q)) + 2 <= 6')
    comparisons = 0
    for k in range(7, 41):
        Nmax = 700
        S = section(k, 0)
        trace = set()
        first = {}
        hist = [0] * (Nmax + 1)
        for t in range(Nmax + 1):
            shifted = {(x, y + t) for x, y in S}
            if not not shifted & trace:
                raise RuntimeError((k, t, 'visited-site intersection'))
            trace |= shifted
            for x, y in shifted:
                if not x <= max(k + 1, y):
                    raise RuntimeError((k, t, x, y, 'horizontal bound'))
                if max(x, y) <= Nmax:
                    hist[max(x, y)] += 1
            for p in S:
                first.setdefault(p, t)
            S = component_step(S)
        count = 0
        for N, delta in enumerate(hist):
            count += delta
            if N >= k + 1:
                if not count == C(k, N):
                    raise RuntimeError((k, N, count, C(k, N)))
                if not A(k, N) == sum((n * n + (2 * k - 10) * n - 1 <= N for n in range(1, N + 2))):
                    raise RuntimeError('Audit check failed: A(k, N) == sum((n * n + (2 * k - 10) * n - 1 <= N for n in range(1, N + 2)))')
                if not B(k, N) == sum((n * n + (2 * k - 9) * n + k - 5 <= N for n in range(N + 2))):
                    raise RuntimeError('Audit check failed: B(k, N) == sum((n * n + (2 * k - 9) * n + k - 5 <= N for n in range(N + 2)))')
                comparisons += 1
        n = 0
        while T(k, n + 1) <= Nmax:
            for x, y in formula_visited(k, n):
                if not first[x, y] == arrival(k, n, x):
                    raise RuntimeError((k, n, x, first[x, y], arrival(k, n, x)))
            n += 1
    print(f'PASS: 34 drifted orbits for 701 states each; {comparisons} exact centered-box counts; square-root floor formulas; disjoint traces; horizontal cutoff; original-rule first arrivals; drifted radius ≤6.')
if __name__ == '__main__':
    main()
