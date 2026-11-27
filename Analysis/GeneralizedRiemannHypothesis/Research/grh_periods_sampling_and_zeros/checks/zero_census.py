#!/usr/bin/env python3
"""Exact rational check of the two spectral scales, using only Python 3."""
from fractions import Fraction as Q
from math import isqrt


def multiply(f, g):
    product = [Q(0)] * (len(f) + len(g) - 1)
    for i, a in enumerate(f):
        for j, b in enumerate(g):
            product[i + j] += a * b
    return product


def logarithmic_moments(f, nmax):
    """Coefficients of -z f'(z)/f(z), by formal power-series division."""
    b = [Q(0)]
    for n in range(1, nmax + 1):
        rhs = -n * f[n] if n < len(f) else Q(0)
        for j in range(1, min(n, len(f) - 1) + 1):
            rhs -= f[j] * b[n-j]
        b.append(rhs / f[0])
    return b


def inertia(matrix):
    """Exact symmetric elimination. A zero diagonal permits a 2 by 2 pivot."""
    a = [row[:] for row in matrix]
    pos = neg = 0
    while a:
        n = len(a)
        p = next((i for i in range(n) if a[i][i]), None)
        if p is not None:
            a[0], a[p] = a[p], a[0]
            for row in a:
                row[0], row[p] = row[p], row[0]
            v = a[0][0]
            pos += int(v > 0)
            neg += int(v < 0)
            a = [[a[i][j] - a[i][0] * a[0][j] / v
                  for j in range(1, n)] for i in range(1, n)]
            continue
        pair = next(((i, j) for i in range(n) for j in range(i) if a[i][j]), None)
        if pair is None:
            break
        i, j = pair
        rest = [r for r in range(n) if r not in pair]
        v = a[i][j]
        a = [[a[r][s] - (a[r][i] * a[j][s] + a[r][j] * a[i][s]) / v
              for s in rest] for r in rest]
        pos += 1
        neg += 1
    return pos, neg


def outliers(h, cutoff):
    plus = [row[:] for row in h]
    minus = [row[:] for row in h]
    for j in range(len(h)):
        plus[j][j] -= cutoff
        minus[j][j] += cutoff
    return inertia(plus)[0], inertia(minus)[1]


def squarefree_part(f):
    def divmod_poly(a, b):
        a = a[:]
        q = [Q(0)] * max(1, (len(a) - len(b) + 1))
        while a and len(a) >= len(b):
            n = len(a) - len(b)
            c = a[-1] / b[-1]
            q[n] = c
            for i, v in enumerate(b):
                a[n+i] -= c * v
            while a and a[-1] == 0:
                a.pop()
        return q, a

    a, b = f, [j * f[j] for j in range(1, len(f))]
    while b:
        _, rem = divmod_poly(a, b)
        a, b = b, rem
    q, rem = divmod_poly(f, a)
    assert not rem
    return [c / q[0] for c in q]


def gram_inverse(q, d):
    # H = W B W^T with B its leading square block. W extends any moment
    # sequence by the distinct-root recurrence given by the denominator q.
    r = len(q)-1
    w = [[Q(i == j) for j in range(r)] for i in range(r)]
    for i in range(r, d):
        w.append([-sum(q[l]*w[i-l][j] for l in range(1,r+1)) for j in range(r)])
    g = [[sum(row[i]*row[j] for row in w) for j in range(r)]
         + [Q(i == j) for j in range(r)] for i in range(r)]
    for i in range(r):
        g[i] = [v/g[i][i] for v in g[i]]
        for j in range(r):
            if j != i:
                coeff = g[j][i]
                g[j] = [v-coeff*u for v,u in zip(g[j],g[i])]
    return [row[r:] for row in g]


def compact_outliers(b, inv, t):
    # The nonzero eigenvalues of H are those of G^(1/2) B G^(1/2),
    # where G = W^T W, hence inertia after subtracting t G^(-1) suffices.
    pos = inertia([[v-t*ij for v,ij in zip(row, gr)] for row,gr in zip(b, inv)])[0]
    neg = inertia([[v+t*ij for v,ij in zip(row, gr)] for row,gr in zip(b, inv)])[1]
    return pos, neg


def run():
    # Interior: 1/2 (twice), ±i/2. Boundary: 1 (three times), ±i (twice).
    # Exterior: 2. Only the expanded coefficients feed the moment recurrence.
    f = [Q(1)]
    for factor, multiplicity in [([1,-2],2), ([1,0,4],1), ([1,-1],3),
                                 ([1,0,1],2), ([1,Q(-1,2)],1)]:
        for _ in range(multiplicity):
            f = multiply(f, factor)
    print("k     d    +/- above k, d/2, 3d/2, 5d/2, 7d/2")
    q = squarefree_part(f)
    r = len(q)-1
    for k in (16, 64, 144, 256, 1024, 2304):
        d = isqrt(k)
        n = min(d,r)
        moments = logarithmic_moments(f, 2*k+2*n-2)
        h = [[moments[2*k+i+j] for j in range(n)] for i in range(n)]
        cuts = (k, Q(d,2), Q(3*d,2), Q(5*d,2), Q(7*d,2))
        if d <= r:
            counts = [outliers(h, t) for t in cuts]
        else:
            inv = gram_inverse(q, d)
            counts = [compact_outliers(h, inv, t) for t in cuts]
        if k == 64:
            raw = logarithmic_moments(f, 2*k+2*d-2)
            full = [[raw[2*k+i+j] for j in range(d)] for i in range(d)]
            assert counts == [outliers(full, t) for t in cuts]
        print(f"{k:<5} {d:<4} {counts}", flush=True)
        if k == 2304:
            assert counts == [(2,1), (4,2), (4,2), (3,1), (2,1)]



def check_boundary_angles():
    # Four conjugation orbits, all of multiplicity three. Since all distinct
    # nodes are 12th roots of unity, the recurrence rows repeat every 12.
    f = [Q(1)]
    for factor in ([1,-1], [1,1], [1,0,1], [1,-1,1]):
        for _ in range(3):
            f = multiply(f, factor)
    recurrence = squarefree_part(f)
    r = len(recurrence)-1
    sample = logarithmic_moments(f, 36)
    assert sample[1:25] == sample[13:37]
    period = sample[1:13]
    d = 12**4
    k = d*d
    weight = Q(1,12)

    def b(n):
        return period[(n-1)%12]

    h = [[b(2*k+i+j)+weight*b(2*k+i+j+1)
          for j in range(r)] for i in range(r)]
    inv = [[v*Q(12,d) for v in row] for row in gram_inverse(recurrence,12)]
    print("real part   positive/negative eigenvalues in angular band")
    for x, real in [(-1,True), (0,False), (Q(1,2),False), (1,True)]:
        middle = 3*d*(1+weight*x)
        radius = 3*d*weight**2
        lo = compact_outliers(h, inv, middle-radius)
        hi = compact_outliers(h, inv, middle+radius)
        band = tuple(a-b for a,b in zip(lo,hi))
        assert band == (1, int(not real))
        print(f"{str(x):<11} {band}")


if __name__ == "__main__":
    run()
    check_boundary_angles()
