"""Exact double norm for phi_9(1+T), T^2+pi*T+pi and pi^3=3."""
from itertools import product
from math import comb


def multiply_pi(a, b):
    c = [0, 0, 0]
    for i, j in product(range(3), repeat=2):
        c[(i+j) % 3] += (3 if i+j >= 3 else 1) * a[i] * b[j]
    return tuple(c)


def add(a, b):
    return tuple(x+y for x, y in zip(a, b))


def neg(a):
    return tuple(-x for x in a)


def det(mat):
    if len(mat) == 1:
        return mat[0][0]
    d = (0, 0, 0)
    for j, c in enumerate(mat[0]):
        minor = [row[:j] + row[j+1:] for row in mat[1:]]
        v = multiply_pi(c, det(minor))
        d = add(d, neg(v) if j % 2 else v)
    return d


if __name__ == '__main__':
    # In Z[pi,T]/(Phi_9(1+T)), act by multiplication by T^2+pi*T+pi.
    phi = [sum(comb(k,j) for k in (0,3,6) if j<=k) for j in range(7)]
    rows = [[(0,0,0) for _ in range(6)] for _ in range(6)]
    for j in range(6):
        col = [(0,0,0)] * j + [(0,1,0),(0,1,0),(1,0,0)] + [(0,0,0)] * 6
        for i in range(7,5,-1):
            for t, coeff in enumerate(phi[:6]):
                col[i-6+t] = add(col[i-6+t], tuple(-coeff*k for k in col[i]))
        for i in range(6):
            rows[i][j] = col[i]
    norm1 = det(rows)
    a,b,c = norm1
    # Norm of a + b*pi + c*pi^2 for pi^3=3.
    norm = a**3 + 3*b**3 + 9*c**3 - 9*a*b*c
    print("Norm to Q3(pi), coefficients on 1,pi,pi^2:",norm1)
    print("Norm to Q3:",norm)
    assert norm == 3**10
