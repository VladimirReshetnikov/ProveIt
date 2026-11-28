"""Check the rank-gain estimate on a finite rational representation (requires SymPy)."""
from itertools import combinations
from fractions import Fraction
from sympy import Matrix, Rational, eye, zeros

def hstack(blocks, n):
    return Matrix.hstack(*blocks) if blocks else zeros(n, 0)

def subspace(matrix):
    return hstack(matrix.columnspace(), matrix.rows)

def projector(basis):
    if basis.cols == 0:
        return zeros(basis.rows)
    return basis * (basis.T * basis).inv() * basis.T

def cyclic_group(d):
    result = []
    for shift in range(d):
        g = zeros(d + 1)
        for i in range(d):
            g[(i + shift) % d, i] = 1
        g[d, d] = 1
        result.append(g)
    return result

def finite_model():
    d, h = 8, 4
    group = cyclic_group(d)
    e = eye(d + 1)
    e[d, d] = 0
    P = eye(d + 1)[:, :h]
    P[0, 0], P[1, 1], P[d, 0] = Rational(5, 4), Rational(3, 4), Rational(1, 4)
    a = Rational(7, 16 * h)
    # The only eigenvalue of (eP)^*(eP) below one is 9/16.
    assert (e * P).T * (e * P) == Matrix.diag(Rational(25, 16), Rational(9, 16), 1, 1)
    A = sum((g * P * P.T * g.T for g in group), zeros(d + 1)) / d
    overlaps = [P.T * g * P for g in group]
    mean = sum((B.T * B).trace() for B in overlaps) / d
    assert (A * A).trace() == mean
    v = Rational(d, h*h) * mean - 1
    assert v > 0
    S = eye(h)[:, 0:3]
    S[3, 0] = 1
    r = 1 - Rational(S.cols, h)
    delta = v + 2 * a + 2 * r
    assert 0 < delta < 1
    images = [e * g * P * S for g in group]
    checked = 0
    for length in range(d + 1):
        for indices in combinations(range(d), length):
            prior = subspace(hstack([images[i] for i in indices], d + 1))
            F = projector(prior)
            u = 1 - Rational(prior.cols, d)
            mean_gain = 0
            for g, image in zip(group, images, strict=True):
                gain = hstack([prior, image], d + 1).rank() - prior.cols
                projected = F * g * P
                assert S.cols - gain <= a*h + (projected.T * projected).trace()
                mean_gain += gain
            mean_gain = Rational(mean_gain, d)
            assert (F*A).trace()**2 <= prior.cols * mean
            assert mean_gain >= h * (u-delta)/2
            checked += 1
    print(f"Rank bound verified for all {checked} translate subsets, including a proper ramified subspace.")
    print(f"Moment and losses are v={v}, a={a}, r={r}, Delta={delta}.")

def constants():
    b = 8
    assert 20 + Fraction(2, b**4) < 4*b*b
    assert 1 / (1 - Fraction(5, b**4)) <= 2
    for b in (2, 3, 8, 37):
        d = b**4 + 1
        assert d * Fraction(1, d-1) == 1 + Fraction(1, b**4)
    print("Endpoint constants and cyclic sharpness example checked.")

if __name__ == "__main__":
    finite_model()
    constants()
