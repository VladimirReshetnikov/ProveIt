"""Reproduce the exact finite calculations in the graph-tower section (Python 3)."""

from collections import Counter
from math import isqrt


def is_prime(n):
    return n >= 2 and all(n % d for d in range(2, isqrt(n) + 1))


def quartic_point(p):
    """A point of sum x_i^2 = sum x_i^4 = 0, or None after exhaustive search."""
    squares = {x * x % p: x for x in range(p)}
    # By permutation symmetry and homogeneity, set a nonzero coordinate to 1.
    for y in range(p):
        a = y * y % p
        for z in range(p):
            b = z * z % p
            c = (-1 - a - b) % p
            if c in squares and (1 + a*a + b*b + c*c) % p == 0:
                return 1, y, z, squares[c]
    return None


def depth_histogram(p, steps):
    counts = Counter()
    directions = [(1, t) for t in range(p)] + [(0, 1)]
    for a, b in directions:
        squares = [(a*x + b*y)**2 % p for x, y in steps]
        for j in range(1, len(steps) + 1):
            if sum(pow(x, j, p) for x in squares) % p:
                counts[j] += 1
                break
        else:
            raise ValueError("Step list fails to span or p is too small")
    return dict(sorted(counts.items()))


def four_step_a_max(p):
    """Every spanning isotropic plane has the normal form in the text."""
    coefficients = []
    for a in range(p):
        for b in range(p):
            if (1 + a*a + b*b) % p == 0:
                steps = ((1, 0), (0, 1), (a, b), (b, -a))
                hist = depth_histogram(p, steps)
                coefficients.append(2 * sum(k*v for k, v in hist.items()))
    return max(coefficients)


def level_one_tree_count(p, steps):
    """Exact cofactor using fraction-free elimination, independently of moments."""
    size = p*p - 1
    mat = [[0]*size for _ in range(size)]
    for x in range(p):
        for y in range(p):
            i = p*x + y
            for a, b in steps:
                j = p*((x+a) % p) + (y+b) % p
                if i < size:
                    mat[i][i] += 1
                if j < size:
                    mat[j][j] += 1
                if i < size and j < size:
                    mat[i][j] -= 1
                    mat[j][i] -= 1
    previous = 1
    for k in range(size-1):
        pivot = mat[k][k]
        assert pivot > 0
        for i in range(k+1, size):
            entry = mat[i][k]
            for j in range(k+1, size):
                mat[i][j] = (pivot*mat[i][j]-entry*mat[k][j]) // previous
            mat[i][k] = 0
        previous = pivot
    return mat[-1][-1]


def main():
    exceptions = {11, 23, 29, 47, 53, 83, 149}
    primes = [p for p in range(11, 323) if is_prime(p) and p % 8 != 1]
    point_free = set()
    print("Normalized witnesses on the (2,4) intersection")
    for p in primes:
        point = quartic_point(p)
        print(f"p={p:3}  {point}")
        if point is None:
            point_free.add(p)
        else:
            assert all(sum(x**j for x in point) % p == 0 for j in (2, 4))
    assert len(primes) == 49 and point_free == exceptions
    print("Point-free primes:", sorted(point_free))
    print("Independent exhaustive four-step plane maxima")
    for p in (11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47):
        maximum = four_step_a_max(p)
        excess = 16 if p % 8 == 1 else (0 if p in exceptions else 8)
        assert maximum == 4*(p+1) + excess
        print(f"p={p:3}  maximum A={maximum}")
    steps = [(1, 0), (4, 0), (3, 0), (0, 1), (0, 4), (0, 3)]
    hist = depth_histogram(13, steps)
    assert hist == {3: 8, 6: 6}
    count = level_one_tree_count(13, steps)
    valuation = 0
    while count % 13 == 0:
        count //= 13
        valuation += 1
    assert valuation == 118
    print("p=13 six-step histogram:", hist)
    print("p=13 reduced Laplacian size 168, determinant valuation:", valuation)


if __name__ == "__main__":
    main()
