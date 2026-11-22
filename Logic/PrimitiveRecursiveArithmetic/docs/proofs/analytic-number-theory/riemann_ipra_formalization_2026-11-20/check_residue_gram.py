"""Finite Gram packets with exact arithmetic, including Cramer witnesses."""
from fractions import Fraction
from itertools import permutations, product
from math import prod


def det(matrix):
    n = len(matrix)
    total = 0
    for perm in permutations(range(n)):
        odd = sum(perm[i] > perm[j] for i in range(n) for j in range(i+1, n)) % 2
        total += (-1)**odd * prod(matrix[i][perm[i]] for i in range(n))
    return total


def packet(k, j, target):
    factors = [n * (n + 1) for n in range(1, j+1)]
    p = prod(factors)
    scale = (j+1)*p
    heights = list(range(1, k+1)) + [1]
    samples = [[n % (i+2) for i in range(k)] + [target(n)] for n in range(1, j+1)]
    gram = [[sum((scale // factors[n])*r[i]*r[l] for n, r in enumerate(samples))
             + int(i == l)*p*(k+1)*heights[i]**2
             for l in range(k+1)] for i in range(k+1)]
    core = [r[:-1] for r in gram[:-1]]
    d = det(core)
    assert d > 0
    argmin = []
    for i in range(k):
        replaced = [r[:i] + [gram[n][-1]] + r[i+1:] for n, r in enumerate(core)]
        argmin.append(Fraction(det(replaced), d))
    minimum = Fraction(det(gram), scale*d)

    def objective(x):
        risk = sum((Fraction((r[-1] - sum(a*b for a, b in zip(x, r)))**2, factors[n])
                    for n, r in enumerate(samples)), Fraction())
        return risk + Fraction(k+1, j+1)*(1+sum(a*a*b*b for a, b in zip(x, heights)))

    assert objective(argmin) == minimum
    for x in product((-1, 0, 1), repeat=k):
        assert objective(x) >= minimum
    return minimum, argmin


if __name__ == "__main__":
    one = lambda n: 1
    cases = 0
    for f, k, j in product((one, lambda n: int(n == 2), lambda n: int(n >= 2)),
                           range(5), (0, 1, 2, 4, 8, 16)):
        packet(k, j, f)
        cases += 1
    value, coeff = packet(1, 24, one)
    assert 2*value <= 1
    print(f"{cases} Gram minima independently recovered by Cramer's rule")
    print(f"K=1, J=24, constant target: minimum = {value}, coefficient = {coeff[0]}")
