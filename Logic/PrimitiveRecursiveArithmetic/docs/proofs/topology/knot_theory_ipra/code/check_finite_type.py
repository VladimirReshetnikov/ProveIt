"""Check the finite-difference claims on explicit Jones state sums."""
from itertools import combinations, product
from math import comb
from jones_states import jones


def binomial_integer(n, k):
    if n < 0:
        return (-1)**k * comb(-n + k - 1, k)
    return comb(n, k) if k <= n else 0


def coefficient(poly, k):
    return sum(val * binomial_integer(degree, k) for degree, val in poly.items())


def difference(strands, word, marked, k):
    total = 0
    for signs in product((1, -1), repeat=len(marked)):
        w = list(word)
        for j, sign in zip(marked, signs):
            w[j] = sign * abs(w[j])
        total += (-1)**signs.count(-1) * coefficient(jones(strands, w), k)
    return total


if __name__ == "__main__":
    for word in [(1, 1, 1), (1, -2, 1, -2), (1, -2, 1, -2, 1, -2)]:
        strands = 1 + max(map(abs, word))
        for k in range(3):
            for sites in combinations(range(len(word)), k + 1):
                assert difference(strands, word, sites, k) == 0
    assert difference(2, (1, 1, 1), (0, 1), 2) == -48
    print("Passed Jones finite differences through degree two and exact order-two witness.")
