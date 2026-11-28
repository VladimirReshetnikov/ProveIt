"""Check the curve-derivative, Frobenius support, and path-count examples exactly."""
from collections import Counter
from itertools import product


def derivative(poly):
    """Differentiate in Z[x,y]/(y²-x³+x); keys are (power of x, power of y)."""
    result = Counter()
    for (i, j), coeff in poly.items():
        if i and j == 0:
            result[i - 1, 1] += 2 * i * coeff
        if i and j == 1:
            result[i + 2, 0] += 2 * i * coeff
            result[i, 0] -= 2 * i * coeff
        if j == 1:
            result[i + 2, 0] += 3 * coeff
            result[i, 0] -= coeff
    return {term: value for term, value in result.items() if value}


def reduced(poly, p):
    return {term: value % p for term, value in poly.items() if value % p}


def curve():
    for generator in [{(1, 0): 1}, {(0, 1): 1}]:
        derivatives = [generator]
        for _ in range(5):
            derivatives.append(derivative(derivatives[-1]))
        assert reduced(derivatives[3], 3) == {}
        scaled = {term: 3 * value for term, value in derivatives[1].items()}
        assert reduced(derivatives[5], 5) == reduced(scaled, 5)


def powers():
    p = 3
    even = [p ** (2 * i) for i in range(3)]
    odd = [p ** (2 * i + 1) for i in range(3)]
    assert [[r + c for c in even] for r in odd] == [
        [4, 12, 84], [28, 36, 108], [244, 252, 324]]
    for r, c in product(range(5), repeat=2):
        i, j = 2 * r + 1, 2 * c
        assert abs(i - j) % 2 == 1
        assert p**i + p**j == p**min(i, j) * (p**abs(i - j) + 1)


def paths():
    for q in (3, 5, 7, 11):
        freq = Counter((a*b + b*c) % q for a, b, c in product(range(q), repeat=3))
        assert freq[0] == 2*q*q - q
        assert all(freq[u] == q*q-q for u in range(1, q))
        # Sum over all nonzero roots of unity is -1. Every nonzero Fourier
        # frequency therefore gives freq[0] - freq[1] = q^2 exactly.
        assert freq[0] - freq[1] == q*q


if __name__ == '__main__':
    curve()
    powers()
    paths()
    print('Checked the differential operators at 3 and 5, the odd differences, and four path-quadric counts.')
