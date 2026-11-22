"""Exact arithmetic checks for the integer Toeplitz and determinant criteria."""

from fractions import Fraction
from itertools import permutations, product
from math import factorial, lcm, prod


def riemann_packet(c, m, n):
    """Finite Riemann-family packet for F = X - 1."""
    q = 2 * c
    p = (2 * c - 1) * c - 1
    degree, height = 1, 0
    u = 1000 * c * (1000 * (degree + 1) ** 4 * (height + 2) ** 2) * q**3
    common = q**m * factorial(m) * n ** (2 * m) * factorial(n) ** c
    s = common * (n * u + 9 * m * (degree + 1) * (1 + c) ** m)
    prefix = [0]
    integer_product = 1
    for j in range(1, n + 1):
        integer_product = lcm(integer_product, j)
        prefix.append(integer_product.bit_length() - 1)
    jumps = [0] + [prefix[j] - prefix[j - 1] for j in range(1, n + 1)]
    signed = [jumps[j] - (2 * jumps[j // 2] if j % 2 == 0 else 0) for j in range(n + 1)]
    logs = [sum(n * n // (n + v) for v in range(1, n * (j - 1) + 1)) for j in range(n + 1)]
    terms = []
    for k in range(m):
        num = sum(signed[j] * logs[j] ** k * (factorial(n) // j) ** c for j in range(1, n + 1))
        den = factorial(k) * n ** (2 * k) * factorial(n) ** c
        entry = n * p**k * num * q ** (m - k) * (factorial(m) // factorial(k)) * n ** (2 * (m - k))
        assert Fraction(entry, n * common) == Fraction(p, q) ** k * Fraction(num, den)
        terms.append(entry)
    return terms, s


def convolution(t, x):
    return [sum(t[i - j] * x[j] for j in range(i + 1)) for i in range(len(t))]


def norm2(x):
    return sum(a * a for a in x)


def shifted_matrix(t, s, k):
    m = len(t)
    return [
        [
            (1 + k * s * s if a == b else 0)
            - k * sum(t[h - a] * t[h - b] for h in range(max(a, b), m))
            for b in range(m)
        ]
        for a in range(m)
    ]


def det_prefix(matrix, h):
    ans = 0
    for sigma in permutations(range(h)):
        inversions = sum(sigma[i] > sigma[j] for i in range(h) for j in range(i + 1, h))
        ans += (-1) ** inversions * prod(matrix[i][sigma[i]] for i in range(h))
    return ans


def encoded_det(matrix, h):
    """Reference implementation of the radix permutations and sign masks."""
    parts = [0, 0]
    for w in range((h + 1) ** h):
        cols = [w // (h + 1) ** j % (h + 1) for j in range(h)]
        if sorted(cols) != list(range(h)):
            continue
        inv = sum(cols[b] > cols[a] for a in range(h) for b in range(a))
        for mask in range(2**h):
            sign = (inv + mask.bit_count()) % 2
            # Deliberately use noncanonical signed pairs as in the PR matrix.
            entries = [matrix[j][cols[j]] for j in range(h)]
            terms = [
                3 + (max(-a, 0) if (mask >> j) & 1 else max(a, 0))
                for j, a in enumerate(entries)
            ]
            parts[sign] += prod(terms)
    return parts[0] - parts[1]


def verify(t, s, shifts, full=True):
    m = len(t)
    for x in product((-1, 0, 1), repeat=m):
        z = convolution(t, x)
        deficit = s * s * norm2(x) - norm2(z)
        if full:
            assert deficit >= 0
        for y in product((-1, 0, 1), repeat=m):
            block = s * s * norm2(x) + norm2(y) - 2 * sum(a * b for a, b in zip(y, z))
            assert block == deficit + norm2([a - b for a, b in zip(y, z)])
        for k in shifts:
            q = shifted_matrix(t, s, k)
            assert sum(q[i][j] * x[i] * x[j] for i in range(m) for j in range(m)) == norm2(x) + k * deficit
    for k in shifts:
        a = shifted_matrix(t, s, k)
        for h in range(1, m + 1):
            d = det_prefix(a, h)
            assert d == encoded_det(a, h)
            if full:
                assert d > 0


if __name__ == "__main__":
    for c in [5, 6, 8]:
        for m in [1, 2, 3]:
            for n in [1, 2, 4, 6]:
                verify(*riemann_packet(c, m, n), shifts=[0, 1, 3])
    verify([5, 0], 5, [0, 1, 9])  # Equality of the unshifted contraction.
    t, s, x = [3, 4], 5, [1, 1]
    assert norm2(t) == s * s
    assert norm2(convolution(t, x)) == 58 > s * s * norm2(x) == 50
    assert det_prefix(shifted_matrix(t, s, 3), 2) < 0
    verify(t, s, [0, 1, 3], full=False)
    print("36 RH packets, 2 boundary examples, sign expansions and quadratic identities passed.")
