"""Verify the seven-loop ternary tower by exact cyclotomic arithmetic."""
from collections import Counter
from math import comb


def local_order(a, b, k, h):
    """Return the integral valuation in the uniformizer zeta_(3^h)-1."""
    block = 3 ** (h - 1)
    order, degree = 3 * block, 2 * block
    poly = Counter({0: 14})
    for power, multiplicity in [(a, 3), (b, 3), (3**k * a, 1)]:
        for sign in [-1, 1]:
            poly[sign * power % order] -= multiplicity
    # Reduce by 1 + Z^block + Z^(2*block).
    for exponent in sorted(poly, reverse=True):
        if exponent < degree:
            break
        value = poly.pop(exponent)
        poly[exponent - degree] -= value
        poly[exponent - block] -= value
    best = None
    for j in range(degree):
        if best is not None and j >= best:
            break
        coefficient = sum(value * comb(i, j) for i, value in poly.items() if i >= j)
        if coefficient == 0:
            continue
        term_order = j
        while coefficient % 3 == 0:
            term_order += degree
            coefficient //= 3
        best = term_order if best is None else min(best, term_order)
    assert best is not None
    return best


def level_increment(k, h):
    order = 3**h
    # One representative per Galois orbit of primitive characters.
    return (sum(local_order(1, b, k, h) for b in range(order))
            + sum(local_order(a, 1, k, h) for a in range(0, order, 3)) - 2)


def prefix(n):
    return 9**n + 4*3**n - 2*n - 5


def tail(k, n):
    return ((2*(n-k)+1)*3**(k+n) + (2*(n-k)+4)*3**k - 2*n - 5)


def main():
    for k in range(1, 5):
        values = []
        total = 0
        for n in range(1, 6):
            total += level_increment(k, n)
            assert total == (prefix(n) if n <= k else tail(k, n))
            if n == k:
                assert total == tail(k, n)
            if n == k-1:
                assert total > tail(k, n)
            values.append(total)
        print(f"k={k}, levels 1 to 5: {values}")


if __name__ == "__main__":
    main()
