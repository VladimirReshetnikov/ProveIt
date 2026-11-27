#!/usr/bin/env python3
"""Exact, standard-library checks of the depth-one period theorem."""
from math import comb


def valuation(n, p):
    assert n > 0
    count = 0
    while n % p == 0:
        n //= p
        count += 1
    return count


def period_by_boundary_binomials(p, e, m):
    if m == 1:
        return 1
    h = m - 1
    a = 1
    while p**a <= h:
        a += 1
    jmax = max(j // e + valuation(comb(h - 1, j), p) for j in range(h))
    return p**max(a, 1 + valuation(h, p) + jmax)


def period(p, e, m):
    if m == 1:
        return 1
    return p**max((j + e - 1) // e + valuation(j, p) for j in range(1, m))


def defect(n, p, e, m):
    """Compute directly from surviving coefficients of the negative binomial series."""
    for k in range(n, -1, -1):
        if k + e * valuation(comb(k + m - 1, m - 1), p) <= n:
            return n - k
    raise AssertionError("constant coefficient must survive")


def shortest_repeating_block(word):
    """Recover least period from a sample made of complete repetitions."""
    prefix = [0] * len(word)
    for i in range(1, len(word)):
        match = prefix[i - 1]
        while match and word[i] != word[match]:
            match = prefix[match - 1]
        if word[i] == word[match]:
            match += 1
        prefix[i] = match
    length = len(word) - prefix[-1]
    return length if len(word) % length == 0 else len(word)


def quotient_cutoff(p, m, r):
    """Compute the nilpotency index of X modulo X^m (p+X^(p-1))^m, p^r."""
    modulus = p**r
    degree = p * m
    poly = [0] * degree  # lower coefficients of this monic polynomial
    for j in range(m):
        poly[m + (p - 1) * j] = comb(m, j) * p**(m - j) % modulus
    vec = [1] + [0] * (degree - 1)
    count = 0
    while any(vec):
        lead = vec[-1]
        vec = [((0 if i == 0 else vec[i - 1]) - lead * c) % modulus
               for i, c in enumerate(poly)]
        count += 1
        assert count <= degree * r
    return count


def main():
    small = large = quotient_checks = jordan_checks = 0
    for p in (2, 3, 5, 7):
        for e in (1, 2, 3, 5, 10):
            for m in range(1, 19):
                t = period(p, e, m)
                assert t == period_by_boundary_binomials(p, e, m)
                if t <= 3000:
                    word = [defect(n, p, e, m) for n in range(2 * t)]
                    assert shortest_repeating_block(word) == t, (p, e, m, t)
                    assert all((value == m - 1) == ((n + 1) % t == 0)
                               for n, value in enumerate(word))
                    small += 1
                else:
                    h = m - 1
                    block = p
                    while block <= h:
                        block *= p
                    # Inspect entire blocks around the maximal precision needed
                    # to distinguish a proper p-power divisor.
                    cases = {s + z for z in (0, t // p - block, t - block)
                             for s in range(block)}
                    assert all(defect(n, p, e, m) == defect(n + t, p, e, m)
                               for n in cases)
                    assert any(defect(n, p, e, m) != defect(n + t // p, p, e, m)
                               for n in cases)
                    assert all((defect(n, p, e, m) == m - 1) == ((n + 1) % t == 0)
                               for n in cases)
                    large += 1
    for p in (2, 3, 5):
        for m in range(1, 9):
            for r in range(1, 13):
                n = r - 1
                expected = p * m + (p - 1) * (n - defect(n, p, 1, m))
                assert quotient_cutoff(p, m, r) == expected
                quotient_checks += 1
    for p in (2, 3, 5):
        for e in (1, 2, 3):
            for m in range(1, 12):
                for r in range(1, 20):
                    # Superdiagonal j of J**s equals pi**(s-j) times C(s,j).
                    def vanishes(s):
                        return all(s - j + e * valuation(comb(s, j), p) >= r
                                   for j in range(min(m - 1, s) + 1))
                    first = next(s for s in range(r, r + m) if vanishes(s))
                    assert first == m + r - 1 - defect(r - 1, p, e, m)
                    jordan_checks += 1
    for p in (2, 3, 5, 7):
        for a in (1, 2, 3):
            m = p**a
            assert period(p, 1, m) == p**(m - 1)
    print(f"Primitive period recovered from two full cycles: {small} parameter triples")
    print(f"Large-period witness and translation checked: {large} parameter triples")
    print(f"Independent polynomial quotient checks: {quotient_checks}")
    print(f"Independent Jordan power checks: {jordan_checks}")
    print("Prime-power multiplicity identities verified: 12")
    for p, e, m in ((2, 1, 4), (2, 2, 4), (3, 1, 3), (2, 1, 8), (2, 2, 8),
                    (2, 1, 10), (5, 1, 5)):
        t = period(p, e, m)
        print(f"p={p} e={e} m={m} period={t} initial defects="
              f"{[defect(n, p, e, m) for n in range(min(t, 16))]}")


if __name__ == "__main__":
    main()
