#!/usr/bin/env python3
"""Exact rational verification of the small-digit first-depth criterion.

Recover the exponential from E(pZ)=pE(Z)+E(Z)^q. Compute the least
valuation among actual kernel-generator leading coefficients. The prediction
is computed separately from digit sums and Legendre's formula.
"""
from fractions import Fraction
from math import comb


def vp(x, p):
    if not x:
        return float('inf')
    x = Fraction(x)
    numerator, denominator = abs(x.numerator), x.denominator
    value = 0
    while numerator % p == 0:
        value += 1
        numerator //= p
    while denominator % p == 0:
        value -= 1
        denominator //= p
    return value


def exponential_powers(p, nmax):
    q = p * p
    powers = [[Fraction(0)] * (nmax + 1) for _ in range(nmax + 1)]
    powers[0][0] = powers[1][1] = Fraction(1)
    for n in range(2, nmax + 1):
        # Compute all powers >= 2 before E_n. Their coefficients only need
        # E_1 through E_{n-1}. The support restriction speeds exact arithmetic.
        for i in range(2, n + 1):
            if (n - i) % (q - 1) == 0:
                powers[i][n] = sum(powers[1][j] * powers[i-1][n-j]
                                    for j in range(1, n-i+2, q-1))
        powers[1][n] = powers[q][n] / (p**n - p)
    return powers


def kernel_generators(p, cutoff):
    """Produce coefficient dictionaries of the generators from BS Lemma 5.2."""
    q = p * p
    for j in range(cutoff + 1):
        # (pX + X^q)^j
        phi_power = {j + h * (q - 1): comb(j, h) * p**(j - h)
                     for h in range(j + 1) if j + h * (q - 1) <= cutoff}
        special = {}
        for exponent, a in phi_power.items():
            special[exponent] = special.get(exponent, 0) + (q - 1) * a
            shifted = exponent + q - 1
            if shifted <= cutoff:
                special[shifted] = special.get(shifted, 0) + p * a
        yield special
        for i in range(1, q - 1):
            if j + i <= cutoff:
                yield {m + i: a for m, a in phi_power.items() if m + i <= cutoff}


def digits(n, q):
    result = []
    while n:
        n, digit = divmod(n, q)
        result.append(digit)
    return result


def test(p, cutoff):
    q = p * p
    powers = exponential_powers(p, cutoff)
    minima = [float('inf')] * (cutoff + 1)
    for generator in kernel_generators(p, cutoff):
        if not generator:
            continue
        first = min(generator)
        for n in range(first, cutoff + 1, q - 1):
            top = sum(a * powers[m][n] for m, a in generator.items() if m <= n)
            minima[n] = min(minima[n], vp(top, p))
    checked = attained = delayed = 0
    for n in range(1, cutoff + 1):
        coefficients = digits(n, q)
        s = sum(coefficients)
        if s > q - 1:
            continue
        # Legendre's digit-sum criterion for a multinomial unit.
        no_carry = sum(sum(digits(a, p)) for a in coefficients) == sum(digits(s, p))
        expected = (s <= q - 2 and no_carry)
        observed = minima[n] == -(n-s) // (q-1)
        assert minima[n] >= -(n-s) // (q-1)
        assert expected == observed, (p, n, minima[n], expected)
        checked += 1
        attained += observed
        delayed += not observed
    print(f'p={p}, q={q}, n <= {cutoff}: {checked} cases, {attained} at first depth, {delayed} delayed.')


def check_later_rows(p, ks):
    """Use L(pX+X^q)=pL(X) to check the low-degree log factors independently."""
    q = p * p
    for k in ks:
        n = (q - 1) * q**k
        J = 1
        while J + len(digits(J, p)) - 1 <= 2 * k:
            J += 1
        J -= 1
        log_coefficient = [Fraction(1)]
        power_coefficient = [Fraction(1)]
        for j in range(1, J + 1):
            m = 1 + j * (q - 1)
            numerator = sum(log_coefficient[j - i] * comb(m - i * (q - 1), i)
                            * p**(m - q * i) for i in range(1, m // q + 1))
            log_coefficient.append(numerator / (p - p**m))
            # Differentiate B^n to compute the j-th coefficient from lower ones;
            # here B is L(X)/X written as a series in X^(q-1).
            coefficient = sum(((n + 1) * i - j) * log_coefficient[i]
                              * power_coefficient[j-i] for i in range(1, j + 1)) / j
            power_coefficient.append(coefficient)
            assert vp(coefficient, p) >= 0, (p, k, j)
    print(f'p={p}: later-row log integrality checked for k={list(ks)}.')


if __name__ == '__main__':
    test(2, 100)
    test(3, 120)
    test(5, 130)
    check_later_rows(2, range(1, 17))
    check_later_rows(3, range(1, 9))
    check_later_rows(5, range(1, 5))
