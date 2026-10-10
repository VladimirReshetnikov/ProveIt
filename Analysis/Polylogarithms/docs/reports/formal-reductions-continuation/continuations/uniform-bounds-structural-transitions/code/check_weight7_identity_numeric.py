#!/usr/bin/env python3
"""Optional numerical audit of the full weight-seven analytic identity.

Requires mpmath.  These are diagnostic checks of branches and endpoint
normalizations, not a proof or an interval enclosure.  The exact proof
certificate is replayed by verify_depth_orbits.py.
"""
from fractions import Fraction
from functools import lru_cache
import json
from pathlib import Path
import mpmath as mp
from verify_depth_orbits import shuffle_words

mp.mp.dps = 80


def indices(word):
    result, count = [], 1
    for letter in word:
        if letter == 0:
            count += 1
        else:
            result.append(count)
            count = 1
    return tuple(result)


@lru_cache(None)
def mpl(index, z):
    """Unaccelerated disk series; all test arguments have |z| <= 3/4."""
    harmonic = [mp.mpf(0)] * (len(index) - 1) + [mp.mpf(1)]
    result, power = mp.mpf(0), mp.mpf(1)
    for n in range(1, 800):
        power *= z
        result += power * harmonic[0] / mp.mpf(n) ** index[0]
        # Ascending order uses every deeper harmonic sum at n-1.
        for j in range(len(index) - 1):
            harmonic[j] += harmonic[j + 1] / mp.mpf(n) ** index[j + 1]
    return result


@lru_cache(None)
def hyperlog(word, z):
    if not word:
        return mp.mpf(1)
    if sum(word) == 0:
        return mp.log(z) ** len(word) / mp.factorial(len(word))
    if word[-1] == 1:
        return mpl(indices(word), z)
    prefix = word[:-1]
    expansion = shuffle_words(prefix, (0,))
    result = hyperlog(prefix, z) * mp.log(z)
    for other, coefficient in expansion.items():
        if other != word:
            result -= coefficient * hyperlog(other, z)
    return result / expansion[word]


def zeta_n1(n):
    return (n * mp.zeta(n + 1)
            - mp.fsum(mp.zeta(n - k) * mp.zeta(k + 1)
                      for k in range(1, n - 1))) / 2


def main():
    root = Path(__file__).resolve().parents[1] / 'data'
    certificate = json.loads((root / 'weight7_height_one_products.json').read_text())
    cases = []
    for z in [mp.mpf(1) / 4, mp.mpf(1) / 3]:
        correction = mp.mpf(0)
        for item in certificate['product_correction']:
            coefficient = Fraction(item['coefficient'])
            term = mp.mpf(coefficient.numerator) / coefficient.denominator
            for word in item['factors']:
                term *= hyperlog(tuple(map(int, word)), z)
            correction += term
        u, v, alpha = 1 - z, z / (z - 1), -mp.log(1 - z)
        C7 = mp.zeta(7) + mp.fsum(
            (-alpha) ** k / mp.factorial(k) * mp.zeta(7 - k)
            for k in range(1, 6))
        C61 = zeta_n1(6) + mp.fsum(
            (-alpha) ** k / mp.factorial(k) * zeta_n1(6 - k)
            for k in range(1, 5))
        rhs = (-3 * mpl((7,), z) + 2 * mpl((6, 1), z)
               + 2 * mpl((7,), u) - mpl((6, 1), u)
               - 3 * mpl((7,), v) + mpl((6, 1), v)
               + correction - 2 * C7 + C61)
        lhs = mpl((5, 1, 1), z)
        discrepancy = lhs - rhs
        assert abs(discrepancy) < mp.mpf('1e-65')
        cases.append({'z': mp.nstr(z, 30), 'lhs': mp.nstr(lhs, 70),
                      'diagnostic_discrepancy': mp.nstr(discrepancy, 20)})
    receipt = {'status': 'PASS', 'decimal_working_precision': mp.mp.dps,
               'proof_or_interval_certificate': False, 'cases': cases}
    (root / 'weight7_numerical_diagnostics.json').write_text(
        json.dumps(receipt, indent=2) + '\n')
    print(json.dumps(receipt, indent=2))


if __name__ == '__main__':
    main()
