#!/usr/bin/env python3
"""Independent finite regressions for the new arithmetic lemmas.

These checks are diagnostics, not substitutes for the unbounded proofs.
Only the Python standard library is used; assertions are not used as gates.
"""
from math import comb, gcd, lcm
import json


def require(ok, message):
    if not ok:
        raise ValueError(message)


def generalized_binomial(n, k):
    if k < 0:
        raise ValueError('negative lower index')
    if n >= 0:
        return comb(n, k) if k <= n else 0
    return (-1) ** k * comb(-n + k - 1, k)


def factor_small(n):
    result = {}
    p = 2
    while p * p <= n:
        while n % p == 0:
            result[p] = result.get(p, 0) + 1
            n //= p
        p += 1
    if n > 1:
        result[n] = result.get(n, 0) + 1
    return result


def binomial_factors(R, t):
    factors = {}
    for i in range(1, t + 1):
        for n, sign in [(R + i, 1), (i, -1)]:
            for p, e in factor_small(n).items():
                factors[p] = factors.get(p, 0) + sign * e
    require(all(e >= 0 for e in factors.values()), 'binomial integrality')
    return {p: e for p, e in factors.items() if e}


def pell(A, k):
    X, Y = 1, 0
    for _ in range(abs(k)):
        X, Y = A * X + (A * A - 1) * Y, X + A * Y
    return X, Y if k >= 0 else -Y


def main():
    counts = {}
    L = 1
    lc = [1]
    for n in range(1, 1001):
        L = lcm(L, n)
        lc.append(L)
        require(L <= 4 ** (n - 1), ('lcm exponential bound', n))
        m = (n + 1) // 2
        require((lc[m] * comb(n, n // 2)) % L == 0,
                ('central-binomial divisibility', n))
    counts['lcm_bounds_and_divisibilities'] = 1000

    for t in range(1, 41):
        R = 16 ** t
        B = comb(R + t, t)
        require(B > (t + 1) ** t, ('label-base growth', t))
        require(B % 2 == 1, ('binomial oddness', t))
        require(R >= lc[t] ** 2, ('row radius bound', t))
    counts['fixed_base_binomials'] = 40

    count = 0
    for n in range(-80, 81):
        for k in range(0, 31):
            c = generalized_binomial(n, k)
            require(abs(c) <= max(1, abs(n)) ** k, ('signed coefficient bound', n, k))
            if k:
                for p in [2, 3, 5, 7, 11, 13]:
                    for e in range(1, 5):
                        pe = p ** e
                        if c % pe == 0:
                            require(n % pe < k, ('signed range implication', n, k, pe))
                        count += 1
    counts['signed_range_implications'] = count
    counts['signed_coefficient_bounds'] = 161 * 31

    count = 0
    for t in range(1, 9):
        for offset in [0, 1, 2, 3, 7, 11, 23]:
            R = lc[t] ** 2 + offset
            ff = binomial_factors(R, t)
            for i in range(1, t + 1):
                require(any(p ** e > t and (R + i) % (p ** e) == 0
                            for p, e in ff.items()), ('missing row selector', R, t, i))
            for p, e in ff.items():
                require(any((R + i) % (p ** e) == 0 for i in range(1, t + 1)),
                        ('unassigned modulus prime', R, t, p, e))
            require(comb(R + t, t) == __import__('functools').reduce(
                lambda a, pe: a * pe[0] ** pe[1], ff.items(), 1), 'factorization')
            count += 1
    counts['binomial_selector_instances'] = count

    count = 0
    for q in [3, 5, 9, 15, 21]:
        for N in [d for d in range(1, q + 1) if q % d == 0]:
            for x in [3, 4, 5]:
                modulus = N * q ** x
                n = q + 1
                A = ((n * n + 1) * pow(2 * n, -1, modulus)) % modulus + modulus
                require((2 * A * n - n * n - 1) % modulus == 0, 'common root')
                for k in range(-12, 13):
                    X, Y = pell(A, k)
                    mu = X + (n - A) * Y
                    require(mu % modulus == pow(n, k, modulus),
                            ('signed modular power', q, N, x, k))
                    count += 1
    counts['signed_modular_power_instances'] = count

    count = 0
    for n in range(-12, 13):
        for k in range(1, 9):
            C = max(abs(generalized_binomial(n, j)) for j in range(k + 1))
            q = 3 * (128 * C + 1)
            N = 3
            x = k + 1
            D, M = q ** k, q ** x
            modulus = N * M
            A = (((q + 1) ** 2 + 1) * pow(2 * (q + 1), -1, modulus)) % modulus + modulus
            X, Y = pell(A, n)
            mu = X + (q + 1 - A) * Y
            r = sum(generalized_binomial(n, j) * q ** j for j in range(k))
            require(abs(r) * 32 < D, ('signed truncation bound', n, k))
            require((mu - r) % D == 0, ('digit divisibility', n, k))
            require(((mu - r) // D) % N == generalized_binomial(n, k) % N,
                    ('generalized binomial digit', n, k))
            v = M // D
            require(v * mu == M * ((mu - r) // D) + v * r, 'normalized exact identity')
            count += 1
    counts['signed_modular_digit_instances'] = count

    require(comb(3, 2) == 3 and 1 % 3 != 0, 'small-radius negative control')
    counts['known_small_radius_counterexample_retained'] = True
    return {'status': 'PASS', 'scope': 'finite arithmetic regressions only', 'checks': counts}


if __name__ == '__main__':
    print(json.dumps(main(), indent=2, sort_keys=True))
