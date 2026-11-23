#!/usr/bin/env python3
"""Finite implementation checks for quadratic.tex; these do not prove theorems.

Uses only Python's standard library. Descent functions return explicit trace
records, so every norm equality, exact division and strict decrease is checked.
"""
import itertools
import json
from math import gcd, isqrt
from pathlib import Path


def prime(n):
    return n >= 2 and all(n % d for d in range(2, isqrt(n) + 1))


def factors(n):
    ans = []
    for p in range(2, n + 1):
        while n % p == 0:
            ans.append(p)
            n //= p
    return ans


def legendre(p, a):
    a %= p
    if a == 0:
        return 0
    return 1 if any(x * x % p == a for x in range(1, p)) else -1


def order(p, a):
    return next(e for e in range(1, p) if pow(a, e, p) == 1)


def balance(m, x):
    r = x % m
    return r - m if 2 * r > m else r


def n2(x):
    return sum(t * t for t in x)


def b2(x, r):
    a, b = x
    c, d = r
    return a * c + b * d, a * d - b * c


def b4(x, r):
    a, b, c, d = x
    w, z, y, v = r
    return (a*w+b*z+c*y+d*v,
            a*z-b*w-c*v+d*y,
            a*y+b*v-c*w-d*z,
            a*v-b*y+c*z-d*w)


def two_step(p, m, x):
    assert prime(p) and 1 < m < p and n2(x) == m*p
    r = tuple(balance(m, t) for t in x)
    assert n2(r) % m == 0
    mm = n2(r) // m
    num = b2(x, r)
    assert all(t % m == 0 for t in num)
    y = tuple(t // m for t in num)
    assert 1 <= mm < m and n2(y) == mm*p
    return mm, y


def two_prime(p):
    assert prime(p) and (p == 2 or p % 4 == 1)
    if p == 2:
        return (1, 1), []
    a = next(a for a in range(1, (p-1)//2+1) if (a*a+1) % p == 0)
    m, x = (a*a+1)//p, (a, 1)
    trace = [(m, x)]
    for _ in range(p):
        if m > 1:
            m, x = two_step(p, m, x)
            trace.append((m, x))
    assert m == 1 and n2(x) == p
    return tuple(map(abs, x)), trace


def four_step(p, m, x):
    assert prime(p) and p % 2 and 1 < m < p and n2(x) == m*p
    if m % 2 == 0:
        z = tuple(t for t in x if t % 2 == 0) + tuple(t for t in x if t % 2)
        a, b, c, d = z
        assert (a-b) % 2 == 0 and (c-d) % 2 == 0
        y = ((a+b)//2, (a-b)//2, (c+d)//2, (c-d)//2)
        mm = m//2
    else:
        r = tuple(balance(m, t) for t in x)
        assert n2(r) % m == 0
        mm = n2(r)//m
        num = b4(x, r)
        assert all(t % m == 0 for t in num)
        y = tuple(t//m for t in num)
    assert 1 <= mm < m and n2(y) == mm*p
    assert all(abs(t) < p for t in y)
    return mm, y


def four_prime(p):
    assert prime(p)
    if p == 2:
        return (1, 1, 0, 0), []
    h = (p-1)//2
    a, b = next((a, b) for a in range(h+1) for b in range(h+1)
                if (a*a+b*b+1) % p == 0)
    m, x = (a*a+b*b+1)//p, (a, b, 1, 0)
    trace = [(m, x)]
    for _ in range(p):
        if m > 1:
            m, x = four_step(p, m, x)
            trace.append((m, x))
    assert m == 1 and n2(x) == p
    return tuple(map(abs, x)), trace


def four(n):
    if n == 0:
        return (0, 0, 0, 0)
    x = (1, 0, 0, 0)
    for p in factors(n):
        y, _ = four_prime(p)
        x = b4(x, y)
    assert n2(x) == n
    return tuple(map(abs, x))


def check():
    counts = {}
    ps = [p for p in range(3, 200) if prime(p)]
    qr_cases = 0
    for p in ps:
        assert legendre(p, -1) == (-1)**((p-1)//2)
        assert legendre(p, 2) == (-1)**((p*p-1)//8)
        for q in ps:
            if p != q:
                assert legendre(p, q)*legendre(q, p) == (-1)**(((p-1)//2)*((q-1)//2))
                qr_cases += 1
    counts['quadratic_reciprocity_ordered_prime_pairs_below_200'] = qr_cases
    for p in [p for p in range(2, 100) if prime(p)]:
        gs = [g for g in range(1, p) if order(p, g) == p-1]
        assert len(gs) == sum(gcd(j, p-1) == 1 for j in range(p-1))
        assert gs
    counts['primitive_root_prime_moduli_below_100'] = 25
    two_traces, four_traces = {}, {}
    for p in [p for p in range(2, 500) if prime(p)]:
        x, trace = four_prime(p)
        assert n2(x) == p
        four_traces[str(p)] = trace
        if p == 2 or p % 4 == 1:
            x, trace = two_prime(p)
            assert n2(x) == p
            two_traces[str(p)] = trace
    counts['four_square_prime_routines_below_500'] = len(four_traces)
    counts['two_square_prime_routines_below_500'] = len(two_traces)
    two_classification_cases = 0
    for n in range(1, 501):
        fs = factors(n)
        predicted = all(fs.count(p) % 2 == 0 for p in set(fs) if p % 4 == 3)
        actual = any(a*a+b*b == n for a in range(isqrt(n)+1)
                     for b in range(isqrt(n)+1))
        assert predicted == actual
        assert n2(four(n)) == n
        two_classification_cases += 1
    counts['two_square_classification_n_1_through_500'] = two_classification_cases
    counts['four_square_factor_product_n_0_through_500'] = 501
    assert n2(four(0)) == 0
    even_cases, odd_cases = 0, 0
    for p in [p for p in range(3, 20) if prime(p)]:
        for m in range(2, p):
            norm = m*p
            lim = isqrt(norm)
            for a in range(lim+1):
                for b in range(isqrt(norm-a*a)+1):
                    for c in range(isqrt(norm-a*a-b*b)+1):
                        rem = norm-a*a-b*b-c*c
                        d = isqrt(rem)
                        if d*d != rem:
                            continue
                        for signs in itertools.product((-1, 1), repeat=4):
                            x = tuple(t*sg for t, sg in zip((a,b,c,d), signs))
                            mm, y = four_step(p, m, x)
                            assert mm < m and n2(y) == mm*p
                            if m % 2:
                                odd_cases += 1
                            else:
                                even_cases += 1
    counts['four_square_even_multiplier_signed_states_p_below_20'] = even_cases
    counts['four_square_odd_multiplier_signed_states_p_below_20'] = odd_cases
    return {
        'status': 'PASS',
        'meaning': 'Finite implementation checks; not a machine-checked iPRA proof.',
        'counts': counts,
        'example_four_square_descent_499': four_traces['499'],
        'example_two_square_descent_461': two_traces['461'],
    }


if __name__ == '__main__':
    result = check()
    print(json.dumps(result, indent=2))
    dest = Path(__file__).resolve().parent / 'validation_quadratic.json'
    dest.write_text(json.dumps(result, indent=2) + '\n')
