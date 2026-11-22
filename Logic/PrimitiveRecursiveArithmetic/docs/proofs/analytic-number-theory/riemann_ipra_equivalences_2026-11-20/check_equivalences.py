#!/usr/bin/env python3
"""Independent small numerical checks for the finite identities in the report."""
from fractions import Fraction as F
from itertools import permutations
from math import factorial, gcd, prod
from check_packets import euler_product, h_value, primes_through


def mobius(n):
    factors = [p for p in primes_through(n) if n % p == 0]
    return 0 if any(n % (p*p) == 0 for p in factors) else (-1) ** len(factors)


def determinant(b, v):
    n = len(v)
    def entry(i, j):
        if j == 1:
            return v[i-1]
        return b(j//i) if j % i == 0 else 0
    total = 0
    for perm in permutations(range(1, n+1)):
        parity = sum(x > y for i, x in enumerate(perm) for y in perm[i+1:]) % 2
        total += (-1)**parity * prod(entry(i, j) for i, j in enumerate(perm, 1))
    return total


def inverse_row(b, n):
    a = [0, 1]
    for j in range(2, n+1):
        a.append(-sum(a[i]*b(j//i) for i in range(1, j) if j % i == 0))
    return a


def matrices():
    # zeta, Gaussian zeta (ideals up to norm 7), and two artificial Euler weights
    gaussian = [0, 1, 1, 0, 1, 2, 0, 0]
    bs = [lambda i: 1, lambda i: gaussian[i], lambda i: i, lambda i: (-1)**(i-1)]
    for n in range(1, 8):
        masks = [[1]*n, [int(j % 3 == 1) for j in range(1, n+1)],
                 [(-1)**j*(n-j) for j in range(1, n+1)]]
        for b in bs:
            a = inverse_row(b, n)
            for mask in masks:
                assert determinant(b, mask) == sum(w*t for w, t in zip(a[1:], mask))
    print('84 signed determinant checks, dimensions 1 through 7.')


def energy(m, n):
    v = [0] + [m[n//i] for i in range(1, n+1)]
    def jordan(d):
        return sum(gcd(gcd(x, y), d) == 1 for x in range(d) for y in range(d))
    t = [0] + [sum(F(v[i], i) for i in range(d, n+1, d)) for d in range(1, n+1)]
    a = sum(jordan(d)*t[d]**2 for d in range(1, n+1))
    b = sum(F(gcd(k, j)**2*v[k]*v[j], k*j) for k in range(1, n+1) for j in range(1, n+1))
    assert a == b and sum(mobius(d)*t[d] for d in range(1, n+1)) == m[n] and m[n]**2 <= 8*a
    # Exact integral of the squared sawtooth sum on all maximal affine cells
    points = sorted({F(i, k) for k in range(1, n+1) for i in range(k+1)})
    integral = 0
    for x, y in zip(points, points[1:]):
        mid = (x+y)/2
        def trace(z):
            return sum(v[k]*(k*z - ((k*mid)//1) - F(1, 2)) for k in range(1, n+1))
        l, h = trace(x), trace(y)
        integral += (y-x)*(l*l+l*h+h*h)/3
    assert a == 12*integral
    return a


def farey(n, m, b):
    xs = sorted(F(x, d) for d in range(1, n+1) if d % m == b for x in range(1, d+1) if gcd(x, d) == 1)
    N = len(xs)
    if N == 0:
        return
    s2 = sum((x-F(j, N))**2 for j, x in enumerate(xs, 1))
    delta = int(1 % m == b)
    values = sorted({F(0), *xs, F(1)})
    moment = 0
    for x, y in zip(values, values[1:]):
        count = sum(z <= x for z in xs)
        l = N*x-count-F(delta, 2)
        h = N*y-count-F(delta, 2)
        moment += (y-x)*(l*l+l*h+h*h)/3
    assert moment == N*s2 + F(1, 3) + F(delta-1, 2) - F(delta*delta, 4)


def div_and_series():
    M = [0]
    for n in range(1, 22):
        M.append(M[-1]+mobius(n))
    for r in range(1, 4):
        for n in range(1, 22):
            def u(i):
                return 2**((r+1)*((i.bit_length()-1)//(2*r))) if i else 1
            S = [F(0)]
            for i in range(1, n+1):
                S.append(S[-1]+F(M[i]-M[i-1], u(i)))
            assert all((v*u(i)).denominator == 1 for i, v in enumerate(S))
            assert M[n] == u(n)*S[n] - sum((u(i+1)-u(i))*S[i] for i in range(1, n))
    for n in range(1, 13):
        for m, b in [(1, 0), (3, 1), (3, 2), (7, 5)]:
            farey(n, m, b)
    for n in range(1, 17):
        energy(M, n)
        energy([0]+[(-1)**i*(i+3) for i in range(1, n+1)], n)
    print('32 exact gcd/Gram/integral identities, 63 Abel identities, 48 Farey inputs.')
    print('For Mertens and N=6, gcd energy =', energy(M, 6))


def lagarias():
    for n in range(1, 13):
        H = sum(F(1, i) for i in range(1, n+1))
        sigma = sum(d for d in range(1, n+1) if n % d == 0)
        for k in (0, 2, 7):
            m, B = 2*n+k+1, factorial(n)
            A = int(B*H)
            lower_exp = (1+H/m)**m
            upper_exp = (1-H/m)**(-m)
            def logarithm(offset):
                return sum(F(A-B, m*B+j*(A-B)) for j in range(offset, m+offset))
            lo, hi = H+lower_exp*logarithm(1), H+upper_exp*logarithm(0)
            assert lo <= hi and hi-lo <= F(8**n*(3*n**3+n), m)
            assert sigma <= hi and (n != 1 or lo == hi == 1)
            D = prod(m*B+j*(A-B) for j in range(m+1))
            for offset in [0, 1]:
                e = upper_exp if offset == 0 else lower_exp
                exact_num = (A-B)*sum(D//(m*B+j*(A-B)) for j in range(offset, m+offset))
                assert F(exact_num, D) == logarithm(offset)
                assert (B*sigma*e.denominator*D < A*e.denominator*D+B*e.numerator*exact_num) == (sigma < H+e*logarithm(offset))
    print('36 exact Lagarias enclosure and denominator checks.')


def prime_checks():
    for m in range(1, 8):
        f = [-1]+[0]*(m-1)+[1]
        for p in primes_through(13):
            for k in range(1, 5):
                assert h_value(f, p, k) == gcd(m, p**k-1)
    for f in [(-1,1), (1,0,1), (-1,0,0,1)]:
        vals = []
        for only_primes in (False, True):
            def b(n):
                a = (prod(p**h_value(f, p, 1) for p in primes_through(n))
                     if only_primes else euler_product(f, n))
                return a.bit_length()-1
            vals.append(sum(b(2*n)-2*b(n) for n in range(100, 104)))
        assert vals == {(-1,1):[52,72],(1,0,1):[38,40],(-1,0,0,1):[138,162]}[f]
    print('168 cyclotomic exponent checks and all 6 smoothing examples.')


if __name__ == '__main__':
    matrices()
    div_and_series()
    lagarias()
    prime_checks()
