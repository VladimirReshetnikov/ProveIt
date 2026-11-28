#!/usr/bin/env python3
"""Exact checks for the punctured Fourier construction. Uses the Python standard library."""
from collections import Counter
from fractions import Fraction
from functools import cache
from math import gcd
import json


def factor(q):
    factors = {}
    p = 2
    while p * p <= q:
        while q % p == 0:
            factors[p] = factors.get(p, 0) + 1
            q //= p
        p += 1
    if q > 1:
        factors[q] = 1
    return factors


def divisors(q):
    return [r for r in range(1, q + 1) if q % r == 0]


@cache
def cyclotomic(q):
    # Descending monic division in Z[X].
    f = [-1] + [0] * (q - 1) + [1]
    for d in divisors(q)[:-1]:
        g = cyclotomic(d)
        h = []
        while len(f) >= len(g):
            offset = len(f) - len(g)
            c = f[-1]
            h.append(c)
            for i, gi in enumerate(g):
                f[offset + i] -= c * gi
            assert f.pop() == 0
        assert all(x == 0 for x in f)
        f = h[::-1]
    return tuple(f)


def qmul(x, y, n):
    # β² = β - n, coordinates (a,b) stand for a + bβ.
    a, b = x
    c, d = y
    return a * c - n * b * d, a * d + b * c + b * d


def conj(x):
    a, b = x
    return a + b, -b


def bar_beta_pow(k, n):
    x = (1, 0)
    for _ in range(k):
        x = qmul(x, (1, -1), n)
    return x


def local_frame(q, p, a, n, reduced):
    P = p**a
    original = bar_beta_pow(2*a, n)
    if reduced:
        c = (original[0] % (P*P), original[1] % (P*P))
        t = 1 + p*P*(1+n)
    else:
        c, t = original, 1+n**a
    tr, norm = 2 * c[0] + c[1], qmul(c, conj(c), n)
    assert norm[1] == 0 and norm[0] % (P*P) == 0 and tr % p == 1
    # β=0 and β=1 are the two reductions at the primes over p.
    assert c[0] % p == 1 and (c[0]+c[1]) % p == 0
    L = t*t - p*(norm[0]//(P*P))
    h = (q//P) * (P*t*t + t*tr + norm[0]//P)
    assert L >= 1 and norm[0] % (P*p) == 0
    assert h % p == (q//P) % p
    assert all(h % r == 0 for r in factor(q) if r != p)
    return P, (P*t+c[0], c[1]), (-c[0], -c[1]), L, h


def remainder_zero(f, modulus):
    for i in range(len(f) - 1, len(modulus) - 2, -1):
        a, b = f[i]
        shift = i - len(modulus) + 1
        for j, c in enumerate(modulus):
            u, v = f[shift+j]
            f[shift+j] = u - a*c, v - b*c
    return all(x == (0, 0) for x in f)


def check_gram(q, p, n, block):
    # Compute the Gram matrix of the actual list, multiplied by P²,
    # in Z[β][X]/Φ_q(X). Keep repeated correction vectors as a multiplicity.
    P, A, B, L, h = block
    modulus = cyclotomic(q)
    units = [u for u in range(q) if gcd(u,q)==1]
    coeff = [qmul(x, conj(y), n) for x,y in ((A,A),(A,B),(B,A),(B,B))]
    for s in units:
        for t in units:
            f = [(0,0)] * q

            def add(k, value):
                i = k % q
                f[i] = (f[i][0]+value[0], f[i][1]+value[1])

            for j in range(q//p):
                for k in range(1,p):
                    v = j + (q//p)*k
                    for e, val in zip((s*v-t*v,s*v-t*j,s*j-t*v,s*j-t*j),coeff):
                        add(e,val)
                add((s-t)*j,(L*P*P,0))
            if s == t:
                add(0,(-P*P*h,0))
            assert remainder_zero(f,modulus), (q,p,s,t)
    return len(units)**2


def check_different(q, p, a, units):
    # v_p of the cyclotomic derivative read from its individual root distances.
    # Each factor of order p^i contributes 1/φ(p^i); other factors are units.
    frequencies = Counter(q//gcd(q,1-u) for u in units if u!=1)
    v = sum(Fraction(frequencies[p**i],(p-1)*p**(i-1)) for i in range(1,a+1))
    assert v == a - Fraction(1,p-1), (q,p,v)


def main():
    results = []
    for q,n,direct in [(2,6,True),(3,6,True),(4,6,True),(8,6,True),(9,6,True),
                       (12,6,True),(18,6,True),(20,20,True),(30,90,True),(45,90,True),
                       (60,90,True),(72,6,True),(5040,210,False),(2**12*3**3,6,False)]:
        # d = 4n-1 equals 23, 79, 359, or 839 (all prime).
        units = [u for u in range(q) if gcd(q,u)==1]
        checks = {}
        for reduced in (True,False):
            total, entries = 0, 0
            for p,a in factor(q).items():
                assert n % p == 0
                block = local_frame(q,p,a,n,reduced)
                total += block[-1]
                if direct:
                    entries += check_gram(q,p,n,block)
                check_different(q,p,a,units)
            assert gcd(q,total)==1
            bound = (4*q**5*(1+n)**2 if reduced else
                     9*q*q*(4*n-1)**(2*(q-1).bit_length()))
            assert 0 < total <= bound
            checks['reduced' if reduced else 'unreduced'] = dict(
                frame_length=str(total),exact_gram_entries=entries,height_bound=str(bound))
        results.append(dict(q=q,d=4*n-1,**checks,different_and_congruence_checks='pass'))
    print(json.dumps(results,indent=2))


if __name__ == "__main__":
    main()
