#!/usr/bin/env python3
"""Exercise the finite identities in the proof. Standard library only."""

from argparse import ArgumentParser
from itertools import combinations
from math import prod


def prime(n):
    return n >= 2 and all(n % d for d in range(2, n))


def root(p, a):
    """Least root in [0,p), or sentinel p. Requires p > 0."""
    return next((x for x in range(p) if (x*x) % p == a % p), p)


def sign(p, a):
    if a % p == 0:
        return 0
    return 1 if root(p, a) < p else -1


def floor_sum(p, a):
    return sum(a*i // p for i in range(1, (p+1)//2))


def high_count(p, a):
    h = (p-1)//2
    return sum((a*i) % p > h for i in range(1, h+1))


def audit_prime(p):
    h = (p-1)//2
    units = range(1, p)
    inverses = [0] + [next(y for y in units if x*y % p == 1) for x in units]
    factorial = prod(units) % p
    assert factorial == p-1
    for a in units:
        mate = [0] + [a*inverses[x] % p for x in units]
        assert all(mate[mate[x]] == x for x in units)
        fixed = [x for x in units if x == mate[x]]
        leaders = [x for x in units if x < mate[x]]
        assert len(fixed) + 2*len(leaders) == p-1
        assert (prod(fixed) * pow(a, len(leaders), p)) % p == factorial
        witness = root(p, a)
        assert set(fixed) == ({witness, p-witness} if witness < p else set())
        assert pow(a, h, p) == sign(p, a) % p
        residues = [a*i % p for i in range(1, h+1)]
        assert sorted(min(r, p-r) for r in residues) == list(range(1, h+1))
        assert (-1)**high_count(p, a) == sign(p, a)
        # a+p has the same residue and opposite parity; test an odd lift of every unit.
        odd_lift = a if a % 2 else a+p
        assert floor_sum(p, odd_lift) % 2 == high_count(p, a) % 2
        if p % 4 == 3 and witness < p:
            x = pow(a, (p+1)//4, p)
            assert x*x % p == a
    assert sign(p, -1) == (-1)**h
    assert high_count(p, 2) == h - h//2
    assert sign(p, 2) == (-1)**((p*p-1)//8)
    assert (sign(p, 2) == 1) == (p % 8 in (1, 7))


def audit_pair(p, q):
    h, k = (p-1)//2, (q-1)//2
    below = floor_sum(p, q)
    above = floor_sum(q, p)
    assert below + above == h*k
    assert sign(p, q) == (-1)**below
    assert sign(q, p) == (-1)**above
    assert sign(p, q)*sign(q, p) == (-1)**(h*k)


def main():
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('--limit', type=int, default=127, help='inclusive prime bound')
    args = parser.parse_args()
    if not __debug__:
        parser.error('run without Python optimization so assertions are active')
    if args.limit < 3:
        parser.error('use a bound of at least 3')
    primes = [p for p in range(3, args.limit+1, 2) if prime(p)]
    for p in primes:
        audit_prime(p)
    pairs = 0
    for p, q in combinations(primes, 2):
        audit_pair(p, q)
        pairs += 1
    print(f'Passed for {len(primes)} odd primes through {args.limit}, '
          f'{sum(p-1 for p in primes)} unit residues, {pairs} unordered prime pairs.')
    p, q = 7, 11
    print(f'Example p={p}, q={q}: floor sums {floor_sum(p,q)} + {floor_sum(q,p)}, '
          f'Legendre signs {sign(p,q):+d} and {sign(q,p):+d}, '
          f'least root of {q} modulo {p} is {root(p,q)}.')


if __name__ == '__main__':
    main()
