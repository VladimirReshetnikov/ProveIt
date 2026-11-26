#!/usr/bin/env python3
"""Find 0 < x < y < z with xy+yz+zx=n, or certify that none exists.

Uses only integer operations. The smallest possible x+y is returned.
Run, for example, 'python3 represent.py 1848 1849 100000000000000000001'.
"""
from argparse import ArgumentParser
from math import isqrt


def smallest_pair_sum_solution(n):
    if n <= 0:
        raise ValueError("n must be positive")
    # Let a=x+y and b=x. Then b<a/2 and n+b^2=a(x+z)>a^2,
    # so 3a^2<4n. This bound makes exhaustive failure a certificate.
    for a in range(3, isqrt((4 * n - 1) // 3) + 1):
        residue = -n % a
        for b in range(1, (a - 1) // 2 + 1):
            if b * b % a == residue and n + b * b > a * a:
                z = (n + b * b) // a - b
                return b, a - b, z
    return None


if __name__ == "__main__":
    parser = ArgumentParser(description=__doc__)
    parser.add_argument("n", type=int, nargs="+")
    args = parser.parse_args()
    for n in args.n:
        if n <= 0:
            parser.error("all inputs must be positive")
        triple = smallest_pair_sum_solution(n)
        if triple is None:
            print(f"{n}: no strictly ordered positive representation")
        else:
            x, y, z = triple
            assert 0 < x < y < z and x * y + y * z + z * x == n
            print(f"{n}: (x, y, z) = {triple}, minimum x+y = {x+y}")
