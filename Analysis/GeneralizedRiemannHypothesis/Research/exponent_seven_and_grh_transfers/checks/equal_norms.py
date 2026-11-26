"""Exhaust the pairs of seventh-power norm equations with equal second coefficient.

Run with Python 3 and the proof-enabled GNU coreutils 9.7 factor build.
The factors are checked against their product before enumerating divisors.
"""
from collections import Counter
from concurrent.futures import ProcessPoolExecutor
from itertools import combinations
from math import isqrt, prod
from subprocess import run
import argparse

FLOOR = 31 * 10**19
LIMIT = 6500


def primes_to(n):
    sieve = bytearray([1]) * (n + 1)
    sieve[:2] = bytes(2)
    for i in range(2, isqrt(n) + 1):
        if sieve[i]:
            sieve[i*i::i] = bytes((n-i*i)//i + 1)
    return [i for i, flag in enumerate(sieve) if flag]


def factor_batch(numbers):
    result = run(['factor'], input=''.join(f'{n}\n' for n in numbers),
                 text=True, capture_output=True, check=True)
    lines = result.stdout.splitlines()
    assert len(lines) == len(numbers)
    for n, line in zip(numbers, lines):
        head, tail = line.split(':')
        factors = [int(value) for value in tail.split()]
        assert int(head) == n == prod(factors)
        yield factors


def divisors(factors):
    values = [1]
    for prime, repeats in Counter(factors).items():
        powers = [prime**k for k in range(1, repeats + 1)]
        values += [v * pk for v in values for pk in powers]
    return values


def inspect(pairs):
    primes = primes_to(700)
    witnesses = [(r, {j*j % r for j in range(1, r)}) for r in primes
                 if r > 2 and 4*r**7 < FLOOR]
    numbers = []
    for p, q in pairs:
        difference = q-p
        numbers.extend((difference, (q**7-p**7)//difference))
    factors = iter(factor_batch(numbers))
    counts = Counter()
    for p, q in pairs:
        d = q**7-p**7
        div = divisors(next(factors)+next(factors))
        counts['pairs'] += 1
        for u in div:
            if u*u > d:
                continue
            v = d//u
            m = 4*p**7 - (v-u)**2
            if m <= FLOOR:
                continue
            counts['candidates'] += 1
            for r, squares in witnesses:
                if -m % r in squares:
                    counts['largest_first_witness'] = max(counts['largest_first_witness'], r)
                    break
            else:
                raise ArithmeticError(f'No witness for p={p}, q={q}, u={u}, M={m}')
    return dict(counts)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--workers', type=int, default=4)
    args = parser.parse_args()
    ps = [p for p in primes_to(LIMIT) if 4*p**7 > FLOOR]
    pairs = list(combinations(ps, 2))
    chunks = (pairs[i:i+384] for i in range(0,len(pairs),384))
    total = Counter()
    with ProcessPoolExecutor(args.workers) as pool:
        for batch in pool.map(inspect, chunks):
            total['pairs'] += batch['pairs']
            total['candidates'] += batch.get('candidates', 0)
            total['largest_first_witness'] = max(total['largest_first_witness'],
                                                  batch.get('largest_first_witness', 0))
    assert total['pairs'] == len(ps)*(len(ps)-1)//2
    print('Limit', LIMIT, 'eligible primes', len(ps), 'floor', FLOOR)
    print(dict(total), 'survivors', 0)


if __name__ == '__main__':
    main()
