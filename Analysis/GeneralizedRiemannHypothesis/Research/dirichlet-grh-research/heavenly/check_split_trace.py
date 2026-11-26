"""Independent Hasse congruence check for the range 211 < ell <= 253507."""
from collections import Counter
from math import isqrt


def primes_up_to(limit):
    sieve = bytearray([1]) * (limit + 1)
    sieve[:2] = bytes(2)
    for p in range(2, isqrt(limit) + 1):
        if sieve[p]:
            count = (limit - p*p) // p + 1
            sieve[p*p::p] = bytes(count)
    return [p for p, value in enumerate(sieve) if value]


def has_possible_trace(p, ell):
    # Called only for ell = 3 (mod 4) and p a nonzero square modulo ell.
    for degree in (1, 3):
        norm = p**degree
        root = pow(norm, (ell + 1) // 4, ell)
        if root**2 % ell != norm % ell:
            raise ArithmeticError("Incorrect modular square root")
        absolute_minimum = min((scale * root) % ell for scale in (-2, -1, 1, 2))
        if absolute_minimum <= isqrt(4 * norm):
            return True
    return False


def main():
    witnesses = Counter()
    survivors = []
    tests = primes_up_to(43)
    for ell in primes_up_to(253507):
        if ell <= 211 or ell % 4 != 3:
            continue
        for p in tests:
            if pow(p, (ell - 1) // 2, ell) == 1 and not has_possible_trace(p, ell):
                witnesses[p] += 1
                break
        else:
            survivors.append(ell)
    expected = [283, 307, 331, 379, 499, 547, 643, 883, 907, 4027]
    if survivors != expected:
        raise ArithmeticError(survivors)
    print("Survivors:", ", ".join(map(str, survivors)))
    print("Eliminated primes:", sum(witnesses.values()))
    print("Number removed by each first quadratic-residue witness:")
    for prime, count in sorted(witnesses.items()):
        print(prime, count)


if __name__ == "__main__":
    main()
