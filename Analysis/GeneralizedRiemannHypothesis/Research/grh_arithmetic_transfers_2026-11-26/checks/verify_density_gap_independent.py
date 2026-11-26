"""Independent exact certificate for the inherited McNew density-gap proof.

This checks the finite incompatibility through 12 and a numerical positive
gap. The passage from these finite facts to infinite densities is a paper
argument in prior_notes.md, not something proved by a finite test alone.
Python standard library only; no numerical floating-point arithmetic.
"""
from fractions import Fraction
from math import gcd, isqrt, lcm
import json


def triples(limit, integer_ratios):
    # Every increasing rational GP is t*(b*b,a*b,a*a), gcd(a,b)=1.
    output = set()
    for a in range(2, isqrt(limit) + 1):
        for b in range(1, a):
            if gcd(a, b) != 1 or (integer_ratios and b != 1):
                continue
            for t in range(1, limit // (a * a) + 1):
                output.add((t * b * b, t * a * b, t * a * a))
    return sorted(output)


def finite_certificate(integer_ratios):
    N = 12
    forbidden = triples(N, integer_ratios)
    valid = []
    maxima = [0] * (N + 1)
    for bits in range(2 ** N):
        included = {a for a in range(1, N + 1) if bits >> (a - 1) & 1}
        if any(all(a in included for a in triple) for triple in forbidden):
            continue
        counts = [sum(a <= k for a in included) for k in range(N + 1)]
        maxima = [max(x, y) for x, y in zip(maxima, counts)]
        valid.append((included, counts))
    assert not any(counts == maxima for _, counts in valid)
    assert maxima[-1] == 10
    witness = {1, 2, 5, 6, 7, 8, 9, 10, 11, 12}
    assert any(included == witness for included, _ in valid)
    minimum_integrated_deficit = min(
        sum(Fraction(maxima[k] - counts[k], k * (k + 1))
            for k in range(1, N + 1)) for _, counts in valid
    )
    assert minimum_integrated_deficit >= Fraction(1, 156)
    return {
        'ratios': 'integer' if integer_ratios else 'rational',
        'forbidden_triples': forbidden,
        'prefix_maxima': maxima[1:],
        'no_set_optimizes_every_prefix': True,
        'exact_prefix_loss': str(minimum_integrated_deficit),
        'proof_uses_weaker_loss': '1/156',
    }


def is_prime(n):
    return n >= 2 and all(n % d for d in range(2, isqrt(n) + 1))


def numeric_certificate():
    Y, K, SCALE = 2000, 100000, 10 ** 20
    # Trial division intentionally provides a different prime enumeration
    # from the supplied Eratosthenes implementations.
    ps = [n for n in range(2, K + 1) if is_prime(n)]
    c = Fraction(1)
    tail_scaled_upper = SCALE // K
    for p in ps:
        if p <= Y:
            c *= Fraction(p - 1, p)
        else:
            tail_scaled_upper += (SCALE + p * p - 1) // (p * p)
    # For omitted integers, sum_{n>K} n^-2 <= integral_K^inf t^-2 dt.
    lower = c / 156 - Fraction(tail_scaled_upper, SCALE)
    assert lower > Fraction(404, 10 ** 6)
    return {
        'Y': Y, 'prime_cutoff': K,
        'common_gap_strictly_greater_than': '404/1000000',
        'lower_bound_floor_at_1e18': (lower * 10 ** 18).__floor__(),
        'prime_count': len(ps),
    }


if __name__ == '__main__':
    print(json.dumps({'finite': [finite_certificate(False), finite_certificate(True)],
                      'numeric': numeric_certificate()}, indent=2))
