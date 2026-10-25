#!/usr/bin/env python3
"""Independent finite controls for the new ordinary arithmetic lemmas.

These checks support implementation review; they are not substitutes for
the unbounded proofs in REVIEW.md and the report.
"""
from fractions import Fraction
from itertools import product
from math import comb, factorial, gcd
import json


def require(condition, message):
    if not condition:
        raise ValueError(message)


def ordinates(a, n):
    values = [0, 1]
    while len(values) <= n:
        values.append(2 * a * values[-1] - values[-2])
    return values


def main():
    fixed_points = 0
    for t in range(3, 26):
        target = factorial(t)
        candidates = set(range(2, min(target + 3, 101)))
        candidates.update([target - 1, target, target + 1, target * 2])
        for f in sorted(candidates):
            n = f * f - 1
            b = comb(n, t) if n >= t else 0
            accepted = b >= 2 and n ** t // b == f
            require(accepted == (f == target), ('factorial', t, f))
            fixed_points += 1
        n = target * target - 1
        ratio = Fraction(n ** t, comb(n, t))
        require(target <= ratio < target + 1, ('floor interval', t))
        s = t * (t - 1) // 2
        require(target - 1 > s and n > (target + 1) * s,
                ('floor deficit budget', t))

    reciprocal_cases = 0
    for t in range(3, 13):
        f = factorial(t)
        factors = [f * f // i - 1 for i in range(1, t + 1)]
        b = 1
        for i, d in enumerate(factors, 1):
            require(d > 1 and d % f == f - 1, ('minus factor', t, i))
            require((f * f - 1) % d == i - 1, ('index residue', t, i))
            b *= d
        require(b == comb(f * f - 1, t) and b > f * f,
                ('product', t))
        for i, d in enumerate(factors):
            for e in factors[i + 1:]:
                require(gcd(d, e) == 1, ('coprime factors', t))
        reciprocal_cases += 1

    cap_cases = 0
    accepted_cases = 0
    for w, h, targets in [(8, 5, (1, 2)), (10, 7, (1, 2, 3)),
                          (12, 9, (2, 3, 4)), (16, 5, (1, 1, 2))]:
        a = w ** 3 + 2
        ys = ordinates(a, h + 1)
        for indices in product(range(h + 2), repeat=len(targets)):
            err = sum((ys[j] - k) ** 2 for j, k in zip(indices, targets))
            numerator = ys[h] - h - err
            accepted = numerator >= 0 and numerator % (a - 1) == 0
            require(accepted == (indices == targets),
                    ('one-row cap', w, h, targets, indices))
            cap_cases += 1
            accepted_cases += int(accepted)

    e, ell, tmin = 2 ** 23, 2 ** 22, 12
    fmin = factorial(tmin)
    exponent = fmin.bit_length() - 1
    require(exponent * e < 2 ** exponent and 2 * e <= 2 ** exponent,
            'local majorant initial inequalities')
    require(3 * ell * (tmin + 1) <= 2 * fmin,
            'label majorant initial inequality')
    print(json.dumps({
        'factorial_candidate_controls': fixed_points,
        'reciprocal_product_controls': reciprocal_cases,
        'one_row_cap_controls': cap_cases,
        'canonical_cap_tuples_accepted': accepted_cases,
        'horizon_12_majorant_controls': True,
        'proof_status': 'Finite controls only; unbounded arguments are separate.',
        'verified': True,
    }, sort_keys=True, indent=2))


if __name__ == '__main__':
    main()
