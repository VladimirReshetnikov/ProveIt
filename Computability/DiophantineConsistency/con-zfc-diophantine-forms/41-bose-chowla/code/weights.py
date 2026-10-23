#!/usr/bin/env python3
"""Reproduce and exhaustively certify the 32-element B_4 coding set.

No third-party dependencies.  The decisive certificate is the exhaustive
integer computation: all 52,360 multisets of four weights have distinct
residues modulo 2^20-1.  The field construction is explanatory and redundant.

The construction is the classical Bose--Chowla construction in GF(32^4),
represented as GF(2)[x]/(x^20+x^3+1), with a cyclic rotation that removes
the largest gap.  The zero weight is the padding coordinate for monomials
of total degree at most four; the other 31 weights encode source variables.
"""
from itertools import combinations_with_replacement
from pathlib import Path
import argparse
import hashlib
import json

MODULUS = (1 << 20) - 1
REDUCTION = (1 << 3) | 1
MULTIPLIER = 208418
ROTATION = 97920
EXPECTED = [0, 51609, 55430, 68596, 78030, 89463, 90233, 110498,
            110508, 128615, 136498, 211819, 241519, 305379, 312706,
            314312, 369115, 417382, 429683, 435112, 450230, 462314,
            469608, 490199, 501539, 507151, 524944, 550792, 559943,
            573626, 607799, 610895]


def construct():
    """Generate all nonzero elements; this also certifies primitivity."""
    logarithm = [-1] * (MODULUS + 1)
    powers = []
    value = 1
    for exponent in range(MODULUS):
        assert 0 < value <= MODULUS
        assert logarithm[value] == -1
        logarithm[value] = exponent
        powers.append(value)
        value <<= 1
        if value & (1 << 20):
            value = (value & MODULUS) ^ REDUCTION
    assert value == 1
    assert all(e >= 0 for e in logarithm[1:])
    subfield = [0] + [powers[k * (MODULUS // 31)] for k in range(31)]
    # theta = x has integer representation 2; addition is xor.
    raw = sorted(logarithm[2 ^ a] for a in subfield)
    from math import gcd
    assert gcd(MULTIPLIER, MODULUS) == 1
    scaled = sorted(a * MULTIPLIER % MODULUS for a in raw)
    largest_gap, before = max(((scaled[(i + 1) % 32] - scaled[i]) % MODULUS, i)
                              for i in range(32))
    rotation = scaled[(before + 1) % 32]
    assert rotation == ROTATION
    weights = sorted((a - rotation) % MODULUS for a in scaled)
    assert weights == EXPECTED
    return dict(field_polynomial='x^20+x^3+1',
                field_modulus=(1 << 20) | REDUCTION,
                multiplicative_order=MODULUS, subfield_size=32,
                raw_logs=raw, multiplier=MULTIPLIER,
                rotation=rotation, largest_gap=largest_gap,
                weights=weights, maximum=max(weights))


def verify(weights=EXPECTED):
    assert len(weights) == 32 and weights[0] == 0
    assert weights == sorted(set(weights))
    seen = {}
    digest = hashlib.sha256()
    for indices in combinations_with_replacement(range(32), 4):
        integer_sum = sum(weights[i] for i in indices)
        residue = integer_sum % MODULUS
        assert residue not in seen, (indices, seen.get(residue))
        seen[residue] = indices
        digest.update(bytes(indices))
        digest.update(integer_sum.to_bytes(4, 'little'))
    assert len(seen) == 52360
    return dict(multisets_checked=len(seen), injective_modulus=MODULUS,
                integer_sum_range=[0, 4 * weights[-1]],
                enumeration_sha256=digest.hexdigest(),
                target_exponent=4 * weights[-1],
                maximum_product_exponent=8 * weights[-1])


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--output', type=Path,
                        default=Path(__file__).with_name('weights_certificate.json'))
    parser.add_argument('--verify-only', action='store_true')
    args = parser.parse_args()
    result = ({'weights': EXPECTED, 'maximum': EXPECTED[-1]}
              if args.verify_only else construct())
    result.update(verify(result['weights']))
    args.output.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps({'maximum': result['maximum'],
                      'multisets_checked': result['multisets_checked'],
                      'target_exponent': result['target_exponent'],
                      'maximum_product_exponent': result['maximum_product_exponent'],
                      'certificate': str(args.output)}))


if __name__ == '__main__':
    main()
