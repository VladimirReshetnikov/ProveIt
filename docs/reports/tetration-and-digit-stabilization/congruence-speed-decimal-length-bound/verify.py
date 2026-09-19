#!/usr/bin/env python3
"""Verify the finite certificate and the counterexample, without towers."""
from __future__ import annotations
import argparse
import hashlib
import json
import sys
from pathlib import Path
from tetration_tools import Profile, crt_base, crt_base_euclid


def require(condition: bool, message: str) -> None:
    if not condition:
        raise ArithmeticError(message)


def verify(folder: Path) -> dict:
    text = (folder/'counterexample.txt').read_text(encoding='ascii').strip()
    require(bool(text) and all('0' <= ch <= '9' for ch in text), 'Invalid decimal data')
    require(text[0] != '0', 'Unexpected leading zero')
    a, c = int(text), 2547
    require(a == crt_base(c), 'Decimal integer differs from inverse CRT construction')
    require(a == crt_base_euclid(c), 'Independent Euclidean CRT check failed')
    require(all(crt_base(j) == a for j in range(2544,2548)), 'CRT plateau failed')
    require(crt_base(2548)-a == 9*(2*10**2547), 'Next CRT digit failed')
    require(7*10**2543 < a < 8*10**2543, 'Exact size bounds failed')
    require(a % (1 << 2549) == (1 << 2548)-1, '2-adic certificate failed')
    require(a % (5**2548) == 5**2547 + 1, '5-adic certificate failed')
    require(a % 10 == 1, 'Base not in the conjectured residue classes')
    p = Profile.from_base(a)
    require((p.alpha, p.beta, p.c) == (1,2548,2547), 'Unexpected valuations')
    d = len(text)
    b = d+2
    require(d == 2544 and b == 2546, 'Digit length or height failed')
    require(p.onset == 2547, 'Incorrect sustained onset')
    require(p.speed(b) == 2548, 'Incorrect speed at the conjectured bound')
    require(p.eventual_speed == 2547, 'Incorrect permanent speed')
    # Check the whole transient profile, not merely the exceptional height.
    require(all(p.speed(h) == 2548 for h in range(1,2547)), 'Transient check failed')
    require(p.speed(2547) == p.speed(2548) == 2547, 'Crossover check failed')
    rows = [{
        'height': n, 'v2_delta': p.alpha+n*p.sigma,
        'v5_delta': (n+1)*p.c, 'stable_digits': p.stable(n),
        'raw_gain': p.speed(n)
    } for n in range(2543,2549)]
    return {
        'status': 'PASS', 'base_decimal_digits': d, 'base_bit_length': a.bit_length(),
        'decimal_digits_sha256': hashlib.sha256(text.encode('ascii')).hexdigest(),
        'crt_parameter': c,
        'valuations': {'v2_A_minus_1': p.alpha, 'v2_A_plus_1': p.beta,
                       'v5_A_minus_1': p.c},
        'claimed_sufficient_height': b, 'speed_at_that_height': p.speed(b),
        'eventual_speed': p.eventual_speed, 'exact_sustained_onset': p.onset,
        'leading_80_digits': text[:80], 'trailing_80_digits': text[-80:],
        'crossover_table': rows,
        'finite_checks': ['inverse CRT', 'extended Euclid CRT', 'exact size interval',
                          'exact 2-adic residue', 'exact 5-adic residue',
                          'complete transient gain sequence', 'CRT plateau and next digit'],
        'logical_dependency': 'The all-height claim follows from the proved LTE formulas; no gigantic tower was computed.'
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--directory', type=Path, default=Path(__file__).resolve().parent)
    parser.add_argument('--output', type=Path, help='Optionally write the JSON result.')
    args = parser.parse_args()
    if hasattr(sys, 'set_int_max_str_digits'):
        sys.set_int_max_str_digits(100000)
    try:
        result = verify(args.directory)
    except (ValueError, OSError, ArithmeticError) as exc:
        raise SystemExit(f'FAIL: {exc}') from exc
    rendered = json.dumps(result, indent=2) + '\n'
    if args.output:
        args.output.write_text(rendered, encoding='utf-8')
    print(rendered, end='')

if __name__ == '__main__':
    main()
