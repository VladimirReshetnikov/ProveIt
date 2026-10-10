#!/usr/bin/env python3
"""Audit stored rational residual enclosures (standard library only).

This checks the JSON endpoint arithmetic and reported widths. It does not
re-evaluate polylogarithms or turn a small residual into an equality proof.
Run verify.py to reconstruct the enclosures from the analytic formulas.
"""
from __future__ import annotations
import json
from fractions import Fraction
from pathlib import Path


def interval(record: dict) -> tuple[Fraction, Fraction]:
    digits = record['decimal_scale']
    if not isinstance(digits, int) or digits < 0:
        raise ValueError('Invalid decimal scale')
    denominator = 10**digits
    lo = Fraction(int(record['lower_integer']), denominator)
    hi = Fraction(int(record['upper_integer']), denominator)
    if lo > hi:
        raise ValueError('Reversed interval')
    return lo, hi


def main() -> None:
    root = Path(__file__).resolve().parents[1]
    certificates = json.loads((root/'data/certificates.json').read_text())
    summary = json.loads((root/'data/verification.json').read_text())
    tolerance = Fraction(1, 10**summary['target_decimal_digits'])
    maximum = Fraction(0)
    coordinates = 0
    names = set()
    for cert in certificates:
        if cert['name'] in names:
            raise ValueError('Duplicate certificate name')
        names.add(cert['name'])
        residual = cert['residual']
        parts = [residual] if 'decimal_scale' in residual else [residual['real'], residual['imag']]
        for part in parts:
            lo, hi = interval(part)
            if not lo <= 0 <= hi:
                raise ArithmeticError(f"Zero excluded: {cert['name']}")
            if not hi-lo < tolerance:
                raise ArithmeticError(f"Width requirement failed: {cert['name']}")
            maximum = max(maximum, hi-lo)
            coordinates += 1
        if 'residual_width' in cert and len(parts) == 1:
            lo, hi = interval(parts[0])
            if Fraction(cert['residual_width']) != hi-lo:
                raise ArithmeticError('Incorrect recorded width')
    if len(certificates) != summary['total_interval_certificates']:
        raise ValueError('Certificate count differs from summary')
    report = {'certificate_count': len(certificates),
              'real_coordinate_count': coordinates,
              'all_contain_zero': True,
              'all_widths_below_1e_minus_35': maximum < Fraction(1,10**35),
              'maximum_residual_width': str(maximum),
              'interpretation': 'Rational enclosure audit, not an equality proof.'}
    (root/'data/certificate_audit.json').write_text(json.dumps(report, indent=2)+'\n')
    print(json.dumps(report, indent=2))


if __name__ == '__main__':
    main()
