#!/usr/bin/env python3
"""Finite evidence for the explicitly unproved full-support/sign conjecture."""
import json
from pathlib import Path
from normal_forms import raw_polynomials, normal_reduce, partitions_weight


def main():
    rows = []
    for m, polynomial in enumerate(raw_polynomials(24)):
        if m < 2:
            continue
        _, companion = normal_reduce(polynomial)
        expected = set(partitions_weight(m - 1))
        assert set(companion) == expected
        assert all(coefficient * (-1) ** (m - sum(exponents)) > 0
                   for exponents, coefficient in companion.items())
        rows.append({'weight': m, 'monomials': len(companion),
                     'full_support': True, 'predicted_signs': True})
    record = {'scope': 'finite evidence only; the all-weight assertion is a conjecture',
              'min_weight': 2, 'max_weight': 24, 'rows': rows}
    Path(__file__).with_name('compensator_signs.json').write_text(json.dumps(record, indent=2) + '\n')
    print('PASS: full support and sign pattern at each weight 2 through 24; no all-weight proof claimed.')


if __name__ == '__main__':
    main()
