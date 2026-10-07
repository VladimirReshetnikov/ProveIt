#!/usr/bin/env python3
"""Negative tests for the exact certificate verifier; standard library only."""
from __future__ import annotations

from copy import deepcopy
import json
from pathlib import Path

import verify_exact as v


def main() -> None:
    root = Path(__file__).resolve().parent
    original = json.loads((root/'data'/'ternary_quartic_gram.json').read_text())
    g = v.line_variables()
    basis, k2 = v.monomial_basis(g), v.doubled_line_polynomial(g)
    tests = (
        ('Gram coefficient', 'QA', 0, 0, 1, 'm* Q m = 153-K failed'),
        ('equality kernel', 'KA', 0, 0, 1, 'is not a family coefficient vector'),
        ('positivity witness', 'LA', 0, 0, 10**9, 'Gershgorin lower bound'),
    )
    for label, key, row, col, delta, expected in tests:
        altered = deepcopy(original)
        altered[key][row][col] += delta
        try:
            v.verify_gram(altered, basis, k2)
        except v.VerificationError as error:
            v.require(expected in str(error), f'{label}: unexpected rejection: {error}')
            print(f'PASS: altered {label} rejected ({error})')
        else:
            raise v.VerificationError(f'altered {label} incorrectly accepted')
    # Check the nontrivial conjugation rule on a small exhaustive integer box.
    for a in range(-3,4):
        for b in range(-3,4):
            x = (a,b)
            v.require(v.conj(v.conj(x)) == x, 'conjugation involution')
            v.require(v.mul(x,v.conj(x)) == (a*a-a*b+b*b,0), 'cyclotomic norm')
    print('PASS: integer-pair conjugation and norm identities')


if __name__ == '__main__':
    main()
