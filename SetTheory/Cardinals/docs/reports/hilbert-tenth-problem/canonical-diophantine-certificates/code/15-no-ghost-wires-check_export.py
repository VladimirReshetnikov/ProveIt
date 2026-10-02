#!/usr/bin/env python3
"""Evaluate the exported quartic independently of the compiler's Poly class.

Usage: python3 code/check_export.py [--data PATH]
This checks an arithmetic zero, not the compiler's semantic correctness.
"""
from __future__ import annotations

import argparse
import json
from pathlib import Path


def check(data: Path) -> tuple[int, int, int, int]:
    spec = json.loads((data / 'quartic_A_schedule.json').read_text(encoding='utf-8'))
    values = json.loads((data / 'witness_A.json').read_text(encoding='utf-8'))
    names = spec['parameters'] + spec['witnesses']
    if len(names) != len(set(names)) or set(values) != set(names):
        raise ValueError('The variable list or assignment is not exact.')
    if any(type(v) is not int or v < 0 for v in values.values()):
        raise ValueError('All coordinates must be nonnegative integers, not booleans.')
    energy = 0
    for residual in spec['residuals']:
        total = 0
        for coefficient, monomial in residual['terms']:
            if type(coefficient) is not int or len(monomial) > 2:
                raise ValueError('A residual is not an integer quadratic.')
            term = coefficient
            for name in monomial:
                term *= values[name]
            total += term
        energy += total * total
    if energy:
        raise ValueError(f'The saved assignment has nonzero energy: {energy}')
    return len(spec['parameters']), len(spec['witnesses']), len(spec['residuals']), energy


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--data', type=Path,
                        default=Path(__file__).resolve().parents[1] / 'data')
    args = parser.parse_args()
    try:
        p, w, r, q = check(args.data)
    except (OSError, ValueError, KeyError, TypeError) as exc:
        parser.exit(1, f'FAIL: {exc}\n')
    print(f'PASS: {p} parameters, {w} witnesses, {r} residuals, energy {q}')


if __name__ == '__main__':
    main()
