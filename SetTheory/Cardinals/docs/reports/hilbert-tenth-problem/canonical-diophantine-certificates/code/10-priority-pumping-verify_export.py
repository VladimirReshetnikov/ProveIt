#!/usr/bin/env python3
"""Independently evaluate an exported sum-of-squares polynomial at a witness.

This verifier deliberately does not import the compiler. It verifies the
polynomial zero, not the mathematical semantics-to-polynomial theorem.
Standard library only, Python >= 3.10.
"""
from __future__ import annotations
import argparse
import json
from pathlib import Path
from typing import Any


def integer(v: Any) -> bool:
    return isinstance(v, int) and not isinstance(v, bool)


def verify(certificate: dict, instance: dict) -> dict:
    names = certificate['variable_order']
    free = certificate['free_inputs']
    vals = instance['values_in_exported_variable_order']
    supplied = instance['free_inputs']
    if not isinstance(names, list) or any(not isinstance(n, str) for n in names):
        raise ValueError('Invalid variable names')
    if len(set(names)) != len(names):
        raise ValueError('Duplicate variable name')
    if len(vals) != len(names) or any(not integer(v) or v < 0 for v in vals):
        raise ValueError('A complete natural-number value vector is required')
    if len(set(free)) != len(free) or set(free) != set(supplied):
        raise ValueError('Free input names do not agree')
    positions = {name: i for i, name in enumerate(names)}
    for name in free:
        if name not in positions or not integer(supplied[name]) or supplied[name] < 0:
            raise ValueError('Invalid free input: ' + name)
        if vals[positions[name]] != supplied[name]:
            raise ValueError('Witness does not use the claimed free input: ' + name)
    nonzero = []
    total = 0
    for ri, terms in enumerate(certificate['residuals']):
        residual = 0
        for term in terms:
            coefficient = term['coefficient']
            variables = term['variables']
            if not integer(coefficient):
                raise ValueError('Non-integer polynomial coefficient')
            if not isinstance(variables, list) or len(variables) > 2:
                raise ValueError('Non-quadratic residual monomial')
            product = coefficient
            for index in variables:
                if not integer(index) or not 0 <= index < len(vals):
                    raise ValueError('Invalid variable index')
                product *= vals[index]
            residual += product
        if residual:
            nonzero.append(ri)
        total += residual * residual
    return {
        'valid_polynomial_zero': total == 0,
        'polynomial_value': total,
        'number_of_variables': len(names),
        'number_of_auxiliaries': len(names) - len(free),
        'number_of_residuals': len(certificate['residuals']),
        'nonzero_residual_indices': nonzero,
        'maximum_value_bit_length': max(vals, default=0).bit_length(),
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('certificate', type=Path)
    parser.add_argument('instance', type=Path)
    args = parser.parse_args()
    try:
        certificate = json.loads(args.certificate.read_text(encoding='utf-8'))
        instance = json.loads(args.instance.read_text(encoding='utf-8'))
        result = verify(certificate, instance)
    except (OSError, ValueError, KeyError, TypeError) as exc:
        parser.exit(2, 'Verification error: ' + str(exc) + '\n')
    print(json.dumps(result, indent=2))
    if not result['valid_polynomial_zero']:
        raise SystemExit(1)


if __name__ == '__main__':
    main()
