"""Independently evaluate an exported sum-of-squares polynomial certificate.

Does not import compiler.py or use witness recipes. JSON integer values are
read as exact Python integers, never floating point.
"""
from __future__ import annotations
import argparse
import json
from pathlib import Path


def verify(polynomial_path: Path, assignment_path: Path) -> dict:
    spec = json.loads(polynomial_path.read_text())
    document = json.loads(assignment_path.read_text())
    env = document.get('assignment', document)
    names = spec['inputs'] + spec['witnesses']
    if len(names) != len(set(names)):
        raise ValueError('Duplicate polynomial variable names')
    if set(names) != set(env):
        raise ValueError('Assignment keys do not match the polynomial variables')
    if any(type(value) is not int or value < 0 for value in env.values()):
        raise ValueError('Every assigned value must be a nonnegative integer')
    energy = 0
    failed = []
    max_degree = 0
    for index, residual in enumerate(spec['residuals']):
        value = 0
        for term in residual:
            coefficient, monomial = term['coefficient'], term['monomial']
            if type(coefficient) is not int:
                raise ValueError('Polynomial coefficients must be integers')
            product = coefficient
            max_degree = max(max_degree, len(monomial))
            for name in monomial:
                product *= env[name]
            value += product
        energy += value*value
        if value:
            failed.append(index)
    return {'valid': energy == 0, 'energy': energy,
            'residual_count': len(spec['residuals']),
            'residual_degree': max_degree,
            'witness_count': len(spec['witnesses']),
            'failed_residual_indices': failed}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('polynomial', type=Path)
    parser.add_argument('assignment', type=Path)
    arguments = parser.parse_args()
    result = verify(arguments.polynomial, arguments.assignment)
    print(json.dumps(result, indent=2))
    raise SystemExit(0 if result['valid'] else 1)


if __name__ == '__main__':
    main()
