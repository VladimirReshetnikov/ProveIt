#!/usr/bin/env python3
"""Independently evaluate a sparse sum-of-squares export and its assignment.

This checks arithmetic satisfaction and domains, not compiler correctness
or uniqueness for all possible inputs. No imports from the compiler are used.
"""
from __future__ import annotations
import argparse
import json
from pathlib import Path


def verify(path: Path, assignment_path: Path | None = None) -> dict:
    document = json.loads(path.read_text(encoding='utf-8'))
    if document.get('format') != 'sum-of-squares-quartic-v1':
        raise ValueError('Unsupported polynomial format.')
    values = (json.loads(assignment_path.read_text(encoding='utf-8'))
              if assignment_path else document['sample_assignment'])
    parameters = document['free_parameters']
    witnesses = (document['primary_natural_witnesses']
                 + document['auxiliary_natural_witnesses'])
    declared = parameters + witnesses
    if len(set(declared)) != len(declared):
        raise ValueError('Duplicate variable declarations.')
    if set(values) != set(declared):
        raise ValueError('Assignment does not match declared variables.')
    if any(type(values[name]) is not int for name in declared):
        raise ValueError('All assigned values must be integers.')
    if any(values[name] < 0 for name in witnesses):
        raise ValueError('Existential witnesses must be natural.')
    if 'T' in parameters and values['T'] < 0:
        raise ValueError('The horizon must be natural.')
    squared_sum, maximum_degree, failures = 0, 0, []
    for index, residual in enumerate(document['residuals']):
        value = 0
        for term in residual['terms']:
            product = term['coefficient']
            if type(product) is not int:
                raise ValueError('Noninteger polynomial coefficient.')
            monomial = term['variables']
            maximum_degree = max(maximum_degree, len(monomial))
            if len(monomial) > 2:
                raise ValueError('A residual exceeds quadratic degree.')
            for variable in monomial:
                product *= values[variable]
            value += product
        squared_sum += value * value
        if value:
            failures.append(index)
    return {
        'residuals': len(document['residuals']),
        'natural_witnesses': len(witnesses),
        'maximum_residual_degree': maximum_degree,
        'sum_of_squares_value': squared_sum,
        'failed_residual_indices': failures,
        'assignment_satisfies_polynomial': squared_sum == 0,
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('polynomial', type=Path)
    parser.add_argument('--assignment', type=Path)
    args = parser.parse_args()
    try:
        result = verify(args.polynomial, args.assignment)
    except (OSError, ValueError, KeyError, TypeError) as error:
        parser.exit(2, f'Invalid export or assignment: {error}\n')
    print(json.dumps(result, indent=2))
    if not result['assignment_satisfies_polynomial']:
        parser.exit(1)


if __name__ == '__main__':
    main()
