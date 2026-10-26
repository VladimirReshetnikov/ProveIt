#!/usr/bin/env python3
"""Evaluate a delivered integer polynomial, exactly or modulo a positive integer.

Registers in the JSON file are polynomial abbreviations. The only arguments
are its declared input variables. A modular zero is not an integer solution.
This evaluator is a convenience tool; verify_projections.py supplies the
independent algebraic verification of the circuit.
"""
import argparse
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent


def evaluate(artifact, values, modulus=None):
    if len(values) != len(artifact['variables']):
        raise ValueError('wrong number of integer inputs')
    if any(type(value) is not int for value in values):
        raise ValueError('every input must be an integer; booleans are not integers here')
    if modulus is not None and (type(modulus) is not int or modulus < 2):
        raise ValueError('modulus must be an integer at least two')
    live, pending = set(), [artifact['output']]
    while pending:
        index = pending.pop()
        if index in live:
            continue
        live.add(index)
        node = artifact['nodes'][index]
        if node[0] in ('+', '-', '*'):
            pending.extend(node[1:])
    registers = []
    for index, node in enumerate(artifact['nodes']):
        if index not in live:
            registers.append(None)
            continue
        operation = node[0]
        if operation == 'var':
            value = values[node[1]]
        elif operation == 'const':
            value = node[1]
        else:
            if operation not in ('+', '-', '*') or not all(0 <= j < index for j in node[1:]):
                raise ValueError('invalid arithmetic circuit')
            left, right = (registers[j] for j in node[1:])
            value = left + right if operation == '+' else left - right if operation == '-' else left * right
        registers.append(value if modulus is None else value % modulus)
    return registers[artifact['output']], [registers[j] for j in artifact['residual_roots']]


def main():
    profiles = sorted(path.stem for path in (ROOT / 'equations').glob('*.json'))
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--profile', choices=profiles, default='integer111_degree32')
    parser.add_argument('--tuple', type=Path, help='JSON array of integer inputs in declared order')
    parser.add_argument('--zero', action='store_true', help='evaluate the all-zero tuple for a smoke check')
    parser.add_argument('--variables', action='store_true', help='print the exact input order and exit')
    parser.add_argument('--modulus', type=int, help='evaluate in Z/mZ; this does not decide integer solvability')
    parser.add_argument('--residuals', action='store_true', help='also print every retained residual value')
    args = parser.parse_args()
    artifact = json.loads((ROOT / 'equations' / (args.profile + '.json')).read_text())
    if args.variables:
        print(json.dumps(artifact['variables'], indent=2))
        return
    if bool(args.tuple) == bool(args.zero):
        parser.error('specify exactly one of --tuple FILE or --zero')
    values = json.loads(args.tuple.read_text()) if args.tuple else [0] * len(artifact['variables'])
    if type(values) is not list:
        parser.error('the tuple file must contain a JSON array')
    try:
        value, residuals = evaluate(artifact, values, args.modulus)
    except ValueError as error:
        parser.error(str(error))
    result = {'profile': args.profile, 'domain': 'Z' if args.modulus is None else 'Z/%dZ' % args.modulus,
              'value': value, 'is_zero': value == 0}
    if args.residuals:
        result['residual_values'] = residuals
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
