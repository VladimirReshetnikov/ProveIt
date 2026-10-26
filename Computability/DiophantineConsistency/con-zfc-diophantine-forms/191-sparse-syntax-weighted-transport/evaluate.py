#!/usr/bin/env python3
"""Evaluate a delivered equation at an explicit tuple; never search for zeros."""
from pathlib import Path
import argparse
import gzip
import hashlib
import json
import sys

ROOT = Path(__file__).resolve().parent


def require(condition, message):
    if not condition:
        raise ValueError(message)


def evaluate_direct(equation, values, modulus):
    require(len(values) == len(equation['variables']), 'Wrong integer tuple length')
    total = 0
    for row in equation['residuals']:
        value = 0
        for coefficient, indices in row['terms']:
            term = coefficient
            for index in indices:
                term *= values[index]
            value += term
        if modulus:
            value %= modulus
        total += value * value
        if modulus:
            total %= modulus
    return total


def evaluate_compact(equation, values, modulus):
    require(len(values) == len(equation['witnesses']), 'Wrong positive tuple length')
    require(all(value > 0 for value in values), 'This theorem requires strictly positive inputs')
    registers = dict(zip(equation['witnesses'], values))
    binding = equation['coefficient_binding']
    for name, meta in binding['ports'].items():
        raw = gzip.decompress((ROOT/'positive190'/binding['path']/meta['file']).read_bytes())
        require(hashlib.sha256(raw).hexdigest() == meta['raw_sha256'], 'Fixed coefficient hash mismatch')
        value = int.from_bytes(raw, binding['endianness'])
        registers[name] = value % modulus if modulus else value

    def fetch(item):
        return item if type(item) is int else registers[item]

    for target, operation, left, right in equation['source']:
        require(target not in registers, 'Register is assigned twice')
        a, b = fetch(left), fetch(right)
        if operation == '+':
            value = a + b
        elif operation == '-':
            value = a - b
        elif operation == '*':
            value = a * b
        else:
            raise ValueError('Unsupported arithmetic operation')
        registers[target] = value % modulus if modulus else value
    return registers[equation['output']]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('equation', choices=['direct208', 'positive190'])
    parser.add_argument('tuple_file', help='JSON integer list, or - to read standard input')
    parser.add_argument('--mod', type=int, default=None,
                        help='Optional positive modulus; zero modulo it is not an integer zero')
    parser.add_argument('--hex', action='store_true',
                        help='Include the complete value in hexadecimal; exact values can be enormous')
    args = parser.parse_args()
    require(args.mod is None or args.mod > 1, 'Modulus must exceed one')
    text = sys.stdin.read() if args.tuple_file == '-' else Path(args.tuple_file).read_text()
    values = json.loads(text)
    require(isinstance(values, list) and all(type(value) is int for value in values),
            'The input must be a JSON list of integers, with no Boolean values')
    folder = ROOT/args.equation
    if args.equation == 'direct208':
        folder = folder/'equations/principal208'
    equation = json.loads((folder/'equation.json').read_text())
    function = evaluate_direct if args.equation == 'direct208' else evaluate_compact
    value = function(equation, values, args.mod)
    result = {'equation': args.equation, 'inputs': len(values), 'modulus': args.mod,
              'sign': (value > 0)-(value < 0), 'absolute_value_bits': abs(value).bit_length()}
    if args.mod:
        result['residue'] = value
        result['interpretation'] = 'Modular diagnostic only; not an assertion of an integer zero'
    else:
        result['is_integer_zero'] = value == 0
    if args.hex:
        result['value_hex'] = hex(value)
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
