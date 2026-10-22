#!/usr/bin/env python3
"""Emit the 16-positive-variable SOS and its 64-integer-variable conversion.

The conversion x = 1 + u1^2 + u2^2 + u3^2 + u4^2 is surjective onto
positive integers by Lagrange's four-square theorem. Intermediate gate
values in the integer presentation are expressions, not extra witnesses.
"""
import argparse
from collections import Counter
from copy import deepcopy
import hashlib
import json
from pathlib import Path
import random

from verify_fixed_input import require, evaluate, diagonal, validate_source

HERE = Path(__file__).resolve().parent


def ledger(rows):
    count = Counter(row[1] for row in rows)
    return {'multiplication': count['*'],
            'addition_subtraction': count['+'] + count['-'],
            'total': len(rows)}


def build(system):
    positive = deepcopy(system)
    positive['title'] = '16-positive-variable sum of seven squared residuals'
    rows = positive['source']
    for j, (left, right) in enumerate(system['comparisons'], 1):
        residual = 'sos_residual_' + str(j)
        rows.append([residual, '-', left, right])
        rows.append(['sos_square_' + str(j), '*', residual, residual])
    previous = 'sos_square_1'
    for j in range(2, 8):
        output = 'sos_total_' + str(j)
        rows.append([output, '+', previous, 'sos_square_' + str(j)])
        previous = output
    positive['comparisons'] = [[previous, 0]]
    positive['polynomial_output'] = previous
    positive['degree'] = 56
    positive['operations'] = ledger(rows)
    positive['proof'] = 'report.pdf, Sections 1 and 5; sum of integer squares'

    signed = deepcopy(positive)
    signed['title'] = '64-unrestricted-integer-variable polynomial for ZFC inconsistency'
    prefix = []
    signed['witnesses'] = []
    substitutions = {}
    for original in system['witnesses']:
        names = ['u_' + original + '_' + str(j) for j in range(1, 5)]
        signed['witnesses'].extend(names)
        substitutions[original] = {'constant': 1, 'squares': names}
        squares = []
        for name in names:
            square = 'square_' + name
            prefix.append([square, '*', name, name])
            squares.append(square)
        total = squares[0]
        for j, square in enumerate(squares[1:], 2):
            name = 'positive_sum_' + original + '_' + str(j)
            prefix.append([name, '+', total, square])
            total = name
        prefix.append([original, '+', total, 1])
    signed['source'] = prefix + signed['source']
    signed['operations'] = ledger(signed['source'])
    signed['degree'] = 112
    signed['witness_domain'] = 'unrestricted integers, positive, negative or zero'
    signed['primary_substitutions'] = substitutions
    signed['proof'] = 'report.pdf, Section 6; Lagrange four-square theorem and sum of squares'
    signed['domain_conversion_scope'] = (
        'Exactly 64 integer unknowns. All 16 original positive inputs are computed '
        'expressions, and no gate is an additional existential variable.')
    return positive, signed


def verify(system, positive, signed):
    for packet, count, degree in ((positive, 16, 56), (signed, 64, 112)):
        require(len(packet['witnesses']) == count, 'wrong witness count')
        validate_source(packet, [packet['polynomial_output']])
        constants = dict(Bm1=15, Kconstant=11, MC=2, MF=19, W0=8192)
        expansion = diagonal(packet['source'], packet['witnesses'], constants)
        require(len(expansion[packet['polynomial_output']])-1 == degree,
                'exact diagonal degree failed')
    require(positive['operations'] == dict(multiplication=41, addition_subtraction=42, total=83),
            'positive SOS ledger mismatch')
    require(signed['operations'] == dict(multiplication=105, addition_subtraction=106, total=211),
            'integer SOS ledger mismatch')
    rng = random.Random(6411263)
    for _ in range(64):
        values = {v:rng.randrange(-5, 6) for v in signed['witnesses']}
        values.update(dict(Bm1=15, Kconstant=11, MC=2, MF=19, W0=8192))
        old = {c:values[c] for c in signed['fixed_numerals']}
        for variable, recipe in signed['primary_substitutions'].items():
            old[variable] = 1 + sum(values[v]**2 for v in recipe['squares'])
            require(old[variable] > 0, 'positivity conversion failed')
        system_values = evaluate(system['source'], old)
        get = lambda v: v if type(v) is int else system_values[v]
        expected = sum((get(a)-get(b))**2 for a,b in system['comparisons'])
        pos = evaluate(positive['source'], old)[positive['polynomial_output']]
        integer = evaluate(signed['source'], values)[signed['polynomial_output']]
        require(pos == integer == expected, 'SOS or four-square identity failed')
    return {'status':'PASS', 'positive_variables':16, 'positive_degree':56,
            'positive_operations':positive['operations'], 'integer_variables':64,
            'integer_degree':112, 'integer_operations':signed['operations'],
            'signed_assignment_checks':64,
            'diagnostic_constants_are_not_a_compiled_ZFC_program':True,
            'scope':'Exact arithmetic source lift; surjectivity uses Lagrange four-square theorem.'}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output-directory', type=Path, default=HERE)
    args = parser.parse_args()
    raw = (HERE/'fixed_input63_ordinary_system.json').read_bytes()
    system = json.loads(raw)
    positive, signed = build(system)
    receipt = verify(system, positive, signed)
    for packet in (positive, signed):
        packet['parent_system_sha256'] = hashlib.sha256(raw).hexdigest()
    args.output_directory.mkdir(parents=True, exist_ok=True)
    for name, data in [('positive16_sos.json', positive), ('integer64_sos.json', signed),
                       ('sos_variants_checks.json', receipt)]:
        (args.output_directory/name).write_text(json.dumps(data, indent=2)+'\n')
    print(json.dumps(receipt, indent=2))


if __name__ == '__main__':
    main()
