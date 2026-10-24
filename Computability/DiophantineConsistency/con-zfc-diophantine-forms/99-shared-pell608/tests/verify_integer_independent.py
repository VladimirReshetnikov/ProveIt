#!/usr/bin/env python3
"""Independent full finite audit of the guarded unrestricted-integer quartic.

Only the two independently authored checkers in this directory are imported;
none of the construction, export, compression, or arithmetic-macro code is.
"""
from __future__ import annotations

import argparse
from collections import defaultdict
from copy import deepcopy
from hashlib import sha256
import json
from pathlib import Path

from verify_affine_independent import check as check_affine
from verify_terminal_independent import check as check_terminal
from verify_terminal_independent import read_polynomial, require


def check_integer(raw, natural, integer, guards, expanded):
    require(natural['domain'] == 'nonnegative integers', 'natural source domain mismatch')
    require(integer['domain'] == expanded['domain'] == 'unrestricted integers',
            'integer output domain mismatch')
    n = len(natural['variables'])
    m = len(integer['variables'])
    require(guards['natural_variables'] == n, 'guard source count mismatch')
    require(integer['variables'][:n] == natural['variables'], 'natural variable prefix changed')
    r = len(natural['residuals'])
    require(integer['residuals'][:r] == natural['residuals'], 'natural residual prefix changed')

    identity = lambda value: json.dumps(value, sort_keys=True, separators=(',', ':'))
    raw_ids = [identity(value) for value in raw['variables']]
    require(len(set(raw_ids)) == len(raw_ids), 'duplicate raw variable metadata')
    natural_ids = [identity(value) for value in natural['variables']]
    require(len(set(natural_ids)) == n, 'duplicate natural variable metadata')
    natural_lookup = {key: i for i, key in enumerate(natural_ids)}
    gates = {row['gate'] for row in raw['rows'] if row.get('gate') is not None}
    raw_free = set(range(len(raw_ids))) - gates
    require(all(raw_ids[i] in natural_lookup for i in raw_free),
            'an original free input is absent from the natural export')
    expected_inputs = {natural_lookup[raw_ids[i]] for i in raw_free}
    actual_inputs = [entry['input'] for entry in guards['guards']]
    require(len(set(actual_inputs)) == len(actual_inputs), 'duplicate guarded input')
    require(set(actual_inputs) == expected_inputs,
            'guards do not cover precisely the original free inputs')
    require(len(integer['residuals']) == r + len(actual_inputs), 'integer residual count mismatch')
    require(m == n + 3 * len(actual_inputs), 'integer variable count mismatch')
    all_aux = []
    for j, entry in enumerate(guards['guards']):
        variable = entry['input']
        square_variables = entry['square_variables']
        require(len(square_variables) == 3 and len(set(square_variables)) == 3,
                'guard does not have three distinct square variables')
        require(all(type(v) is int and n <= v < m for v in square_variables),
                'guard auxiliary outside fresh variable range')
        expected = {(): 3, (variable,): 8,
                    **{(v, v): -1 for v in square_variables}}
        row = read_polynomial(integer['residuals'][r + j]['terms'],
                              variable_count=m, max_degree=2,
                              context='integer guard ' + str(j))
        require(row == expected, 'integer guard polynomial differs from 8v+3=sum of three squares')
        require(all(integer['variables'][v].get('kind') == 'integer_square'
                    for v in square_variables), 'auxiliary variable kind mismatch')
        all_aux.extend(square_variables)
    require(sorted(all_aux) == list(range(n, m)), 'fresh square variables overlap or are omitted')

    result = defaultdict(int)
    products = 0
    for j, row_data in enumerate(integer['residuals']):
        row = read_polynomial(row_data['terms'], variable_count=m, max_degree=2,
                              context='integer residual ' + str(j))
        for ma, ca in row.items():
            for mb, cb in row.items():
                result[tuple(sorted(ma + mb))] += ca * cb
                products += 1
    result = {monomial: coefficient for monomial, coefficient in result.items() if coefficient}
    actual = read_polynomial(expanded['terms'], variable_count=m, max_degree=4,
                             context='expanded integer quartic')
    require(result == actual, 'integer polynomial is not the exact expanded sum of squares')
    require(expanded['variables'] == m, 'expanded integer variable count mismatch')
    require(max(map(len, actual), default=-1) == 4, 'integer polynomial is not exactly quartic')
    require(all(actual.get((v, v, v, v), 0) == 1 for v in all_aux),
            'fresh square witness lacks its exact monic quartic term')
    return {
        'status': 'PASS',
        'natural_variables': n,
        'integer_variables': m,
        'original_free_inputs_guarded': len(expected_inputs),
        'fresh_square_variables': len(all_aux),
        'retained_gate_variables_without_guards': n - len(expected_inputs),
        'natural_residuals_preserved': r,
        'integer_residuals': len(integer['residuals']),
        'expanded_monomials': len(actual),
        'maximum_absolute_coefficient': max(map(abs, actual.values())),
        'exact_degree': 4,
        'ordered_convolution_pairs': products,
        'method': 'original nongate input coverage, literal guards, exact prefix and independent SOS',
        'domain_proof': ('Legendre three-square theorem gives guards for every natural input; '
                         'integer guards force inputs nonnegative; inverse affine/terminal lifts '
                         'and positive triangular raw gate induction force every raw value natural.'),
        'scope': 'Finite compilation chain and guard structure; parent semantic macros use ordinary proofs.'
    }


def rejected(name, raw, natural, integer, guards, expanded):
    try:
        check_integer(raw, natural, integer, guards, expanded)
    except (ValueError, KeyError, TypeError, IndexError) as error:
        return {'control': name, 'status': 'REJECTED', 'reason': str(error)}
    raise ValueError('corruption control accepted: ' + name)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('directory', type=Path)
    parser.add_argument('--output', type=Path)
    arguments = parser.parse_args()
    names = ['raw_builder.json', 'before_terminal.json', 'elimination_trace.json',
             'equation.json', 'expanded_polynomial.json', 'integer/equation.json',
             'integer/guard_certificate.json', 'integer/expanded_polynomial.json']
    content = {name: (arguments.directory / name).read_bytes() for name in names}
    data = {name: json.loads(value) for name, value in content.items()}
    raw = data['raw_builder.json']
    natural = data['equation.json']
    integer = data['integer/equation.json']
    guards = data['integer/guard_certificate.json']
    expanded = data['integer/expanded_polynomial.json']
    affine_receipt = check_affine(raw, data['before_terminal.json'])
    terminal_receipt = check_terminal(data['before_terminal.json'], data['elimination_trace.json'],
                                     natural, data['expanded_polynomial.json'])
    require(guards['source_sha256'] == sha256(content['equation.json']).hexdigest(),
            'guard certificate source hash mismatch')
    receipt = check_integer(raw, natural, integer, guards, expanded)
    changed_guards = deepcopy(guards)
    changed_guards['guards'].pop(0)
    controls = [rejected('omitted original free input guard', raw, natural, integer,
                         changed_guards, expanded)]
    changed_integer = deepcopy(integer)
    changed_integer['residuals'][len(natural['residuals'])]['terms'][0][0] += 1
    controls.append(rejected('incorrect guard constant', raw, natural, changed_integer,
                             guards, expanded))
    changed_expanded = deepcopy(expanded)
    changed_expanded['terms'][0][0] += 1
    controls.append(rejected('incorrect expanded integer coefficient', raw, natural, integer,
                             guards, changed_expanded))
    receipt['affine_export_check'] = affine_receipt
    receipt['terminal_export_check'] = terminal_receipt
    receipt['corruption_controls'] = controls
    receipt['input_sha256'] = {name: sha256(value).hexdigest() for name, value in content.items()}
    receipt['verifier_sha256'] = sha256(Path(__file__).read_bytes()).hexdigest()
    rendered = json.dumps(receipt, indent=2, sort_keys=True) + '\n'
    if arguments.output:
        arguments.output.write_text(rendered)
    print(rendered, end='')


if __name__ == '__main__':
    main()
