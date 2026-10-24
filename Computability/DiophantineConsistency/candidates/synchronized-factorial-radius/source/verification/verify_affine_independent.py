#!/usr/bin/env python3
"""Check raw monotone gate residuals against a flattened natural export.

The retained variables are taken from the proposed result; its selection
heuristic is not replayed. Instead, every omitted affine wire needed by a
retained row is reconstructed from its independently checked raw definition.
All raw semantic constraints and retained defining equations are compared.
"""
from __future__ import annotations

import argparse
from collections import defaultdict
from copy import deepcopy
from functools import lru_cache
from hashlib import sha256
import json
from pathlib import Path


def require(condition, message):
    if not condition:
        raise ValueError(message)


def parse(terms, count, label):
    result = {}
    for coefficient, monomial_list in terms:
        require(type(coefficient) is int and coefficient != 0, label + ': bad coefficient')
        monomial = tuple(monomial_list)
        require(monomial == tuple(sorted(monomial)), label + ': unsorted monomial')
        require(len(monomial) <= 2, label + ': degree exceeds two')
        require(all(type(v) is int and 0 <= v < count for v in monomial),
                label + ': invalid variable')
        require(monomial not in result, label + ': duplicate monomial')
        result[monomial] = coefficient
    return result


def accumulate(target, monomial, coefficient):
    updated = target.get(monomial, 0) + coefficient
    if updated:
        target[monomial] = updated
    else:
        target.pop(monomial, None)


def multiply(left, right):
    out = {}
    for a, c in left.items():
        for b, d in right.items():
            accumulate(out, tuple(sorted(a + b)), c * d)
    return out


def check(raw, before):
    require(before['domain'] == 'nonnegative integers', 'wrong export domain')
    variables = raw['variables']
    original_rows = raw['rows']
    count = len(variables)
    identity = lambda value: json.dumps(value, sort_keys=True, separators=(',', ':'))
    identities = [identity(value) for value in variables]
    require(len(set(identities)) == count, 'raw variable metadata is not unique')
    by_identity = {key: i for i, key in enumerate(identities)}
    retained = [by_identity.get(identity(value)) for value in before['variables']]
    require(None not in retained, 'export has an unrecognized variable')
    require(retained == sorted(set(retained)), 'export variables not a sorted raw subset')
    retained_set = set(retained)
    renaming = {old: new for new, old in enumerate(retained)}

    rows = []
    definitions = {}
    gate_rows = {}
    for i, row in enumerate(original_rows):
        polynomial = parse(row['terms'], count, 'raw row ' + str(i))
        rows.append(polynomial)
        gate = row.get('gate')
        if gate is None:
            continue
        require(type(gate) is int and 0 <= gate < count, 'invalid raw gate index')
        require(gate not in definitions, 'duplicate defining gate')
        require(polynomial.get((gate,), 0) == 1, 'raw gate is not monic positive')
        require(all(gate not in m or m == (gate,) for m in polynomial),
                'raw gate has a nonlinear self-reference')
        recipe = {m: -c for m, c in polynomial.items() if m != (gate,)}
        require(all(c > 0 for c in recipe.values()), 'raw gate is not nonnegative')
        require(all(v < gate for m in recipe for v in m), 'raw gate is not triangular')
        definitions[gate] = recipe
        gate_rows[gate] = i

    expanded_affine = {}

    @lru_cache(maxsize=None)
    def resolve(variable):
        if variable in retained_set:
            return {(variable,): 1}
        require(variable in definitions,
                'a required unconstrained input was omitted: ' + str(variable))
        recipe = definitions[variable]
        require(all(len(m) <= 1 for m in recipe),
                'a required nonlinear gate was omitted: ' + str(variable))
        result = {}
        for monomial, coefficient in recipe.items():
            if monomial:
                for child, value in resolve(monomial[0]).items():
                    accumulate(result, child, coefficient * value)
            else:
                accumulate(result, (), coefficient)
        require(all(c > 0 and len(m) <= 1 for m, c in result.items()),
                'restored affine gate is not nonnegative affine')
        require(len(result) <= 4, 'needed omitted affine gate exceeds declared support cap')
        expanded_affine[variable] = result
        return result

    transformed = []
    retained_raw_row_ids = []
    for i, row in enumerate(original_rows):
        gate = row.get('gate')
        if gate is not None and gate not in retained_set:
            continue
        image = {}
        for monomial, coefficient in rows[i].items():
            term = {(): coefficient}
            for variable in monomial:
                term = multiply(term, resolve(variable))
            for m, c in term.items():
                accumulate(image, m, c)
        require(all(len(m) <= 2 for m in image), 'flattening raised residual degree')
        require(all(v in retained_set for m in image for v in m),
                'flattening left an omitted variable')
        if not image:
            continue
        renamed = {tuple(renaming[v] for v in m): c for m, c in image.items()}
        transformed.append((row.get('label'), renamed))
        retained_raw_row_ids.append(i)
    require(len(transformed) == len(before['residuals']), 'flattened row count mismatch')
    for i, ((label, expected), actual_row) in enumerate(zip(transformed, before['residuals'])):
        require(label == actual_row.get('label'), 'flattened label mismatch at ' + str(i))
        actual = parse(actual_row['terms'], len(retained), 'export row ' + str(i))
        require(expected == actual, 'flattened polynomial mismatch at ' + str(i))

    # Every discarded gate can be filled in in ascending raw order using its
    # positive triangular recipe. Any omitted raw input occurs in no required
    # constraint, as resolve would have rejected it above, and can start at zero.
    omitted_inputs = [i for i in range(count) if i not in retained_set and i not in definitions]
    omitted_gate_count = sum(i not in retained_set for i in definitions)
    needed_affine = len(expanded_affine)
    return {
        'status': 'PASS',
        'method': 'exact reconstruction from proposed retained subset; selection heuristic not imported',
        'raw_variables': count,
        'raw_rows': len(original_rows),
        'checked_total_nonnegative_triangular_gate_definitions': len(definitions),
        'retained_variables': len(retained),
        'retained_rows': len(transformed),
        'needed_omitted_affine_gates_checked': needed_affine,
        'other_omitted_definitional_gates': omitted_gate_count - needed_affine,
        'omitted_unconstrained_inputs': len(omitted_inputs),
        'largest_needed_affine_support': max(map(len, expanded_affine.values()), default=0),
        'retained_raw_row_ids_sha256': sha256(json.dumps(retained_raw_row_ids).encode()).hexdigest(),
        'scope': 'Raw residuals to affine export only; arithmetic macro correctness requires ordinary proofs.'
    }


def reject_control(name, raw, before):
    try:
        check(raw, before)
    except (ValueError, KeyError, TypeError, IndexError) as error:
        return {'control': name, 'status': 'REJECTED', 'reason': str(error)}
    raise ValueError('corruption control accepted: ' + name)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('directory', type=Path)
    parser.add_argument('--output', type=Path)
    arguments = parser.parse_args()
    raw_bytes = (arguments.directory / 'raw_builder.json').read_bytes()
    before_bytes = (arguments.directory / 'before_terminal.json').read_bytes()
    raw, before = json.loads(raw_bytes), json.loads(before_bytes)
    receipt = check(raw, before)
    modified_before = deepcopy(before)
    modified_before['residuals'][0]['terms'][0][0] *= -1
    controls = [reject_control('altered affine export coefficient', raw, modified_before)]
    modified_raw = deepcopy(raw)
    gate_row = next(r for r in modified_raw['rows'] if r.get('gate') is not None)
    for term in gate_row['terms']:
        if term[1] == [gate_row['gate']]:
            term[0] = 2
            break
    controls.append(reject_control('nonunit raw defining coefficient', modified_raw, before))
    receipt['corruption_controls'] = controls
    receipt['input_sha256'] = {'raw_builder.json': sha256(raw_bytes).hexdigest(),
                             'before_terminal.json': sha256(before_bytes).hexdigest()}
    receipt['verifier_sha256'] = sha256(Path(__file__).read_bytes()).hexdigest()
    rendered = json.dumps(receipt, indent=2, sort_keys=True) + '\n'
    if arguments.output:
        arguments.output.write_text(rendered)
    print(rendered, end='')


if __name__ == '__main__':
    main()
