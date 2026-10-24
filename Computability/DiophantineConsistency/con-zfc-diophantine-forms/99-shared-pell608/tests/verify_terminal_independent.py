#!/usr/bin/env python3
"""Independent exact check of monic terminal-wire elimination and SOS export.

No imports from the constructor or compressor. Uses explicit exceptions rather
than assert, so the same proof obligations are checked with python -O.
"""
from __future__ import annotations

import argparse
from collections import defaultdict
from copy import deepcopy
from hashlib import sha256
import json
from pathlib import Path


def require(condition, message):
    if not condition:
        raise ValueError(message)


def read_polynomial(terms, *, variable_count, max_degree, context):
    result = {}
    for term in terms:
        require(isinstance(term, list) and len(term) == 2, context + ': malformed term')
        coefficient, indices = term
        require(type(coefficient) is int and coefficient != 0,
                context + ': coefficient must be a nonzero integer')
        require(isinstance(indices, list), context + ': malformed monomial')
        require(all(type(v) is int and 0 <= v < variable_count for v in indices),
                context + ': variable outside universe')
        monomial = tuple(indices)
        require(monomial == tuple(sorted(monomial)), context + ': unsorted monomial')
        require(len(monomial) <= max_degree, context + ': excessive degree')
        require(monomial not in result, context + ': uncollected duplicate monomial')
        result[monomial] = coefficient
    return result


def add_scaled(destination, source, scalar):
    for monomial, coefficient in source.items():
        value = destination.get(monomial, 0) + scalar * coefficient
        if value:
            destination[monomial] = value
        else:
            destination.pop(monomial, None)


def check(before, trace, after, expanded):
    require(before['domain'] == 'nonnegative integers', 'unexpected parent domain')
    require(after['domain'] == before['domain'] == expanded['domain'], 'domain mismatch')
    original_count = len(before['variables'])
    rows = {
        i: read_polynomial(row['terms'], variable_count=original_count,
                           max_degree=2, context='parent row ' + str(i))
        for i, row in enumerate(before['residuals'])
    }
    variables = set(range(original_count))
    all_removed = []
    checked_consumers = 0
    unit_signs = defaultdict(int)
    for step_number, step in enumerate(trace['steps']):
        prefix = 'step ' + str(step_number)
        variable, row_id = step['variable'], step['definition_row']
        require(variable in variables, prefix + ': variable already absent')
        require(row_id in rows, prefix + ': defining row already absent')
        defining = rows[row_id]
        sign = defining.get((variable,), 0)
        require(sign in (-1, 1), prefix + ': defining coefficient is not a unit')
        require(all(variable not in monomial or monomial == (variable,)
                    for monomial in defining), prefix + ': self-dependent definition')
        recipe = {
            monomial: -sign * coefficient for monomial, coefficient in defining.items()
            if monomial != (variable,)
        }
        require(all(coefficient > 0 for coefficient in recipe.values()),
                prefix + ': recipe is not coefficientwise nonnegative')
        require(all(set(monomial) <= variables - {variable} for monomial in recipe),
                prefix + ': recipe uses an absent variable')
        saved = read_polynomial(step['restoration'], variable_count=original_count,
                                max_degree=2, context=prefix + ' saved recipe')
        require(saved == recipe, prefix + ': saved recipe differs from defining row')
        consumers = []
        for other_id, row in rows.items():
            if other_id == row_id:
                continue
            require(all(variable not in monomial or monomial == (variable,)
                        for monomial in row), prefix + ': nonlinear consumer')
            if (variable,) in row:
                consumers.append(other_id)
        require(sorted(consumers) == sorted(step['consumer_rows']),
                prefix + ': consumer row list is incorrect')
        require(len(set(step['consumer_rows'])) == len(step['consumer_rows']),
                prefix + ': duplicate consumer row')
        for other_id in consumers:
            row = rows[other_id]
            coefficient = row.pop((variable,))
            add_scaled(row, recipe, coefficient)
            require(all(len(monomial) <= 2 for monomial in row),
                    prefix + ': substitution raised degree')
        del rows[row_id]
        variables.remove(variable)
        all_removed.append(variable)
        unit_signs[str(sign)] += 1
        checked_consumers += len(consumers)

    dropped = trace.get('dropped_unused_indices', [])
    require(len(set(dropped)) == len(dropped), 'duplicate unused variable')
    used = {v for row in rows.values() for monomial in row for v in monomial}
    require(set(dropped) <= variables - used, 'pruned variable was not unused')
    variables.difference_update(dropped)
    retained = trace['retained_indices']
    require(retained == sorted(variables), 'incorrect retained variable set or order')
    retained_rows = trace['retained_row_indices']
    require(retained_rows == sorted(rows), 'incorrect retained row set or order')
    require(after['variables'] == [before['variables'][v] for v in retained],
            'variable metadata changed')
    require(len(after['residuals']) == len(retained_rows), 'wrong final row count')
    renaming = {old: new for new, old in enumerate(retained)}
    normalized_final = []
    for new_id, old_id in enumerate(retained_rows):
        expected = {
            tuple(renaming[v] for v in monomial): coefficient
            for monomial, coefficient in rows[old_id].items()
        }
        actual = read_polynomial(after['residuals'][new_id]['terms'],
                                 variable_count=len(retained), max_degree=2,
                                 context='final row ' + str(new_id))
        require(expected == actual, 'final row ' + str(new_id) + ' differs exactly')
        require(after['residuals'][new_id].get('label') ==
                before['residuals'][old_id].get('label'), 'row label changed')
        normalized_final.append(actual)

    # Ordered convolution, deliberately separate from the builder's likely
    # triangular/symmetric multiplication. Cancellation is collected exactly.
    sos = {}
    product_pairs = 0
    for row in normalized_final:
        square = defaultdict(int)
        for left, a in row.items():
            for right, b in row.items():
                square[tuple(sorted(left + right))] += a * b
                product_pairs += 1
        add_scaled(sos, square, 1)
    saved_sos = read_polynomial(expanded['terms'], variable_count=len(retained),
                                max_degree=4, context='expanded sum of squares')
    require(saved_sos == sos, 'expanded polynomial differs from exact SOS')
    require(expanded['variables'] == len(retained), 'expanded variable count differs')
    degree = max((len(m) for m in sos), default=-1)
    require(degree == 4, 'final polynomial is not exactly quartic')
    require(any(len(m) == 2 for row in normalized_final for m in row),
            'no quadratic residual survives')
    return {
        'status': 'PASS',
        'method': 'independent exact sparse substitution and ordered convolution',
        'initial_variables': original_count,
        'final_variables': len(retained),
        'initial_rows': len(before['residuals']),
        'final_rows': len(normalized_final),
        'elimination_steps': len(all_removed),
        'defining_unit_signs': dict(unit_signs),
        'checked_consumer_rows': checked_consumers,
        'unused_variables_removed': len(dropped),
        'exact_degree': degree,
        'expanded_monomials': len(sos),
        'maximum_absolute_coefficient': max(abs(c) for c in sos.values()),
        'ordered_convolution_pairs': product_pairs,
        'scope': 'Finite reduction/export only; parent consistency semantics require ordinary proof.'
    }


def expect_rejection(name, before, trace, after, expanded):
    try:
        check(before, trace, after, expanded)
    except (ValueError, KeyError, TypeError, IndexError) as error:
        return {'control': name, 'status': 'REJECTED', 'reason': str(error)}
    raise ValueError('corruption control was accepted: ' + name)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('directory', type=Path)
    parser.add_argument('--output', type=Path)
    arguments = parser.parse_args()
    names = ['before_terminal.json', 'elimination_trace.json', 'equation.json',
             'expanded_polynomial.json']
    raw = [(arguments.directory / name).read_bytes() for name in names]
    before, trace, after, expanded = [json.loads(data) for data in raw]
    receipt = check(before, trace, after, expanded)
    receipt['input_sha256'] = {name: sha256(data).hexdigest() for name, data in zip(names, raw)}
    controls = []
    altered_trace = deepcopy(trace)
    altered_trace['steps'][0]['restoration'][0][0] += 1
    controls.append(expect_rejection('changed restoration coefficient', before,
                                    altered_trace, after, expanded))
    altered_expanded = deepcopy(expanded)
    altered_expanded['terms'][0][0] += 1
    controls.append(expect_rejection('changed polynomial coefficient', before,
                                    trace, after, altered_expanded))
    altered_before = deepcopy(before)
    first = trace['steps'][0]
    if first['consumer_rows']:
        affected = altered_before['residuals'][first['consumer_rows'][0]]['terms']
        affected.append([1, [first['variable'], first['variable']]])
        controls.append(expect_rejection('nonlinear use of eliminated wire', altered_before,
                                        trace, after, expanded))
    receipt['corruption_controls'] = controls
    receipt['verifier_sha256'] = sha256(Path(__file__).read_bytes()).hexdigest()
    output = json.dumps(receipt, indent=2, sort_keys=True) + '\n'
    if arguments.output:
        arguments.output.write_text(output)
    print(output, end='')


if __name__ == '__main__':
    main()
