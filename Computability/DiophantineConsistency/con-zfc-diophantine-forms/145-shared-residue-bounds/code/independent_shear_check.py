#!/usr/bin/env python3
"""Independent exact verification of quadratic rows under integer shears.

Only Python's standard library is used; no producer or search code is imported.
Each stage contains equation.json, expanded_polynomial.json, and shears.json.
"""
import argparse
import copy
import hashlib
import itertools
import json
import math
from pathlib import Path
import sys


class CheckError(Exception):
    pass


def require(condition, message):
    if not condition:
        raise CheckError(message)


def integer(value):
    return isinstance(value, int) and not isinstance(value, bool)


def read(path):
    return json.loads(path.read_text())


def polynomial(terms, n, max_degree, label):
    answer = {}
    require(isinstance(terms, list), label + ': term list')
    for term in terms:
        require(isinstance(term, list) and len(term) == 2, label + ': term pair')
        coefficient, monomial = term
        require(integer(coefficient) and coefficient != 0, label + ': coefficient')
        require(isinstance(monomial, list), label + ': monomial list')
        require(all(integer(v) and 0 <= v < n for v in monomial), label + ': variable')
        require(monomial == sorted(monomial), label + ': canonical monomial')
        require(len(monomial) <= max_degree, label + ': degree')
        key = tuple(monomial)
        require(key not in answer, label + ': duplicate monomial')
        answer[key] = coefficient
    return answer


def equation(data):
    require(data['domain'] == 'unrestricted integers', 'integer domain')
    require(data['polynomial'] == 'sum(square(row) for row in residuals)', 'SOS definition')
    require(data['schema'] == 'finite_quadratic_residuals_v1', 'quadratic schema')
    n = len(data['variables'])
    require(n > 0, 'nonempty coordinate list')
    return [polynomial(r['terms'], n, 2, 'row ' + str(i))
            for i, r in enumerate(data['residuals'])]


def add_to(target, key, value):
    target[key] = target.get(key, 0) + value
    if target[key] == 0:
        del target[key]


def shear(poly, i, j, k):
    """Substitute x_j := x_j + k*x_i in a sparse polynomial."""
    result = {}
    for monomial, coefficient in poly.items():
        exponent = monomial.count(j)
        rest = tuple(v for v in monomial if v != j)
        for taken in range(exponent + 1):
            key = tuple(sorted(rest + (i,) * taken + (j,) * (exponent - taken)))
            value = coefficient * math.comb(exponent, taken) * (k ** taken)
            add_to(result, key, value)
    return result


def expand_sos(rows):
    result = {}
    for row in rows:
        for left, a in row.items():
            for right, b in row.items():
                add_to(result, tuple(sorted(left + right)), a * b)
    return result


def metrics(poly):
    return [max(map(abs, poly.values()), default=0), len(poly),
            sum(map(abs, poly.values()))]


def step_data(step, n):
    i, j, k = step['i'], step['j'], step['k']
    require(integer(i) and integer(j) and 0 <= i < n and 0 <= j < n and i != j,
            'distinct valid shear coordinates')
    require(integer(k) and k != 0, 'nonzero integral shear multiplier')
    require(step['meaning'] == 'old x_j = new x_j + k new x_i', 'shear convention')
    return i, j, k


def matrix_shear(rows, i, j, k):
    # Matrices are stored as sparse row dictionaries. This is right
    # multiplication by the elementary substitution matrix.
    for row in rows:
        if j in row:
            add_to(row, i, k * row[j])


def matrix_product(left, right):
    result = []
    for row in left:
        output = {}
        for middle, a in row.items():
            for column, b in right[middle].items():
                add_to(output, column, a * b)
        result.append(output)
    return result


def verify(start, stages):
    initial = equation(start)
    current = initial
    n = len(start['variables'])
    all_steps = []
    stage_receipts = []
    previous_data = start
    for number, stage in enumerate(stages, 1):
        history = stage['history']
        require(metrics(expand_sos(current)) == history['initial_metrics'],
                'stage initial metrics ' + str(number))
        require(stage['equation']['variables'] == start['variables'], 'unchanged variables')
        require([r['label'] for r in stage['equation']['residuals']] ==
                [r['label'] for r in start['residuals']], 'unchanged row labels')
        require({k: v for k, v in stage['equation'].items() if k != 'residuals'} ==
                {k: v for k, v in previous_data.items() if k != 'residuals'},
                'unchanged equation metadata')
        for position, step in enumerate(history['history'], 1):
            i, j, k = step_data(step, n)
            current = [shear(row, i, j, k) for row in current]
            require(all(len(m) <= 2 for row in current for m in row), 'quadratic preservation')
            require(metrics(expand_sos(current)) == step['metrics'],
                    'step metrics stage ' + str(number) + ' step ' + str(position))
            all_steps.append((i, j, k))
        expected = equation(stage['equation'])
        require(current == expected, 'complete forward row identity stage ' + str(number))
        collected = expand_sos(current)
        final = stage['expanded']
        if set(final) != {'terms'}:
            require(final['schema'] == 'sparse_integer_polynomial_v1', 'expanded schema')
            require(final['domain'] == 'unrestricted integers' and final['variables'] == n,
                    'expanded variable domain')
        require(collected == polynomial(final['terms'], n, 4, 'expanded polynomial'),
                'full SOS expansion stage ' + str(number))
        require(metrics(collected) == history['final_metrics'], 'stage final metrics')
        stage_receipts.append({'stage': number, 'shears': len(history['history']),
                               'metrics': metrics(collected)})
        previous_data = stage['equation']

    reverse = current
    for i, j, k in reversed(all_steps):
        reverse = [shear(row, i, j, -k) for row in reverse]
    require(reverse == initial, 'full inverse row identity')

    identity = [{i: 1} for i in range(n)]
    forward_matrix = copy.deepcopy(identity)
    inverse_matrix = copy.deepcopy(identity)
    for i, j, k in all_steps:
        matrix_shear(forward_matrix, i, j, k)
    for i, j, k in reversed(all_steps):
        matrix_shear(inverse_matrix, i, j, -k)
    require(matrix_product(forward_matrix, inverse_matrix) == identity,
            'coordinate matrices inverse in first order')
    require(matrix_product(inverse_matrix, forward_matrix) == identity,
            'coordinate matrices inverse in second order')

    final_poly = expand_sos(current)
    live = set(itertools.chain.from_iterable(final_poly))
    require(live == set(range(n)), 'all coordinates live in collected polynomial')
    degree = max(map(len, final_poly), default=0)
    require(degree == 4, 'exact quartic degree')
    return {'passed': True, 'variables': n, 'rows': len(current), 'degree': degree,
            'monomials': len(final_poly), 'height': max(map(abs, final_poly.values())),
            'l1_coefficient_sum': sum(map(abs, final_poly.values())),
            'shears': len(all_steps), 'stage_checks': stage_receipts,
            'coordinate_inverse_both_orders': True, 'inverse_row_identity': True,
            'all_variables_live': True}


def mutation_checks(start, stages):
    outcomes = []

    def reject(label, changed):
        try:
            verify(start, changed)
        except CheckError as error:
            outcomes.append({'mutation': label, 'rejected': True, 'reason': str(error)})
        else:
            raise CheckError('undetected mutation: ' + label)

    bad = copy.deepcopy(stages)
    term = bad[-1]['equation']['residuals'][0]['terms'][0]
    term[0] = -term[0]
    reject('final quadratic-row coefficient sign', bad)

    bad = copy.deepcopy(stages)
    first = bad[0]['history']['history'][0]
    first['k'] += 1 if first['k'] > 0 else -1
    reject('shear multiplier', bad)

    bad = copy.deepcopy(stages)
    terms = bad[-1]['expanded']['terms']
    support = {tuple(m) for c, m in terms}
    n = len(start['variables'])
    replacement = next((i, i, i, i) for i in range(n) if (i, i, i, i) not in support)
    terms[0][1] = list(replacement)
    reject('collected-polynomial monomial', bad)
    return outcomes


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--start', type=Path, required=True)
    parser.add_argument('--stage', type=Path, action='append', required=True)
    parser.add_argument('--receipt', type=Path)
    parser.add_argument('--skip-mutations', action='store_true')
    args = parser.parse_args()
    stages = [{'history': read(p / 'shears.json'), 'equation': read(p / 'equation.json'),
               'expanded': read(p / 'expanded_polynomial.json')} for p in args.stage]
    start = read(args.start)
    result = verify(start, stages)
    if not args.skip_mutations:
        result['mutations'] = mutation_checks(start, stages)
    files = [args.start] + [p / f for p in args.stage for f in
                            ['shears.json', 'equation.json', 'expanded_polynomial.json']]
    result['file_sha256'] = {str(p): hashlib.sha256(p.read_bytes()).hexdigest() for p in files}
    result['python_optimization'] = sys.flags.optimize
    result['scope'] = ('Exact finite polynomial identities and integral coordinate inverses; '
                       'does not reprove inherited arithmetic or logical calibration.')
    encoded = json.dumps(result, sort_keys=True, indent=2) + '\n'
    if args.receipt:
        args.receipt.parent.mkdir(parents=True, exist_ok=True)
        args.receipt.write_text(encoded)
    print(encoded, end='')


if __name__ == '__main__':
    main()
