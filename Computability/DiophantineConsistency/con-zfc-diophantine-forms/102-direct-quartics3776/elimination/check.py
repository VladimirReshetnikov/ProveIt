#!/usr/bin/env python3
"""Independently replay exact polynomial elimination certificates.

Usage: python3 check.py PARENT_EQUATION.json OUTPUT_DIRECTORY [--receipt PATH]

This checker does not import or execute the optimizer.  It accepts only monic
definitions, replays every substitution with sparse integer arithmetic, checks
the degree-preserving criterion, and independently expands the entire final
sum of squares.  No numerical sampling is used.
"""
from __future__ import annotations

import argparse
from collections import Counter, defaultdict
from hashlib import sha256
import json
from pathlib import Path
import sys


def demand(condition, message):
    if not condition:
        raise ValueError(message)


def integer(x):
    return type(x) is int


def read_polynomial(raw, variable_count, maximum_degree, context):
    """Validate canonical data and return monomial -> integer coefficient."""
    demand(type(raw) is list, context + ': term list required')
    result = {}
    order = []
    for term in raw:
        demand(type(term) is list and len(term) == 2, context + ': malformed term')
        coefficient, monomial = term
        demand(integer(coefficient) and coefficient != 0, context + ': nonzero integer coefficient required')
        demand(type(monomial) is list, context + ': monomial list required')
        demand(all(integer(v) and 0 <= v < variable_count for v in monomial),
               context + ': invalid coordinate')
        demand(monomial == sorted(monomial), context + ': unsorted monomial')
        demand(len(monomial) <= maximum_degree, context + ': degree exceeded')
        key = tuple(monomial)
        demand(key not in result, context + ': repeated monomial')
        result[key] = coefficient
        order.append(key)
    demand(order == sorted(order), context + ': term order is not canonical')
    return result


def encoded(poly):
    return [[value, list(key)] for key, value in sorted(poly.items()) if value]


def multiply(left, right):
    accum = defaultdict(int)
    for monomial_l, coefficient_l in left.items():
        for monomial_r, coefficient_r in right.items():
            accum[tuple(sorted(monomial_l + monomial_r))] += coefficient_l * coefficient_r
    return {m: c for m, c in accum.items() if c}


def replacement(poly, target, expression):
    """Compute substitution by expanding each monomial factor independently."""
    result = defaultdict(int)
    for monomial, coefficient in poly.items():
        expansion = {(): coefficient}
        for variable in monomial:
            factor = expression if variable == target else {(variable,): 1}
            expansion = multiply(expansion, factor)
        for key, value in expansion.items():
            result[key] += value
    return {m: c for m, c in result.items() if c}


def support(poly):
    return {v for monomial in poly for v in monomial}


def audit(source_path, output_path):
    source_bytes = source_path.read_bytes()
    parent_hash = sha256(source_bytes).hexdigest()
    source = json.loads(source_bytes)
    demand(source.get('schema') == 'finite_quadratic_residuals_v1', 'unsupported parent schema')
    demand(source.get('domain') == 'unrestricted integers', 'parent domain must be Z')
    demand(source.get('polynomial') == 'sum(square(row) for row in residuals)', 'unexpected parent polynomial')
    variables = source['variables']
    demand(type(variables) is list, 'parent variables must be a list')
    variable_count = len(variables)
    demand(variable_count > 0, 'empty parent coordinate list')
    demand(all(type(v) is dict and type(v.get('name')) is str for v in variables),
           'malformed variable metadata')
    demand(len({v['name'] for v in variables}) == variable_count, 'duplicate parent variable names')
    residual_data = source['residuals']
    demand(type(residual_data) is list, 'parent residual list required')
    row_polys, row_metadata = {}, {}
    incidence = defaultdict(set)
    for index, row in enumerate(residual_data):
        demand(type(row) is dict and type(row.get('label')) is str, 'malformed parent row')
        row_polys[index] = read_polynomial(row['terms'], variable_count, 2, f'parent row {index}')
        row_metadata[index] = {k: v for k, v in row.items() if k != 'terms'}
        for variable in support(row_polys[index]):
            incidence[variable].add(index)

    paths = {name: output_path/name for name in
             ('equation.json', 'expanded_polynomial.json', 'elimination_certificate.json')}
    raw_output = {name: path.read_bytes() for name, path in paths.items()}
    values = {name: json.loads(raw) for name, raw in raw_output.items()}
    certificate = values['elimination_certificate.json']
    equation = values['equation.json']
    expanded_file = values['expanded_polynomial.json']
    demand(certificate.get('method') == 'successive_monic_polynomial_projection',
           'wrong certificate method')
    demand(certificate.get('parent_sha256') == parent_hash, 'certificate parent hash mismatch')
    demand(equation.get('parent_sha256') == parent_hash, 'equation parent hash mismatch')
    for name in ('affine_support_cap', 'quadratic_support_cap'):
        demand(integer(certificate.get(name)) and certificate[name] >= 0, 'invalid support cap')

    alive = set(range(variable_count))
    zero_deletions = []
    kind_counts = Counter()
    total_rewritten_rows = 0
    steps = certificate.get('steps')
    demand(type(steps) is list, 'certificate steps must be a list')
    for number, step in enumerate(steps, 1):
        context = f'elimination {number}'
        demand(type(step) is dict, context + ': invalid record')
        target = step.get('variable')
        defining = step.get('definition_row')
        demand(integer(target) and target in alive, context + ': coordinate already absent or invalid')
        demand(integer(defining) and defining in row_polys, context + ': defining row absent or invalid')
        exact_definition = dict(row_metadata[defining], terms=encoded(row_polys[defining]))
        demand(step.get('definition') == exact_definition, context + ': wrong defining polynomial')
        original = row_polys[defining]
        coefficient = original.get((target,))
        demand(coefficient in (-1, 1), context + ': defining coefficient is not a unit')
        demand(all(target not in monomial or monomial == (target,) for monomial in original),
               context + ': target occurs elsewhere in its definition')
        expression = {m: -coefficient*c for m, c in original.items() if m != (target,)}
        given = read_polynomial(step.get('expression'), variable_count, 2, context + ' expression')
        demand(given == expression, context + ': incorrect solved expression')
        demand(support(expression) <= alive - {target}, context + ': expression uses absent coordinate')
        expression_degree = max(map(len, expression), default=0)
        kind = step.get('kind')
        if kind == 'affine':
            demand(expression_degree <= 1, context + ': claimed affine expression is nonlinear')
            demand(len(expression) <= certificate['affine_support_cap'], context + ': affine support cap')
        elif kind == 'linear_occurrence_quadratic':
            demand(expression_degree == 2, context + ': wrong quadratic expression degree')
            demand(len(expression) <= certificate['quadratic_support_cap'], context + ': quadratic support cap')
            for row_index in incidence[target]:
                demand(all(target not in m or m == (target,) for m in row_polys[row_index]),
                       context + ': quadratic replacement has a nonlinear occurrence')
        else:
            raise ValueError(context + ': unknown elimination kind')
        affected = sorted(incidence[target] - {defining})
        demand(step.get('affected_rows') == affected, context + ': incomplete or wrong affected-row list')

        # Remove the defining row, then replace target in every other occurrence.
        for coordinate in support(original):
            incidence[coordinate].remove(defining)
        del row_polys[defining]
        del row_metadata[defining]
        for row_index in affected:
            before = row_polys[row_index]
            after = replacement(before, target, expression)
            demand(all(len(m) <= 2 for m in after), context + ': resulting degree exceeds two')
            for coordinate in support(before):
                incidence[coordinate].remove(row_index)
            if after:
                row_polys[row_index] = after
                for coordinate in support(after):
                    incidence[coordinate].add(row_index)
            else:
                zero_deletions.append(row_index)
                del row_polys[row_index]
                del row_metadata[row_index]
            total_rewritten_rows += 1
        demand(not incidence[target], context + ': target remains after substitution')
        alive.remove(target)
        kind_counts[kind] += 1

    retained_variables = sorted(alive)
    retained_rows = sorted(row_polys)
    demand(certificate.get('retained_variables') == retained_variables, 'retained coordinate list mismatch')
    demand(certificate.get('retained_rows') == retained_rows, 'retained row list mismatch')
    demand(certificate.get('removed_zero_rows') == zero_deletions, 'zero-row deletion list mismatch')
    demand(len(retained_rows) + len(steps) + len(zero_deletions) == len(residual_data), 'row count identity')
    renumbering = {old: new for new, old in enumerate(retained_variables)}
    final_rows = []
    for index in retained_rows:
        demand(support(row_polys[index]) <= alive, 'deleted coordinate in final row')
        renumbered = {tuple(renumbering[v] for v in monomial): coefficient
                      for monomial, coefficient in row_polys[index].items()}
        final_rows.append({'label': row_metadata[index]['label'], 'terms': encoded(renumbered)})
    final_variables = [variables[index] for index in retained_variables]
    demand(equation.get('variables') == final_variables, 'final coordinate metadata/renumbering mismatch')
    demand(equation.get('residuals') == final_rows, 'final residual system mismatch')
    demand(equation.get('schema') == 'finite_quadratic_residuals_v1', 'wrong output schema')
    demand(equation.get('domain') == 'unrestricted integers', 'wrong output domain')
    demand(equation.get('polynomial') == 'sum(square(row) for row in residuals)', 'wrong output polynomial')

    final_count = len(final_variables)
    expansion = defaultdict(int)
    final_polys = []
    for index, row in enumerate(final_rows):
        poly = read_polynomial(row['terms'], final_count, 2, f'final row {index}')
        final_polys.append(poly)
        for monomial, coefficient in multiply(poly, poly).items():
            expansion[monomial] += coefficient
    expansion = {m: c for m, c in expansion.items() if c}
    demand(expansion, 'zero final polynomial')
    demand(support(expansion) == set(range(final_count)), 'unused final coordinate')
    demand(expanded_file.get('domain') == 'unrestricted integers', 'expanded domain mismatch')
    demand(expanded_file.get('variables') == final_count, 'expanded dimension mismatch')
    delivered_poly = read_polynomial(expanded_file.get('terms'), final_count, 4, 'expanded polynomial')
    demand(delivered_poly == expansion, 'full sum-of-squares expansion mismatch')
    metrics = {
        'variables': final_count,
        'quadratic_rows': len(final_rows),
        'exact_degree': max(map(len, expansion)),
        'expanded_monomials': len(expansion),
        'coefficient_height': max(map(abs, expansion.values())),
        'max_abs_row_coefficient': max(abs(c) for p in final_polys for c in p.values()),
        'eliminated_variables': len(steps),
        'elimination_kinds': dict(kind_counts),
        'zero_rows_removed': len(zero_deletions),
        'max_row_terms': max(map(len, final_polys)),
    }
    demand(equation.get('metrics') == metrics, 'reported equation metrics mismatch')
    hashes = {name: sha256(raw).hexdigest() for name, raw in raw_output.items()}
    build_path = output_path/'BUILD.json'
    if build_path.is_file():
        build_receipt = json.loads(build_path.read_bytes())
        demand(build_receipt.get('status') == 'PASS', 'builder status mismatch')
        demand(build_receipt.get('parent_sha256') == parent_hash, 'builder parent hash mismatch')
        demand(build_receipt.get('metrics') == metrics, 'builder metrics mismatch')
        demand(build_receipt.get('sha256') == hashes, 'builder artifact hashes mismatch')

    return {
        'status': 'PASS',
        'checker': 'independent_exact_projection_replay_v1',
        'parent_sha256': parent_hash,
        'metrics': metrics,
        'sha256': hashes,
        'rewritten_row_instances': total_rewritten_rows,
        'optimization_flag': sys.flags.optimize,
        'scope': 'Every monic definition, complete sparse substitution, domain Z, quadratic-degree criterion, final renumbering, full collected quartic, and all displayed metrics; no sampling or optimizer import.',
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('source', type=Path)
    parser.add_argument('output', type=Path)
    parser.add_argument('--receipt', type=Path)
    args = parser.parse_args()
    result = audit(args.source, args.output)
    text = json.dumps(result, indent=2, sort_keys=True) + '\n'
    if args.receipt:
        args.receipt.parent.mkdir(parents=True, exist_ok=True)
        args.receipt.write_text(text)
    print(text, end='')


if __name__ == '__main__':
    main()
