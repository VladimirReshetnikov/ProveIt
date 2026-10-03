#!/usr/bin/env python3
"""Export an expanded, unique-witness quartic for one local G transition.

This is a local one-step certificate, not an unbounded reachability result.
Every product is evaluated by its own unshared multiplication chain.
"""
from collections import Counter
from pathlib import Path
import argparse
import json

COORDINATES = tuple((x, y) for y in range(-3, 3) for x in range(-6, 7))
INDEX = {p: i for i, p in enumerate(COORDINATES)}
OUTPUT = len(COORDINATES)
FIRST_AUXILIARY = OUTPUT + 1


def require(condition, detail):
    if not condition:
        raise RuntimeError(detail)


def indicators():
    # Independent copy of the geometric definition, not local-rule bitmasks.
    rules = (
        ('E', {(0, 0), (1, 0)}, {(1, 0), (2, 0)}),
        ('W', {(0, 0), (2, 0)}, {(-1, 0), (1, 0)}),
        ('R', {(0, 0), (1, 0), (3, 0)}, {(-1, 0), (1, 0), (4, 1)}),
        ('L', {(0, 0), (2, 0), (4, 0)}, {(0, 1), (3, 1), (4, 1)}),
    )
    answer = []
    for name, old, new in rules:
        for sign, targets in ((1, new-old), (-1, old-new)):
            for tx, ty in sorted(targets):
                ones = {(x-tx, y-ty) for x, y in old}
                halo = {(x+dx, y+dy) for x, y in ones
                        for dx in range(-2, 3) for dy in range(-2, 3)}
                require(halo <= INDEX.keys(), 'Indicator exceeds input rectangle')
                answer.append({
                    'name': name, 'sign': sign, 'anchor': [-tx, -ty],
                    'ones': sorted(INDEX[p] for p in ones),
                    'zeros': sorted(INDEX[p] for p in halo-ones),
                })
    return answer


def terms_json(poly):
    return [{'coefficient': c, 'variables': list(m)}
            for m, c in sorted(poly.items(), key=lambda p: (len(p[0]), p[0]))
            if c]


def build():
    indicators_data = indicators()
    gates, residuals = [], []
    next_variable = FIRST_AUXILIARY
    for item in indicators_data:
        factors = [(v, False) for v in item['ones']]
        factors += [(v, True) for v in item['zeros']]
        previous = factors[0][0]
        require(not factors[0][1], 'First factor must be occupied input')
        for variable, complement in factors[1:]:
            gate = {'target': next_variable, 'previous': previous,
                    'input': variable, 'complement': complement}
            gates.append(gate)
            monomial = tuple(sorted((previous, variable)))
            residual = {(next_variable,): 1}
            if complement:
                residual[(previous,)] = -1
                residual[monomial] = 1
            else:
                residual[monomial] = -1
            residuals.append(residual)
            previous = next_variable
            next_variable += 1
        item['result_variable'] = previous
    for variable in range(OUTPUT):
        residuals.append({(variable, variable): 1, (variable,): -1})
    output_residual = {(OUTPUT,): 1, (INDEX[(0, 0)],): -1}
    for item in indicators_data:
        output_residual[(item['result_variable'],)] = -item['sign']
    residuals.append(output_residual)
    expanded = Counter()
    for residual in residuals:
        for monomial_a, coefficient_a in residual.items():
            for monomial_b, coefficient_b in residual.items():
                expanded[tuple(sorted(monomial_a+monomial_b))] += coefficient_a*coefficient_b
    expanded = {m: c for m, c in expanded.items() if c}
    counts = {
        'input_bits': OUTPUT, 'external_variables': FIRST_AUXILIARY,
        'auxiliary_variables': len(gates), 'residuals': len(residuals),
        'plain_product_gates': sum(not g['complement'] for g in gates),
        'complement_product_gates': sum(g['complement'] for g in gates),
        'residual_monomial_occurrences': sum(len(r) for r in residuals),
        'ordered_sos_expansion_occurrences': sum(len(r)**2 for r in residuals),
        'collected_expanded_terms': len(expanded),
        'degree': max(map(len, expanded)),
        'maximum_coefficient_magnitude': max(abs(c) for c in expanded.values()),
    }
    expected = {'input_bits': 78, 'external_variables': 79,
                'auxiliary_variables': 614, 'residuals': 693,
                'plain_product_gates': 26, 'complement_product_gates': 588,
                'residual_monomial_occurrences': 1990,
                'ordered_sos_expansion_occurrences': 6032, 'degree': 4}
    require(all(counts[k] == v for k, v in expected.items()), ('counts', counts))
    # Six distinct degree-45 monomials certify exact Boolean degree and support.
    tops = []
    for item in indicators_data:
        if item['name'] == 'L':
            support = tuple(sorted(item['ones']+item['zeros']))
            tops.append((support, item['sign'] * (-1)**len(item['zeros'])))
    require(len(tops) == 6 and len({s for s, _ in tops}) == 6,
            'Top monomials are not distinct')
    require(all(len(s) == 45 and c in (-1, 1) for s, c in tops),
            'Top coefficient or degree mismatch')
    require(set().union(*(set(s) for s, _ in tops)) == set(range(78)),
            'Top supports do not cover every input cell')
    variables = [f'c_{x}_{y}' for x, y in COORDINATES] + ['y']
    variables += [f'z_{i}' for i in range(len(gates))]
    return {
        'scope': 'One local transition of G only; no unbounded reachability claim.',
        'definition': 'P=sum of squares of the exported residuals',
        'monomial_encoding': 'variables lists indices with repetition; multiply all listed variables',
        'variable_order': variables,
        'input_coordinates': [list(p) for p in COORDINATES],
        'external_variable_count': FIRST_AUXILIARY,
        'auxiliary_domain': 'nonnegative integers, including zero (also unique over unrestricted reals)',
        'counts': counts,
        'indicators': indicators_data,
        'gates': gates,
        'residuals': [terms_json(r) for r in residuals],
        'expanded_polynomial': terms_json(expanded),
        'degree_45_boolean_top_terms': [
            {'coefficient': c, 'variables': list(s)} for s, c in tops],
    }


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--output', type=Path, default=Path('local-quartic-certificate.json'))
    args = parser.parse_args()
    certificate = build()
    args.output.write_text(json.dumps(certificate, separators=(',', ':'), sort_keys=True)+'\n')
    print(json.dumps(certificate['counts'], indent=2, sort_keys=True))
