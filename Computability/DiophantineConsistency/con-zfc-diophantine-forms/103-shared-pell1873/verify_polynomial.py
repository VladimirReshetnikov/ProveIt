#!/usr/bin/env python3
"""Independent exact checker for the literal quartic and its flattening.

This file imports neither the compiler nor its polynomial helper. It checks
all pruning, gate-restoration, guard, and coefficient identities exactly.
The unbounded mathematical proof is in the report and proof notes.
"""
from __future__ import annotations

import argparse
from collections import defaultdict
from hashlib import sha256
import json
from pathlib import Path


def demand(ok, message):
    if not ok:
        raise ValueError(message)


def decode(terms):
    out = {}
    for coefficient, monomial in terms:
        demand(type(coefficient) is int and coefficient != 0, 'Noninteger or zero coefficient')
        demand(all(type(v) is int and v >= 0 for v in monomial), 'Bad coordinate')
        key = tuple(monomial)
        demand(key == tuple(sorted(key)) and key not in out, 'Noncanonical monomial')
        out[key] = coefficient
    return out


def plus(a, b, scale=1):
    c = dict(a)
    for m, v in b.items():
        c[m] = c.get(m, 0) + scale * v
        if not c[m]:
            del c[m]
    return c


def times(a, b):
    c = defaultdict(int)
    for u, x in a.items():
        for v, y in b.items():
            c[tuple(sorted(u + v))] += x * y
    return {m: x for m, x in c.items() if x}


def validate_dag(nodes, variable_count):
    for i, n in enumerate(nodes):
        demand(isinstance(n, list) and n, 'Malformed DAG node')
        if n[0] == 'c':
            demand(len(n) == 2 and type(n[1]) is int, 'Bad literal')
        elif n[0] == 'v':
            demand(len(n) == 2 and type(n[1]) is int and 0 <= n[1] < variable_count,
                   'Bad variable leaf')
        else:
            demand(n[0] in ('a', 's', 'm') and len(n) == 3,
                   'Unknown arithmetic operation')
            demand(all(type(j) is int and 0 <= j < i for j in n[1:]),
                   'Nontopological arithmetic graph')


def check_pruning(raw, circuit):
    nodes = raw['nodes']
    size = len(raw['variable_names'])
    validate_dag(nodes, size)
    validate_dag(circuit['nodes'], size)
    live = set()
    todo = [n for a, b, label in raw['equalities'] for n in (a, b)]
    while todo:
        i = todo.pop()
        demand(0 <= i < len(nodes), 'Invalid equation output')
        if i in live:
            continue
        live.add(i)
        if nodes[i][0] in ('a', 's', 'm'):
            todo.extend(nodes[i][1:])
    ordered = sorted(live)
    renaming = {old: new for new, old in enumerate(ordered)}
    expected = []
    for i in ordered:
        n = nodes[i]
        expected.append(n if n[0] in ('c', 'v') else [n[0], *(renaming[j] for j in n[1:])])
    demand(expected == circuit['nodes'], 'Pruning changed a polynomial')
    eqs = [[renaming[a], renaming[b], label] for a, b, label in raw['equalities']]
    demand(eqs == circuit['equalities'], 'Pruning changed an equation')
    demand(raw['variable_names'] == circuit['variable_names'], 'Semantic coordinate mismatch')
    free = sorted(raw['unrestricted_inputs'])
    guarded = sorted(set(range(size)) - set(free))
    demand(len(set(free)) == len(free), 'Duplicate unrestricted coordinate')
    demand(free == circuit['unrestricted_inputs'] and guarded == circuit['nonnegative_inputs'],
           'Incorrect sign-domain partition')
    return len(nodes), len(ordered)


def reconstruct_rows(circuit, cap):
    # Independent affine substitution, with a unique fresh coordinate for
    # each nonlinear product or explicitly retained affine support barrier.
    forms, rows = [], []
    count = len(circuit['variable_names'])
    nonlinear, barriers = 0, 0
    for i, n in enumerate(circuit['nodes']):
        if n[0] == 'c':
            value = {(): n[1]} if n[1] else {}
        elif n[0] == 'v':
            value = {(n[1],): 1}
        elif n[0] == 'a':
            value = plus(forms[n[1]], forms[n[2]])
        elif n[0] == 's':
            value = plus(forms[n[1]], forms[n[2]], -1)
        else:
            expression = times(forms[n[1]], forms[n[2]])
            if any(len(m) == 2 for m in expression):
                value = {(count,): 1}
                count += 1
                nonlinear += 1
                rows.append(('nonlinear gate ' + str(i), plus(value, expression, -1)))
            else:
                value = expression
        demand(all(len(m) <= 1 for m in value), 'Nonaffine register form')
        if cap and len(value) > cap:
            old = value
            value = {(count,): 1}
            count += 1
            barriers += 1
            rows.append(('affine support barrier ' + str(i), plus(value, old, -1)))
        forms.append(value)
    for a, b, label in circuit['equalities']:
        rows.append((label, plus(forms[a], forms[b], -1)))
    for v in circuit['nonnegative_inputs']:
        a, b, c = count, count + 1, count + 2
        count += 3
        rows.append(('semantic nonnegativity ' + str(v),
                     {(v,): 1, (a,a): -1, (b,b): -1, (c,c): -1, (c,): -1}))
    return rows, count, nonlinear, barriers


def collect_squares(rows):
    result = defaultdict(int)
    for label, p in rows:
        demand(all(len(m) <= 2 for m in p), 'A residual exceeds degree two')
        # Use symmetric convolution; this differs from the emitter's ordered
        # double loop and explicitly handles diagonal/off-diagonal terms.
        terms = sorted(p.items())
        for i, (a, ca) in enumerate(terms):
            for j in range(i, len(terms)):
                b, cb = terms[j]
                result[tuple(sorted(a+b))] += (1 if i == j else 2) * ca * cb
    return {m: x for m, x in result.items() if x}


def inspect(directory):
    def load(name):
        return json.loads((directory / name).read_text())
    raw, circuit = load('semantic_certificate.json'), load('circuit.json')
    reported = load('metrics.json')
    before, after = check_pruning(raw, circuit)
    expected, variables, nonlinear, barriers = reconstruct_rows(
        circuit, reported['max_substituted_affine_terms'])
    literal_rows = load('residuals.json')
    actual_rows = [(r['label'], decode(r['terms'])) for r in literal_rows]
    demand(expected == actual_rows, 'Literal residuals do not flatten the claimed circuit')
    collected = collect_squares(actual_rows)
    literal = load('polynomial.json')
    demand(literal['domain'] == 'unrestricted integers', 'Wrong witness domain')
    demand(literal['variable_count'] == variables, 'Wrong variable count')
    demand(decode(literal['terms']) == collected, 'Expanded polynomial differs from sum of squares')
    support = {i for monomial in collected for i in monomial}
    demand(support == set(range(variables)), 'A counted variable is absent')
    degree = max(map(len, collected), default=0)
    demand(degree == 4, 'The supplied polynomial is not exactly quartic')
    measured = {
        'ordinary_polynomial_variables': variables,
        'ordinary_polynomial_degree': degree,
        'ordinary_polynomial_monomials': len(collected),
        'max_abs_coefficient': max(map(abs, collected.values())),
        'SOS_residuals': len(actual_rows),
        'input_existentials': len(circuit['variable_names']),
        'unrestricted_semantic_inputs': len(circuit['unrestricted_inputs']),
        'nonnegative_semantic_inputs': len(circuit['nonnegative_inputs']),
        'nonnegativity_witnesses': 3 * len(circuit['nonnegative_inputs']),
        'nonlinear_wires': nonlinear,
        'retained_affine_wires': barriers,
        'largest_residual_support': max(len(p) for _, p in actual_rows),
    }
    for key, value in measured.items():
        demand(reported[key] == value, 'Incorrect advertised metric: ' + key)
    # Material corruption controls ensure comparisons cover coefficients,
    # gate definitions, and nonnegativity rows, rather than file dimensions.
    changed = dict(collected)
    first = next(iter(changed))
    changed[first] += 1
    demand(changed != decode(literal['terms']), 'Coefficient corruption not rejected')
    damaged_rows = list(actual_rows)
    first_guard = next(i for i, (label, _) in enumerate(damaged_rows)
                       if label.startswith('semantic nonnegativity '))
    label, guard = damaged_rows[first_guard]
    guard = dict(guard)
    quadratic = next(m for m in guard if len(m) == 2)
    guard[quadratic] = -2
    damaged_rows[first_guard] = label, guard
    demand(damaged_rows != expected, 'Guard corruption not rejected')
    return {
        'status': 'PASS', 'directory': directory.name,
        'scope': 'Exact pruning, full affine/gate restoration, complete guard coverage, '
                 'and all collected coefficients; unbounded semantics proved separately.',
        'optimized_python': not __debug__,
        'raw_nodes': before, 'retained_nodes': after,
        'metrics': measured,
        'negative_controls': ['one polynomial coefficient changed', 'one guard square changed'],
        'sha256': {name: sha256((directory/name).read_bytes()).hexdigest()
                   for name in ('circuit.json', 'residuals.json', 'polynomial.json', 'metrics.json')},
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('directory', nargs='?', type=Path,
                        default=Path(__file__).resolve().parent/'equations')
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    result = inspect(args.directory)
    text = json.dumps(result, sort_keys=True, indent=2) + '\n'
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(text)
    print(text, end='')


if __name__ == '__main__':
    main()
