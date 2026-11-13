#!/usr/bin/env python3
"""Search sign-reversed intermediates used only as complete squares."""
import contextlib
from hashlib import sha256
import io
from itertools import product
import json
from pathlib import Path
import random
import runpy
import sys

HERE = Path(__file__).resolve().parent
BASE = HERE.parent / 'ordinary12-circuit-local-search/search.py'
BASE_PIN = '98f54938a6eb1a158ffca98581dd5836300e13a6d07f9340ca52ab8ae55f3949'
if sha256(BASE.read_bytes()).hexdigest() != BASE_PIN:
    raise RuntimeError('base search drift')
# The pinned base program verifies its graph, payloads and positive control;
# capture its output while reusing its actual deterministic values and helpers.
with contextlib.redirect_stdout(io.StringIO()):
    base = runpy.run_path(str(BASE))
prime, samples = base['PRIME'], base['SAMPLES']
evaluate, live_count = base['evaluate'], base['live_count']
original_rows, variables, fixed = base['rows'], base['variables'], base['fixed']


def search(rows, fixed_ports=None):
    uses = {row[0]: [] for row in rows}
    for row in rows:
        for arg in set(row[2:]):
            if arg in uses:
                uses[arg].append(row)
    eligible = {name for name, consumers in uses.items()
                if consumers and all(r[1] == '*' and r[2] == name and r[3] == name for r in consumers)}
    rng = random.Random(base['SEED'])
    values = {v: tuple(rng.randrange(1, prime) for _ in range(samples)) for v in variables}
    if fixed_ports:
        values.update({v: (n % prime,) * samples for v, n in fixed_ports.items()})
    values.update({n: (n,) * samples for n in range(5)})
    before = live_count(rows, 'P12')
    results, counts = [], {'targets': 0, 'first_gates': 0, 'second_queries': 0,
                           'square_root_queries': 0, 'nonconstant_zero_samples': 0,
                           'target_zero_samples': 0}
    for index, (name, op, left, right) in enumerate(rows):
        if name in values or left not in values or right not in values:
            raise ValueError(f'bad topological row {name}')
        original = evaluate(op, values[left], values[right])
        if name not in eligible:
            values[name] = original
            continue
        target = tuple(-x % prime for x in original)
        counts['target_zero_samples'] += int(any(x == 0 for x in target))
        earlier, pool = list(values), {}
        for i, a in enumerate(earlier):
            for b in earlier[i:]:
                for operation in ('+', '*'):
                    pool.setdefault(evaluate(operation, values[a], values[b]), []).append((operation, a, b))
                    counts['first_gates'] += 1
            for b in earlier:
                pool.setdefault(evaluate('-', values[a], values[b]), []).append(('-', a, b))
                counts['first_gates'] += 1
        for operation, a, b in pool.get(target, []):
            replacement = rows[:index] + [[name, operation, a, b]] + rows[index + 1:]
            size = live_count(replacement, 'P12')
            if size < before:
                results.append({'target': name, 'first': [operation, a, b], 'live': size})
        for c in earlier:
            cv = values[c]
            queries = [('+', evaluate('-', target, cv)), ('-', evaluate('+', target, cv)),
                       ('r-', evaluate('-', cv, target))]
            if all(cv):
                queries.append(('*', tuple(t * pow(v, -1, prime) % prime for t, v in zip(target, cv))))
            elif c != 0:
                counts['nonconstant_zero_samples'] += 1
            for operation, need in queries:
                counts['second_queries'] += 1
                for first, a, b in pool.get(need, []):
                    temp = '__fresh_sign_gate__'
                    second = [name, '-', c, temp] if operation == 'r-' else [name, operation, temp, c]
                    replacement = rows[:index] + [[temp, first, a, b], second] + rows[index + 1:]
                    size = live_count(replacement, 'P12')
                    if size < before:
                        results.append({'target': name, 'first': [first, a, b],
                                        'second': [operation, c], 'live': size})
        roots = [pow(t, (prime + 1) // 4, prime) for t in target]
        if all(r * r % prime == t for r, t in zip(roots, target)):
            for signs in product((1, -1), repeat=samples):
                counts['square_root_queries'] += 1
                need = tuple(r * s % prime for r, s in zip(roots, signs))
                for first, a, b in pool.get(need, []):
                    temp = '__fresh_sign_gate__'
                    replacement = rows[:index] + [[temp, first, a, b], [name, '*', temp, temp]] + rows[index + 1:]
                    size = live_count(replacement, 'P12')
                    if size < before:
                        results.append({'target': name, 'first': [first, a, b],
                                        'second': ['square'], 'live': size})
        values[name] = original
        counts['targets'] += 1
    return {'eligible': sorted(eligible), 'original_live': before, 'candidates': results, 'counts': counts}


if any(r[0] in ('__fresh_sign_gate__', '__sign_control__') for r in original_rows):
    raise RuntimeError('fresh name collision')
zindex = next(i for i, row in enumerate(original_rows) if row[0] == 'Z')
if original_rows[zindex] != ['Z', '-', 'g34', 'folded_q3Bt']:
    raise RuntimeError('unexpected positive-control site')
control = (original_rows[:zindex] + [['__sign_control__', '-', 'folded_q3Bt', 'g34'],
                                   ['Z', '-', 0, '__sign_control__']] + original_rows[zindex + 1:])
symbolic = search(original_rows)
concrete = search(original_rows, fixed)
test = search(control)
if not any(c['target'] == 'Z' and c['live'] < test['original_live'] for c in test['candidates']):
    raise RuntimeError('sign-change positive control was not detected')
for result in (symbolic, concrete):
    if result['counts']['target_zero_samples'] or result['counts']['nonconstant_zero_samples']:
        raise RuntimeError('zero-sample case needs separate handling')
print(json.dumps({'source_sha256': sha256(Path(__file__).read_bytes()).hexdigest(),
                  'base_source_sha256': BASE_PIN, 'graph_sha256': base['PIN'],
                  'prime': prime, 'samples': samples, 'seed': base['SEED'],
                  'python_version': sys.version.split()[0], 'universal_ports': symbolic,
                  'fixed_ports': concrete, 'positive_control': test}, indent=2, sort_keys=True))
