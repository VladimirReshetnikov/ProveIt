#!/usr/bin/env python3
"""Finite modular prefilter for one- and two-gate local DAG rewrites."""
from hashlib import sha256
from itertools import product
import gzip
import json
from pathlib import Path
import random
import sys

ROOT = Path(__file__).resolve().parents[4]
GRAPH = ROOT / 'Computability/DiophantineConsistency/con-zfc-diophantine-forms/115-synchronized-exponents/supplement/circuits/positive12_95_degree70.json'
PIN = '2348183cb8e366433f668cdcc9d77ca9c7e2d0c55b7b630bda39bd8db7506d22'
PRIME = 1_000_000_007
SAMPLES = 3
SEED = 0x46BE
if PRIME % 4 != 3 or any(PRIME % d == 0 for d in range(2, int(PRIME**0.5) + 1)):
    raise RuntimeError('expected a prime congruent to three modulo four')


def evaluate(op, left, right):
    if op == '+':
        return tuple((x + y) % PRIME for x, y in zip(left, right))
    if op == '-':
        return tuple((x - y) % PRIME for x, y in zip(left, right))
    if op == '*':
        return tuple(x * y % PRIME for x, y in zip(left, right))
    raise ValueError(op)


def live_count(rows, output):
    dependencies = {name: (a, b) for name, _, a, b in rows}
    live, pending = set(), [output]
    while pending:
        node = pending.pop()
        if node in dependencies and node not in live:
            live.add(node)
            pending.extend(dependencies[node])
    return len(live)


def search(rows, variables, output, fixed=None):
    rng = random.Random(SEED)
    values = {x: tuple(rng.randrange(1, PRIME) for _ in range(SAMPLES)) for x in variables}
    if fixed:
        values.update({x: (value % PRIME,) * SAMPLES for x, value in fixed.items()})
    values.update({x: (x,) * SAMPLES for x in range(5)})
    original = live_count(rows, output)
    one, two = [], []
    counts = {'targets': 0, 'targets_with_sample_zero': 0, 'first_gates': 0, 'second_queries': 0,
              'sample_zero_nonconstant': 0, 'square_root_queries': 0}
    for index, (name, op, left, right) in enumerate(rows):
        if name in values or left not in values or right not in values:
            raise ValueError(f'non-topological or duplicate row: {name}')
        target = evaluate(op, values[left], values[right])
        counts['targets_with_sample_zero'] += int(any(x == 0 for x in target))
        earlier = list(values)
        pool = {}
        for i, a in enumerate(earlier):
            for b in earlier[i:]:
                for operation in ('+', '*'):
                    pool.setdefault(evaluate(operation, values[a], values[b]), []).append((operation, a, b))
                    counts['first_gates'] += 1
            for b in earlier:
                pool.setdefault(evaluate('-', values[a], values[b]), []).append(('-', a, b))
                counts['first_gates'] += 1
        for operation, a, b in pool.get(target, []):
            changed = rows[:index] + [[name, operation, a, b]] + rows[index + 1:]
            size = live_count(changed, output)
            if size < original:
                one.append({'target': name, 'replacement': [operation, a, b], 'live': size})

        def try_first(need, operation, c):
            for first, a, b in pool.get(need, []):
                temp = '__fresh_local_gate__'
                second = [name, '-', c, temp] if operation == 'r-' else [name, operation, temp, c]
                changed = rows[:index] + [[temp, first, a, b], second] + rows[index + 1:]
                size = live_count(changed, output)
                if size < original:
                    two.append({'target': name, 'first': [first, a, b], 'second': [operation, c], 'live': size})

        for c in earlier:
            cv = values[c]
            queries = [('+', evaluate('-', target, cv)),
                       ('-', evaluate('+', target, cv)),
                       ('r-', evaluate('-', cv, target))]
            if all(cv):
                queries.append(('*', tuple(t * pow(v, -1, PRIME) % PRIME for t, v in zip(target, cv))))
            elif c != 0:
                counts['sample_zero_nonconstant'] += 1
            for operation, need in queries:
                counts['second_queries'] += 1
                try_first(need, operation, c)
        # The second gate may also square the fresh first gate. PRIME is 3 mod 4.
        roots = [pow(t, (PRIME + 1) // 4, PRIME) for t in target]
        if all(r * r % PRIME == t for r, t in zip(roots, target)):
            for signs in product((1, -1), repeat=SAMPLES):
                counts['square_root_queries'] += 1
                need = tuple(r * sign % PRIME for r, sign in zip(roots, signs))
                for first, a, b in pool.get(need, []):
                    temp = '__fresh_local_gate__'
                    changed = rows[:index] + [[temp, first, a, b], [name, '*', temp, temp]] + rows[index + 1:]
                    size = live_count(changed, output)
                    if size < original:
                        two.append({'target': name, 'first': [first, a, b], 'second': ['square'], 'live': size})
        values[name] = target
        counts['targets'] += 1
    return {'original_live': original, 'one_gate_candidates': one,
            'two_gate_candidates': two, 'counts': counts}


raw = GRAPH.read_bytes()
if sha256(raw).hexdigest() != PIN:
    raise RuntimeError('source graph hash drift')
graph = json.loads(raw)
rows = graph['source']
variables = graph['witnesses'] + graph['fixed_numerals']
if len(rows) != 95 or graph['output'] != 'P12' or live_count(rows, 'P12') != 95:
    raise RuntimeError('unexpected source or live gate count')
if rows[-1] != ['P12', '-', 'g98', 1] or any(r[0] in ('__fresh_local_gate__', '__control__') for r in rows):
    raise RuntimeError('unexpected control/output names')
result = search(rows, variables, 'P12')
# Also test at the actual fixed coefficient residues from the manifest-pinned
# supplement. Equality over the integers must remain equality modulo PRIME.
coeff = GRAPH.parent.parent / 'coefficients'
binding_raw = (coeff / 'BINDING.json').read_bytes()
binding_hash = sha256(binding_raw).hexdigest()
if binding_hash != 'dd13365e1c68cd244e67a61abfeb5b351c3ad679acb55a73f714d2885341ee01':
    raise RuntimeError('coefficient binding hash drift')
binding = json.loads(binding_raw)
fixed = {}
for name in graph['fixed_numerals']:
    meta = binding['ports'][name]
    compressed = (coeff / meta['file']).read_bytes()
    if sha256(compressed).hexdigest() != meta['sha256_gzip']:
        raise RuntimeError(f'compressed coefficient drift: {name}')
    data = gzip.decompress(compressed)
    if sha256(data).hexdigest() != meta['sha256_raw'] or len(data) != meta['raw_bytes']:
        raise RuntimeError(f'raw coefficient drift: {name}')
    fixed[name] = int.from_bytes(data, 'little')
fixed_result = search(rows, variables, 'P12', fixed)
# A source-equivalent but deliberately redundant output computes (g98+1)-2.
control = rows[:-1] + [['__control__', '+', 'g98', 1], ['P12', '-', '__control__', 2]]
control_result = search(control, variables, 'P12')
if not control_result['one_gate_candidates'] or not control_result['two_gate_candidates']:
    raise RuntimeError('positive control was not detected')
for tested in (result, fixed_result):
    if tested['counts']['sample_zero_nonconstant'] or tested['counts']['targets_with_sample_zero']:
        raise RuntimeError('zero sample needs separate multiplication/zero handling')
print(json.dumps({'graph_sha256': PIN, 'source_sha256': sha256(Path(__file__).read_bytes()).hexdigest(),
                  'python_version': sys.version.split()[0], 'prime': PRIME, 'samples': SAMPLES, 'seed': SEED,
                  'binding_sha256': binding_hash,
                  'fixed_port_residues': {x: fixed[x] % PRIME for x in graph['fixed_numerals']},
                  'universal_port_search': result, 'fixed_port_search': fixed_result,
                  'positive_control': control_result}, indent=2, sort_keys=True))
