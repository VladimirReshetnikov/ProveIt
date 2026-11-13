#!/usr/bin/env python3
"""Bounded exact-target and square-sign modular prefilter for the 76Y graph."""
import sys
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:
    raise SystemExit("use python3 -I -S -B without optimization")
from hashlib import sha256
from itertools import product
import gzip
import json
from pathlib import Path
import random
import sys

ROOT = Path(__file__).resolve().parents[4]
GRAPH = ROOT / 'Computability/DiophantineConsistency/research/p64-qcube76-independent-y-candidate/graph.json'
PIN = '196ef3bdf6805c7ed7d44c278359e32c0f658634db357cc19f0e87464ed6b11c'
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



def alias_and_square_sign(rows, variables, output):
    rng = random.Random(SEED)
    values = {x: tuple(rng.randrange(1, PRIME) for _ in range(SAMPLES)) for x in variables}
    values.update({x: (x,) * SAMPLES for x in range(5)})
    consumers = {name: [] for name, *_ in rows}
    for dest, op, a, b in rows:
        for node in {a, b}:
            if node in consumers: consumers[node].append((dest, op, a, b))
    aliases, signs = [], []
    original = live_count(rows, output)
    for index, (name, op, left, right) in enumerate(rows):
        target = evaluate(op, values[left], values[right])
        for a in list(values):
            if values[a] != target: continue
            changed = [list(row) for row in rows if row[0] != name]
            for row in changed:
                row[2:] = [a if x == name else x for x in row[2:]]
            new_output = a if name == output else output
            size = live_count(changed, new_output)
            if size < original: aliases.append({'target':name,'replacement':a,'live':size})
        # Negating a node preserves the output only when every immediate
        # consumer squares it and the node is not itself the output.
        uses = consumers[name]
        if name != output and uses and all(op2 == '*' and a == name and b == name for _,op2,a,b in uses):
            wanted = tuple((-x) % PRIME for x in target)
            prior = list(values)
            for a in prior:
                for b in prior:
                    if evaluate('-',values[a],values[b]) != wanted: continue
                    changed = rows[:index]+[[name,'-',a,b]]+rows[index+1:]
                    size = live_count(changed,output)
                    if size < original: signs.append({'target':name,'replacement':['-',a,b],'live':size})
        values[name] = target
    return {'aliases': aliases, 'square_only_negations':signs}

raw=GRAPH.read_bytes()
if sha256(raw).hexdigest()!=PIN: raise RuntimeError('source graph hash drift')
graph=json.loads(raw); rows=graph['source']; variables=graph['witnesses']+graph['fixed_numerals']; output=graph['output']
if len(rows)!=76 or output!='polynomial' or live_count(rows,output)!=76: raise RuntimeError('unexpected graph')
result=search(rows,variables,output)
extras=alias_and_square_sign(rows,variables,output)
if result['counts']['sample_zero_nonconstant'] or result['counts']['targets_with_sample_zero']:
    raise RuntimeError('zero sample needs separate treatment')
# An extra final double negation is a positive control for alias and sign.
control=rows[:-1]+[['__neg_one__','-',0,rows[-1][2]],['__neg_two__','-',0,'__neg_one__'],[rows[-1][0],rows[-1][1],'__neg_two__',rows[-1][3]]]
control_result=search(control,variables,output)
if not control_result['one_gate_candidates'] and not alias_and_square_sign(control,variables,output)['aliases']:
    raise RuntimeError('positive control not detected')
sign_control=[['a','+','x',1],['b','-','a',1],['sq','*','b','b'],['N','+','sq',0]]
sign_control_result=alias_and_square_sign(sign_control,['x'],'N')
if not any(x['target']=='b' and x['live']==3 for x in sign_control_result['square_only_negations']):
    raise RuntimeError('square-only sign control not detected')
print(json.dumps({'graph_sha256':PIN,'source_sha256':sha256(Path(__file__).read_bytes()).hexdigest(),
    'prime':PRIME,'samples':SAMPLES,'seed':SEED,'exact_target':result,'extras':extras,
    'positive_control':control_result,'square_sign_control':sign_control_result},indent=2,sort_keys=True))
