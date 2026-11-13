#!/usr/bin/env python3
"""Reproducible local finite-field prefilter for the audited Positive74 gate graph.

The modular prefilter is not an equality certificate. Validate every candidate
using exact symbolic arithmetic and recalculate output reachability.
"""
import hashlib, json, random, re, sys
from itertools import product
from pathlib import Path
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize: raise SystemExit('use python3 -I -S -B')
P=Path(__file__).resolve().parent
SOURCE=P.parent/'nine-sharing-sign14-positive74-circuit-retry01-check/src/DiophantineConsistency/Sign14Positive74Circuit.lean'
PIN='cdd4117cd0b8af7eefbca2d53388068350970f78dba7e73dc9be2fe1b51f105d'
PRIME=1_000_000_007
SAMPLES=3
SEED=0x46BE
if PRIME % 4 != 3 or any(PRIME % d == 0 for d in range(2, int(PRIME**0.5)+1)): raise RuntimeError('prime check')

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
    values.update({x: (x,) * SAMPLES for x in range(-4, 9)})
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


raw=SOURCE.read_bytes()
if hashlib.sha256(raw).hexdigest()!=PIN:raise RuntimeError('source pin drift')
s=raw.decode().split('def gates : List Gate := [',1)[1].split(']\ndef parents',1)[0]
pattern=r'⟨\.(add|sub|mul), \.(var|port|lit|reg) (-?\d+), \.(var|port|lit|reg) (-?\d+)⟩'
parsed=re.findall(pattern,s)
if len(parsed)!=74:raise RuntimeError('gate count')
def arg(t,n):
 n=int(n)
 return n if t=='lit' else {'var':'u','port':'p','reg':'g'}[t]+str(n)
rows=[[f'g{i}',{'add':'+','sub':'-','mul':'*'}[op],arg(a,b),arg(c,d)] for i,(op,a,b,c,d) in enumerate(parsed)]
variables=[f'u{i}' for i in range(14)]+[f'p{i}' for i in range(4)]
if live_count(rows,'g73')!=74:raise RuntimeError('liveness drift')
result=search(rows,variables,'g73')
control=rows[:-1]+[['__control0','+','g72','g69'],['__control1','+','__control0',1],['g73','-','__control1',1]]
control_result=search(control,variables,'g73')
if control_result['original_live']!=76 or not control_result['one_gate_candidates'] or not control_result['two_gate_candidates']:raise RuntimeError('positive control failed')

sign_results=[]
for mask in range(1,32):
    changed=[row[:] for row in rows]
    for i,idx in enumerate((23,41,48,61,64)):
        if mask & (1<<i):
            if changed[idx][1]!='-':raise RuntimeError('root not subtraction')
            changed[idx][2],changed[idx][3]=changed[idx][3],changed[idx][2]
    found=search(changed,variables,'g73')
    if found['counts']['sample_zero_nonconstant'] or found['counts']['targets_with_sample_zero']:raise RuntimeError('sign sample zero needs separate handling')
    if found['one_gate_candidates'] or found['two_gate_candidates']:
        sign_results.append({'mask':mask,'result':found})
print(json.dumps({'source_sha256':PIN,'search_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),'prime':PRIME,'samples':SAMPLES,'seed':SEED,'positive_control':control_result,'result':result,'sign_reversal_candidates':sign_results,'scope':'Finite-field prefilter only: symbolic verification required; no minimality claim.'},indent=2,sort_keys=True))
