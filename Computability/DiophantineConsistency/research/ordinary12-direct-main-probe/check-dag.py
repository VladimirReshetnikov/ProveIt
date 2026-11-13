#!/usr/bin/env python3
"""Audit the direct-main draft DAG, Lean rows, liveness, and forward samples."""
from pathlib import Path
from hashlib import sha256
import collections, json, random, re, sys
if sys.flags.optimize:
    raise SystemExit('optimized Python refused')
H = Path(__file__).resolve().parent
P = H.parent / 'ordinary12-xq91-candidate' / 'candidate.json'
D = H / 'graph-dag.json'
L = H / 'DirectMainGraph.lean'
def digest(path):
    return sha256(path.read_bytes()).hexdigest()
def need(value, message):
    if not value:
        raise RuntimeError(message)
need(digest(P) == 'fde7510bbc984b7160e92ed5caff260fc90a25c9c24437efbf5c2f40c3f92513', 'parent drift')
need(digest(D) == '82dd1f55f67ef3487509a6d4d31ef085d5d4813c11df43be40570a3293a8b430', 'draft drift')
need(digest(L) == '6e465bd6329d4932b3c75e2984f9b771b5ae99d329f946aebba88abaa283c216', 'Lean source drift')
old, new = json.loads(P.read_bytes()), json.loads(D.read_bytes())
need(new['parent_graph_sha256'] == digest(P), 'parent pin mismatch')
need(new['witnesses'] == [('direct' if x == 'gamma' else x) for x in old['witnesses']], 'witness mapping')
need(new['fixed_numerals'] == old['fixed_numerals'] and new['output'] == old['output'], 'port/output mapping')
expected = []
for n, op, x, y in old['source']:
    if n == 'g54':
        continue
    if n == 'g56':
        need((op, x, y) == ('*', 'U', 'g54'), 'old main shape')
        y = 'direct'
    expected.append([n, op, x, y])
need(new['source'] == expected, 'row transformation')
source = L.read_text().split('def graph (p : Fin 4 → ℤ) : Graph :=', 1)[1].split('\nvariable {R : Type*}', 1)[0]
pattern = re.compile(r'^  let (\w+) := (\w+) ([+*\-]) (\w+)$', re.M)
def operand(s):
    return int(s) if s.isdigit() else s
lean_rows = [[n, op, operand(x), operand(y)] for n, x, op, y in pattern.findall(source)]
need(lean_rows == new['source'], 'Lean rows differ from external DAG')
for i, name in enumerate(new['witnesses']):
    need(f'  let {name} : Expr (Fin 12) := .var {i}\n' in source, 'Lean witness slot mismatch')
for i, name in enumerate(new['fixed_numerals']):
    need(f'  let {name} : Expr (Fin 12) := .constant (p {i})\n' in source, 'Lean port slot mismatch')
need('  ⟨A0, A1, N, P12⟩' in source, 'Lean graph outputs')
known = set(new['witnesses'] + new['fixed_numerals']) | set(range(5))
parents = {}
for n, op, x, y in new['source']:
    need(n not in known and x in known and y in known and op in ('+', '-', '*'), 'bad topology')
    known.add(n)
    parents[n] = (x, y)
live = set()
todo = [new['output']]
while todo:
    node = todo.pop()
    if node in parents and node not in live:
        live.add(node)
        todo.extend(parents[node])
counts = {op: sum(row[1] == op for row in new['source']) for op in ('*', '+', '-')}
need(len(new['source']) == len(live) == new['operations'] == 90, 'live operation count')
need(counts == new['operation_breakdown'] == {'*': 50, '+': 23, '-': 17}, 'operation breakdown')
def evaluate(rows, env):
    values = dict(env)
    values.update({i: i for i in range(5)})
    for n, op, x, y in rows:
        a, b = values[x], values[y]
        values[n] = a*b if op == '*' else a+b if op == '+' else a-b
    return values
rng = random.Random(902024)
for _ in range(100):
    env = {k: rng.randrange(1, 5) for k in old['witnesses']}
    env.update({k: rng.randrange(0, 5) for k in old['fixed_numerals']})
    newenv = {k: env[k] for k in new['witnesses'] if k != 'direct'}
    newenv['direct'] = env['gamma'] + env['w']
    newenv.update({k: env[k] for k in new['fixed_numerals']})
    before, after = evaluate(old['source'], env), evaluate(new['source'], newenv)
    for name in new['residuals'] + [new['output']]:
        need(before[name] == after[name], 'forward sample mismatch ' + name)
print(json.dumps({'status':'PASS', 'parent_sha256':digest(P), 'draft_sha256':digest(D),
                  'lean_sha256':digest(L), 'rows':len(new['source']), 'live':len(live),
                  'breakdown':counts, 'forward_exact_integer_samples':100}, indent=2))
