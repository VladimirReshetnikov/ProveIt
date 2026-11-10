#!/usr/bin/env python3
"""Build one shared difference of the sign14 87-gate AST."""
import copy
import hashlib
import json
import sys
from collections import Counter
from pathlib import Path

if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:
    raise SystemExit('use python3 -I -S -B')
P = Path(__file__).resolve().parent
source = P.parent / 'nine-sharing-sign14-87gate-candidate/seed.json'
raw = source.read_bytes()
source_hash = hashlib.sha256(raw).hexdigest()
if source_hash != 'a2d509d3e5b693f3b0f4bb994eeb7e60e32c5ca2937206179599d574e7103998':
    raise RuntimeError('source hash')
original = json.loads(raw)
A = lambda a, b: ['add', a, b]
S = lambda a, b: ['sub', a, b]
M = lambda a, b: ['mul', a, b]
N = lambda n: ['num', n]
V = lambda n: ['var', n]
P0 = lambda p: ['port', p]
b = M(P0('beta'), A(V(1), N(1)))
q = A(b, N(1))
r = A(M(b, S(b, V(2))), A(V(3), N(1)))
R = A(M(r, M(q, q)), M(A(P0('MC'), M(q, P0('MF'))), A(V(1), N(1))))
hits = 0


def rewrite(e):
    global hits
    if e[0] == 'sub' and e[1][0] == 'add' and e[1][2] == r and e[2] == R:
        hits += 1
        return S(rewrite(e[1][1]), S(copy.deepcopy(R), copy.deepcopy(r)))
    if e[0] in ('add', 'sub', 'mul'):
        return [e[0], rewrite(e[1]), rewrite(e[2])]
    return copy.deepcopy(e)


result = copy.deepcopy(original)
for row in result['residuals']:
    row['expr'] = rewrite(row['expr'])
if hits != 4:
    raise RuntimeError(('unexpected rewrite count', hits))

# Normalize (a+r)-R = a-(R-r) as sparse integer polynomials.
def add(a, b):
    out = dict(a)
    for k, v in b.items():
        out[k] = out.get(k, 0) + v
        if not out[k]: del out[k]
    return out
def neg(a): return {k: -v for k, v in a.items()}
A0, R0, T0 = {(1,0,0):1}, {(0,1,0):1}, {(0,0,1):1}
assert add(add(A0, R0), neg(T0)) == add(A0, neg(add(T0, neg(R0))))

def arithmetic(op, a, b0):
    if op == 'add': return a + b0
    if op == 'sub': return a - b0
    if op == 'mul': return a * b0
    raise ValueError(op)
def evaluate(e, variables, ports):
    if e[0] in ('add', 'sub', 'mul'):
        return arithmetic(e[0], evaluate(e[1], variables, ports), evaluate(e[2], variables, ports))
    if e[0] == 'num': return e[1]
    if e[0] == 'var': return variables[e[1]]
    if e[0] == 'port': return ports[e[1]]
    raise ValueError('unknown AST')
for offset in range(4):
    variables = {i: (i + offset) % 3 for i in range(1, 15)}
    ports = {p: (i + offset) % 4 for i, p in enumerate(('beta', 'K0', 'MC', 'MF'))}
    for before, after in zip(original['residuals'], result['residuals']):
        if evaluate(before['expr'], variables, ports) != evaluate(after['expr'], variables, ports):
            raise RuntimeError('direct residual evaluation mismatch')

nodes, ids = [], {}
def node(op, left, right):
    key = (op, left, right)
    if key not in ids:
        ids[key] = len(nodes)
        nodes.append(key)
    return ('node', ids[key])
def lower(e):
    if e[0] in ('add', 'sub', 'mul'):
        return node(e[0], lower(e[1]), lower(e[2]))
    if e[0] in ('var', 'port', 'num') and len(e) == 2: return (e[0], e[1])
    raise ValueError('unknown AST')
roots = [lower(row['expr']) for row in result['residuals']]
residual_count = len(nodes)
squares = [node('mul', x, x) for x in roots]
output = squares[0]
for x in squares[1:]: output = node('add', output, x)
counts = Counter(n[0] for n in nodes)
if residual_count != 77 or len(nodes) != 86 or counts != {'add': 30, 'sub': 18, 'mul': 38}:
    raise RuntimeError(('unexpected circuit size', residual_count, len(nodes), counts))
live = set()
def visit(x):
    if x[0] == 'node' and x[1] not in live:
        live.add(x[1])
        for y0 in nodes[x[1]][1:]: visit(y0)
visit(output)
if len(live) != len(nodes): raise RuntimeError('dead circuit node')
result['status'] = 'external ring-rewrite candidate; Lean equivalence and external file binding unproved'
result.setdefault('rewrite_history', []).append(result.pop('rewrite_provenance'))
result['rewrite_provenance'] = {
    'source': '../nine-sharing-sign14-87gate-candidate/seed.json', 'source_sha256': source_hash,
    'identity': '(a+r)-R=a-(R-r)', 'occurrences': hits,
    'scope': 'Exact integer-ring identity; Lean translation remains unproved.'}
out = (json.dumps(result, indent=2, sort_keys=True) + '\n').encode()
(P / 'seed.json').write_bytes(out)
print(json.dumps({'status': 'PASS_EXTERNAL_RING_REWRITE_AND_CIRCUIT', 'source_sha256': source_hash,
                  'candidate_sha256': hashlib.sha256(out).hexdigest(), 'identity_occurrences': hits,
                  'residual_gates': residual_count, 'total_gates': len(nodes),
                  'gate_counts': dict(sorted(counts.items())), 'live_gates': len(live), 'evaluation_controls': 4,
                  'scope': 'External polynomial identity and exact-sharing circuit; Lean equivalence/minimality not established.'}, sort_keys=True))
