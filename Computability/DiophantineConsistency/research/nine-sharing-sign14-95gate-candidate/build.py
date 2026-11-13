#!/usr/bin/env python3
"""Build and externally validate two exact ring rewrites of the sign14 AST."""
import copy
import hashlib
import json
import sys
from collections import Counter
from pathlib import Path

if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:
    raise SystemExit('use python3 -I -S -B')
P = Path(__file__).resolve().parent
source = P.parent / 'nine-sharing-sign14-tau-candidate/seed.json'
raw = source.read_bytes()
source_hash = hashlib.sha256(raw).hexdigest()
if source_hash != '7048a10d409ab5ff8031a444cd32117ba772b3834425c17a066188338e189ea9':
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
w = V(9)
w1 = A(w, N(1))
old_xb = A(M(w, q), b)
new_xb = S(M(w1, q), N(1))
hits = 0


def rewrite(e):
    global hits
    if e == old_xb:
        hits += 1
        return copy.deepcopy(new_xb)
    if e[0] in ('add', 'sub', 'mul'):
        return [e[0], rewrite(e[1]), rewrite(e[2])]
    return copy.deepcopy(e)


result = copy.deepcopy(original)
for row in result['residuals']:
    row['expr'] = rewrite(row['expr'])
if hits != 10:
    raise RuntimeError(('unexpected first-rewrite count', hits))
a = A(P0('K0'), w1)
d = A(V(2), N(1))
g = A(V(3), N(1))
c = A(d, g)
z = M(A(V(4), N(1)), b)
old_nt = S(S(A(M(a, q), q), A(A(M(a, c), d), z)), N(1))
new_nt = S(S(A(M(a, S(q, c)), b), d), z)
if result['residuals'][2]['gate'] != 'Nt' or result['residuals'][2]['expr'] != old_nt:
    raise RuntimeError('unexpected Nt expression')
result['residuals'][2]['expr'] = new_nt

# Check the two local identities as formal integer polynomials, using sparse
# exponent tuples. The second identity uses the defining equation q=b+1.
dim = 6
zero = (0,) * dim
def const(n): return {zero: n} if n else {}
def var(i):
    e = [0] * dim
    e[i] = 1
    return {tuple(e): 1}
def add(x, y, sign=1):
    z0 = dict(x)
    for k, v in y.items():
        z0[k] = z0.get(k, 0) + sign * v
        if not z0[k]: del z0[k]
    return z0
def mul(x, y):
    z0 = {}
    for k, v in x.items():
        for l, u in y.items():
            key = tuple(i + j for i, j in zip(k, l))
            z0[key] = z0.get(key, 0) + v * u
    return {k: v for k, v in z0.items() if v}
B, W, AA, CC, DD, ZZ = [var(i) for i in range(dim)]
Q = add(B, const(1))
assert add(mul(W, Q), B) == add(mul(add(W, const(1)), Q), const(-1))
lhs = add(add(add(mul(AA, Q), Q), add(add(mul(AA, CC), DD), ZZ), -1), const(-1))
rhs = add(add(add(mul(AA, add(Q, CC, -1)), B), DD, -1), ZZ, -1)
assert lhs == rhs

def arithmetic(op, x, y):
    if op == 'add': return x + y
    if op == 'sub': return x - y
    if op == 'mul': return x * y
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

# Construct the exact ordered-subtree-sharing circuit, including all squares.
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
    if e[0] in ('var', 'port', 'num') and len(e) == 2:
        return (e[0], e[1])
    raise ValueError('unknown AST')
roots = [lower(row['expr']) for row in result['residuals']]
residual_count = len(nodes)
squares = [node('mul', x, x) for x in roots]
output = squares[0]
for x in squares[1:]: output = node('add', output, x)
counts = Counter(n[0] for n in nodes)
if residual_count != 86 or len(nodes) != 95 or counts != {'add': 38, 'sub': 17, 'mul': 40}:
    raise RuntimeError(('unexpected circuit size', residual_count, len(nodes), counts))
live = set()
def visit(x):
    if x[0] == 'node' and x[1] not in live:
        live.add(x[1])
        for y in nodes[x[1]][1:]: visit(y)
visit(output)
if len(live) != len(nodes): raise RuntimeError('dead circuit node')
result['status'] = 'external ring-rewrite candidate; Lean equivalence and external file binding unproved'
result['rewrite_provenance'] = {
    'source': '../nine-sharing-sign14-tau-candidate/seed.json', 'source_sha256': source_hash,
    'identity_1': 'w*q+b=(w+1)*q-1 where q=b+1', 'identity_1_occurrences': hits,
    'identity_2': '(a*q+q)-(a*c+d+z)-1=a*(q-c)+b-d-z where q=b+1',
    'scope': 'Exact integer-ring identities; Lean translation remains unproved.'}
out = (json.dumps(result, indent=2, sort_keys=True) + '\n').encode()
(P / 'seed.json').write_bytes(out)
print(json.dumps({'status': 'PASS_EXTERNAL_RING_REWRITE_AND_CIRCUIT', 'source_sha256': source_hash,
                  'candidate_sha256': hashlib.sha256(out).hexdigest(), 'identity_1_occurrences': hits,
                  'residual_gates': residual_count, 'total_gates': len(nodes),
                  'gate_counts': dict(sorted(counts.items())), 'live_gates': len(live), 'evaluation_controls': 4,
                  'scope': 'External sparse-polynomial local identities and exact-sharing circuit; Lean equivalence/minimality not established.'}, sort_keys=True))
