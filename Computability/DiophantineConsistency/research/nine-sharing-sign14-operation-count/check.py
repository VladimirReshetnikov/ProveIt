#!/usr/bin/env python3
"""Count binary gates in the external sign14 sum-of-squares AST by exact sharing."""
import hashlib
import json
import sys
from collections import Counter
from pathlib import Path

if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:
    raise SystemExit('use python3 -I -S -B')
P = Path(__file__).resolve().parent
seed = P.parent / 'nine-sharing-sign14-tau-candidate/seed.json'
raw = seed.read_bytes()
if hashlib.sha256(raw).hexdigest() != '7048a10d409ab5ff8031a444cd32117ba772b3834425c17a066188338e189ea9':
    raise RuntimeError('seed hash mismatch')
data = json.loads(raw)
if data['witness_count'] != 14 or len(data['residuals']) != 5:
    raise RuntimeError('unexpected seed shape')

nodes = []
intern = {}
leaves = {'var': set(), 'port': set(), 'num': set()}


def node(op, args):
    key = (op, *args)
    if key not in intern:
        intern[key] = len(nodes)
        nodes.append(key)
    return ('node', intern[key])


def lower(e):
    if not isinstance(e, list) or not e:
        raise ValueError('bad AST')
    op = e[0]
    if op in ('add', 'sub', 'mul') and len(e) == 3:
        return node(op, (lower(e[1]), lower(e[2])))
    if op == 'var' and len(e) == 2 and type(e[1]) is int and 1 <= e[1] <= 14:
        leaves[op].add(e[1])
        return (op, e[1])
    if op == 'port' and len(e) == 2 and e[1] in ('beta', 'K0', 'MC', 'MF'):
        leaves[op].add(e[1])
        return (op, e[1])
    if op == 'num' and len(e) == 2 and type(e[1]) is int:
        leaves[op].add(e[1])
        return (op, e[1])
    raise ValueError(('bad leaf or operator', e))


roots = [lower(row['expr']) for row in data['residuals']]
residual_count = len(nodes)
squares = [node('mul', (x, x)) for x in roots]
output = squares[0]
for square in squares[1:]:
    output = node('add', (output, square))
counts = Counter(n[0] for n in nodes)
if len(set(roots)) != 5 or leaves['var'] != set(range(1, 15)) or leaves['port'] != {'beta', 'K0', 'MC', 'MF'}:
    raise RuntimeError('unexpected root or input coverage')
if residual_count != 89 or counts != {'add': 41, 'sub': 15, 'mul': 42} or len(nodes) != 98:
    raise RuntimeError('unexpected gate count')
for i, entry in enumerate(nodes):
    for kind, value in entry[1:]:
        if kind == 'node' and value >= i:
            raise RuntimeError('non-topological node')
if output != ('node', 97):
    raise RuntimeError('unexpected output')
live = set()
def visit(x):
    if x[0] == 'node' and x[1] not in live:
        live.add(x[1])
        for y in nodes[x[1]][1:]:
            visit(y)
visit(output)
if len(live) != len(nodes):
    raise RuntimeError('dead gates')

def arithmetic(op, x, y):
    if op == 'add': return x + y
    if op == 'sub': return x - y
    if op == 'mul': return x * y
    raise ValueError(op)

def tree_value(e, vars_, ports):
    if e[0] in ('add', 'sub', 'mul'):
        return arithmetic(e[0], tree_value(e[1], vars_, ports), tree_value(e[2], vars_, ports))
    if e[0] == 'var': return vars_[e[1]]
    if e[0] == 'port': return ports[e[1]]
    if e[0] == 'num': return e[1]
    raise ValueError(e[0])

for offset in range(4):
    vs = {i: (i + offset) % 3 for i in range(1, 15)}
    ps = {p: (i + offset) % 4 for i, p in enumerate(('beta', 'K0', 'MC', 'MF'))}
    values = []
    def val(x):
        if x[0] == 'node': return values[x[1]]
        if x[0] == 'var': return vs[x[1]]
        if x[0] == 'port': return ps[x[1]]
        if x[0] == 'num': return x[1]
        raise ValueError(x[0])
    for op, a, b in nodes:
        values.append(arithmetic(op, val(a), val(b)))
    if val(output) != sum(tree_value(row['expr'], vs, ps) ** 2 for row in data['residuals']):
        raise RuntimeError('DAG evaluation differs from source AST')
print(json.dumps({'status': 'PASS_EXTERNAL_EXACT_SHARING_COUNT', 'residual_gates': residual_count,
                  'output_gates': len(nodes), 'binary_gate_counts': dict(sorted(counts.items())),
                  'live_gates': len(live), 'evaluation_controls': 4, 'witnesses': 14,
                  'ports': 4, 'seed_sha256': hashlib.sha256(raw).hexdigest(),
                  'scope': 'Structural hash-consing of external AST and sum of squares; upper bound under this gate convention, no Lean/JSON binding or minimality.'}, sort_keys=True))
