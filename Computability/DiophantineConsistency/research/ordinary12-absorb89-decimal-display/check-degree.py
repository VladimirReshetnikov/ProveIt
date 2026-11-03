#!/usr/bin/env python3
"""Verify the fixed-coefficient 89-row draft's exact polynomial degree."""
from collections import Counter
from hashlib import sha256
import gzip
import json
from pathlib import Path
import sys

if sys.flags.optimize:
    raise SystemExit('optimized Python refused')

D = Path(__file__).resolve().parents[2]
GRAPH = D / 'research/ordinary12-absorb89-probe/graph-dag.json'
COEFF = D / 'con-zfc-diophantine-forms/115-synchronized-exponents/supplement/coefficients'
BINDING = COEFF / 'BINDING.json'
PINS = {
    GRAPH: '280b23e5be95692b9db0183affce4247d974320ded1e709f41b05cc7e32b2fdd',
    BINDING: 'dd13365e1c68cd244e67a61abfeb5b351c3ad679acb55a73f714d2885341ee01',
}

def need(condition, message):
    if not condition:
        raise SystemExit(message)

def sha(path):
    return sha256(Path(path).read_bytes()).hexdigest()

for path, digest in PINS.items():
    need(sha(path) == digest, 'input hash mismatch: ' + str(path))
graph = json.loads(GRAPH.read_text())
need(graph['witnesses'] == ['J','F','alpha','t','T','w','s','r','eta','zeta','n','direct'], 'witness order')
need(graph['fixed_numerals'] == ['beta','K0','MC','MF'] and graph['output'] == 'P12', 'port/output mismatch')
rows = graph['source']
parents, known = {}, set(graph['witnesses'] + graph['fixed_numerals'])
for name, op, left, right in rows:
    need(name not in known and op in ('+', '-', '*'), 'bad DAG row')
    for arg in (left, right):
        need(type(arg) is int or isinstance(arg, str) and arg in known, 'unknown/forward input')
    known.add(name)
    parents[name] = (left, right)
live, todo = set(), [graph['output']]
while todo:
    name = todo.pop()
    if name in parents and name not in live:
        live.add(name)
        todo.extend(arg for arg in parents[name] if isinstance(arg, str))
counts = dict(Counter(row[1] for row in rows))
need(len(rows) == len(live) == 89 and live == set(parents) and
     counts == {'*': 50, '+': 22, '-': 17}, 'operation count/liveness mismatch')
by_name = {row[0]: row[1:] for row in rows}

# Verify the exact three-variable cancellation by sparse integer polynomial
# arithmetic: (1-Q)(V+n)^2+QV^2-1 = (V+n)^2-1-Qn(2V+n).
Z = (0, 0, 0)
def const(n):
    return {Z: n} if n else {}
def var(i):
    a = list(Z); a[i] = 1
    return {tuple(a): 1}
def add(a, b):
    z = dict(a)
    for k, v in b.items():
        z[k] = z.get(k, 0) + v
        if not z[k]: del z[k]
    return z
def neg(a): return {k: -v for k, v in a.items()}
def sub(a, b): return add(a, neg(b))
def mul(a, b):
    z = {}
    for ka, va in a.items():
        for kb, vb in b.items():
            k = tuple(x + y for x, y in zip(ka, kb))
            z[k] = z.get(k, 0) + va * vb
    return {k: v for k, v in z.items() if v}
Q, V, n = (var(i) for i in range(3))
one = const(1); vn = add(V, n)
need(add(mul(sub(one, Q), mul(vn, vn)), sub(mul(Q, mul(V, V)), one)) ==
     sub(sub(mul(vn, vn), one), mul(mul(Q, n), add(add(V, V), n))), 'h identity')
shape = {'vn':['+','V','n'], 'vn2':['*','vn','vn'], 'polarV2':['*','V','V'],
         'polarQV2':['*','Q','polarV2'], 'polarCy':['-','polarQV2',1],
         'oneQ':['-',1,'Q'], 'polarHpart':['*','oneQ','vn2'], 'h':['+','polarHpart','polarCy']}
need(all(by_name.get(k) == v for k, v in shape.items()), 'h graph shape')

deg = {name: 1 for name in graph['witnesses']}
deg.update({name: 0 for name in graph['fixed_numerals']})
for name, op, left, right in rows:
    dl = deg[left] if isinstance(left, str) else 0
    dr = deg[right] if isinstance(right, str) else 0
    deg[name] = dl + dr if op == '*' else max(dl, dr)
    if name == 'h':
        dq, dv, dn = deg['Q'], deg['V'], deg['n']
        need((dq, dv, dn) == (14, 8, 1), 'unexpected cancellation premises')
        deg[name] = max(2 * max(dv, dn), dq + dn + max(dv, dn))
keys = ('Q','V','h','den','polarT','polarA','polarCorrection','N','A0','A1','P12')
upper = {name: deg[name] for name in keys}
need(upper == {'Q':14,'V':8,'h':23,'den':20,'polarT':28,'polarA':43,
               'polarCorrection':78,'N':86,'A0':24,'A1':34,'P12':172}, 'upper bound mismatch')

# A one-variable modular specialization cannot increase total degree. A
# nonzero coefficient of t^172 therefore supplies the matching lower bound.
prime = 1000000007
values = {name: [0, i + 2] for i, name in enumerate(graph['witnesses'])}
binding = json.loads(BINDING.read_text())
payload_pins = {}
for name in graph['fixed_numerals']:
    meta = binding['ports'][name]
    path = COEFF / meta['file']
    compressed = path.read_bytes()
    raw = gzip.decompress(compressed)
    need(sha256(compressed).hexdigest() == meta['sha256_gzip'] and
         sha256(raw).hexdigest() == meta['sha256_raw'] and len(raw) == meta['raw_bytes'],
         'payload mismatch: ' + name)
    payload_pins[path] = meta['sha256_gzip']
    values[name] = [int.from_bytes(raw, 'little') % prime]

def poly(op, a, b):
    if op == '*':
        z = [0] * (len(a) + len(b) - 1)
        for i, x in enumerate(a):
            for j, y in enumerate(b):
                z[i+j] = (z[i+j] + x*y) % prime
    else:
        sign = 1 if op == '+' else -1
        z = [((a[i] if i < len(a) else 0) + sign*(b[i] if i < len(b) else 0)) % prime
             for i in range(max(len(a), len(b)))]
    while len(z) > 1 and not z[-1]: z.pop()
    return z

for name, op, left, right in rows:
    values[name] = poly(op, values[left] if isinstance(left, str) else [left],
                        values[right] if isinstance(right, str) else [right])
need(len(values['P12']) - 1 == 172 and values['P12'][-1] == 960910299, 'lower bound mismatch')
for path, digest in {**PINS, **payload_pins}.items():
    need(sha(path) == digest, 'input changed: ' + str(path))
print(json.dumps({'status':'PASS', 'live_operations':len(live), 'operation_breakdown':counts,
                  'upper_bounds':upper, 'prime':prime,
                  'specialized_degree':len(values['P12'])-1,
                  'leading_coefficient':values['P12'][-1],
                  'scope':'external graph/degree check; not a Lean graph, iPRA or file theorem'}, indent=2))
