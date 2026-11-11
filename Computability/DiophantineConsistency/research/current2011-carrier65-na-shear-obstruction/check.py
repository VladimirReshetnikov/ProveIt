#!/usr/bin/env python3
"""Reproduce finite graph, residue and formal polynomial checks; no Lean."""
import gzip
import hashlib
import itertools
import json
from collections import Counter
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
paths = {
    'audited_graph': ('research/carrier65-independent/INCOMING_CARRIER65.json', 'bf58ed6600eee34d86a802a992e3fd9b999e1835b57a5a83734a40073e1658a7'),
    'maintained_graph': ('candidates/one-page-padding-staircase-carrier65-2011/polynomial.json', 'f1f7611842896806fa9e70ad102c6a0e7aa11747a650968f1c74cb169f0e253e'),
    'audited_proof': ('research/carrier65-independent/PROOF.md', '53ec75050c7f4a00386d9738f8c515f3a816d8e4d94afcebb54b3497d972e749'),
}
contents = {}
for key, (path, expected) in paths.items():
    raw = (ROOT / path).read_bytes()
    actual = hashlib.sha256(raw).hexdigest()
    assert actual == expected, (key, actual)
    contents[key] = raw
base = json.loads(contents['audited_graph'])
maintained = json.loads(contents['maintained_graph'])
rows = base['source']
assert rows == maintained['source'] and len(rows) == 65
assert Counter(r[1] for r in rows) == {'+': 16, '-': 12, '*': 37}
assert base['witnesses'] == ['J', 'F', 'alpha', 'z', 'f', 'i', 'T', 's', 'w', 'n', 'eta', 'zeta', 'y', 'gamma']
ports = maintained['coefficient_binding']['ports']
assert set(ports) == {'beta', 'K0', 'MC', 'MF'}
for meta in ports.values():
    packed = (ROOT / 'candidates/one-page-padding-staircase-carrier65-2011/coefficients' / meta['file']).read_bytes()
    assert hashlib.sha256(packed).hexdigest() == meta['gzip_sha256']
    unpacked = gzip.decompress(packed)
    assert hashlib.sha256(unpacked).hexdigest() == meta['raw_sha256']
    assert len(unpacked) == meta['raw_bytes'] and any(unpacked)
available = set(base['witnesses']) | set(ports)
for name, op, x, y in rows:
    assert name not in available and op in '+-*'
    assert all(isinstance(t, int) or t in available for t in (x, y))
    available.add(name)
by_name = {row[0]: row for row in rows}
assert len(by_name) == len(rows)
needed = {'polynomial'}
for name, _, x, y in reversed(rows):
    if name in needed:
        needed.update((x, y))
assert all(name in needed for name, *_ in rows)
expected = [
    ['qm', '*', 'beta', 'J'], ['q', '+', 'qm', 1],
    ['a', '+', 'E', 'Y'], ['four_a', '*', 4, 'a'], ['H', '+', 'four_a', 3],
    ['a2', '*', 'a', 'a'], ['Delta', '+', 'a2', 'H'],
    ['c2', '*', 'c', 'c'], ['Dc2', '*', 'Delta', 'c2'],
    ['zqm', '*', 'z', 'qm'], ['Nt', '-', 'transport_partial', 'zqm'],
    ['V2', '*', 'V', 'V'], ['y2', '*', 'y', 'y'],
    ['normalized_S', '*', 'i', 'Dc2'], ['normalized_S2', '*', 'normalized_S', 'normalized_S'],
    ['V2minusY2', '-', 'V2', 'y2'], ['aux_product', '*', 'normalized_S2', 'V2minusY2'],
    ['Na', '+', 'aux_product', 'y2'],
    ['scaled_f2', '*', 'Delta', 'f2'], ['scaled_Ns', '-', 'scaled_f2', 'normalized_S2'],
    ['product0', '*', 'N0', 'N1'], ['product1', '*', 'product0', 'Na'],
    ['product3', '*', 'product1', 'Nt'], ['product4', '*', 'product3', 'scaled_Ns'],
    ['polynomial', '-', 'product4', 'Delta'],
]
for row in expected:
    assert by_name[row[0]] == row, row

def dependent(symbol):
    seen = {symbol}
    for name, _, x, y in rows:
        if x in seen or y in seen:
            seen.add(name)
    return [row[0] for row in rows[:60] if row[0] in seen]

y_nodes = dependent('y')
z_nodes = dependent('z')
assert y_nodes == ['y2', 'V2minusY2', 'aux_product', 'Na']
assert z_nodes == ['zqm', 'Nt']
assert not any(name in dependent('i') for name in ['Delta', 'c2', 'Dc2', 'V2'])

# Tiny exact integer polynomial ring.  Monomials are sorted tuples of symbols.
def var(s): return {(s,): 1}
def plus(p, q):
    out = dict(p)
    for m, c in q.items(): out[m] = out.get(m, 0) + c
    return {m: c for m, c in out.items() if c}
def neg(p): return {m: -c for m, c in p.items()}
def sub(p, q): return plus(p, neg(q))
def mul(p, q):
    out = {}
    for a, x in p.items():
        for b, y in q.items():
            k = tuple(sorted(a + b))
            out[k] = out.get(k, 0) + x * y
    return {m: c for m, c in out.items() if c}
one = {(): 1}
N0, N1, Na, Nt, Ns, D, qm, H, S, V, y = map(var, ['N0', 'N1', 'Na', 'Nt', 'Ns', 'D', 'qm', 'H', 'S', 'V', 'y'])
A = sub(Na, one)
product = mul(mul(mul(N0, N1), Na), Ns)
old = sub(mul(mul(product, Nt), D), D)
new_nt = sub(Nt, mul(mul(qm, H), A))
new = sub(mul(mul(product, new_nt), D), D)
assert sub(new, old) == neg(mul(mul(mul(mul(qm, H), A), product), D))
S2, V2, y2 = mul(S, S), mul(V, V), mul(y, y)
aux = plus(mul(S2, sub(V2, y2)), y2)
assert sub(aux, one) == plus(mul(sub(one, S2), y2), sub(mul(S2, V2), one))
assert plus(sub(one, S2), S2) == one
for s, v, yy in itertools.product(range(4), repeat=3):
    n = (yy*yy + s*s*(v*v-yy*yy)) % 4
    assert n != 3
    assert n == ((yy*yy if s % 2 == 0 else v*v) % 4)

report = {
    'source_sha256': {k: v[1] for k, v in paths.items()},
    'rows': len(rows), 'live_gates': len(rows), 'positive_authenticated_ports': sorted(ports), 'operation_counts': dict(sorted(Counter(r[1] for r in rows).items())),
    'preaggregation_y_dependent': y_nodes, 'preaggregation_z_dependent': z_nodes,
    'formal_shear_difference_checked': True, 'formal_auxiliary_expansion_checked': True,
    'mod4_cases_checked': 64,
    'scope': 'Exact ring identity and finite residue check; direct-alias obstruction is a general mathematical proof in README, not a circuit lower bound or Lean theorem.'
}
print(json.dumps(report, sort_keys=True, indent=2))
