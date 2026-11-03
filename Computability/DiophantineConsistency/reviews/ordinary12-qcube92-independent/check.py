#!/usr/bin/env python3
"""Independently check the exact q-cube DAG rewrite and polynomial identity."""
from collections import Counter
from hashlib import sha256
import gzip
import json
from pathlib import Path
import random

D = Path(__file__).resolve().parents[2]
old_file = D / 'research/ordinary12-sum-of-squares-candidate/candidate.json'
new_file = D / 'research/ordinary12-qcube92-candidate/candidate.json'
pins = {
    old_file: 'dc13e87a45a687e99e9bcb1cd3276e7c80d3e014bb7f51074084ca3214ac45ee',
    new_file: '3a21d323adb96788a4b46c0b33800e07f2d1cb708b5c3c53ab709f6e186acee3',
}

def must(ok, text):
    if not ok:
        raise SystemExit(text)

def digest(path):
    return sha256(path.read_bytes()).hexdigest()

for path, value in pins.items():
    must(digest(path) == value, 'input hash mismatch: ' + str(path))
old = json.loads(old_file.read_text())
new = json.loads(new_file.read_text())
must(new['parent_graph_sha256'] == pins[old_file], 'wrong parent pin')
must(new['fixed_numerals'] == old['fixed_numerals'], 'ports changed')
old_witnesses = old['witnesses']
expected_vars = list(old_witnesses)
expected_vars[expected_vars.index('Y')] = 's'
must(new['witnesses'] == expected_vars, 'incorrect quotient witness substitution')
must(new['domain'] == old['domain'] and new['output'] == old['output'], 'domain or output changed')
# Reconstruct every candidate node from the old 94-node list; compare whole DAG.
expected = []
for name, op, a, b in old['source']:
    if name == 'q3':
        expected.extend([[name, op, a, b], ['Y', '*', 'q3', 's']])
    elif name in ('M', 'g34', 'folded_q3Bt'):
        continue
    elif name == 'g32':
        expected.append(['g32', '+', 'folded_g31', 's'])
    elif name == 'g33':
        expected.append(['g33', '*', 'qm', 'g32'])
    elif name == 'Z':
        expected.append(['Z', '-', 'g33', 'Bt'])
    elif name == 'g39':
        expected.append(['g39', '*', 'qm', 'qm'])
    else:
        expected.append([name, op, a, b])
must(new['source'] == expected, 'candidate DAG is not the exact proposed rewrite')

def inventory(graph):
    known = set(graph['witnesses']) | set(graph['fixed_numerals'])
    names = set()
    uses = {}
    for node, op, x, y in graph['source']:
        must(node not in known and node not in names, 'duplicate/redefined node: ' + node)
        must(op in ('+', '-', '*'), 'invalid operation')
        for item in (x, y):
            must(type(item) is int or (isinstance(item, str) and item in known), 'bad topological operand: ' + str(item))
        names.add(node)
        known.add(node)
        uses[node] = (x, y)
    live, stack = set(), [graph['output']]
    while stack:
        node = stack.pop()
        if node in live or node not in uses:
            continue
        live.add(node)
        stack.extend(x for x in uses[node] if isinstance(x, str))
    must(live == names, 'dead gates')
    counts = Counter(row[1] for row in graph['source'])
    must(graph['operations'] == len(live), 'reported operation count mismatch')
    must(graph['operation_breakdown'] == dict(counts), 'operation breakdown mismatch')
    return len(live), dict(counts)

old_stats = inventory(old)
new_stats = inventory(new)
must(old_stats[0] == 94 and new_stats[0] == 92, 'unexpected live operation count')
# Sparse polynomials with variables (Q,b,W,s,B,H). Their integer coefficients
# give an exact identity over every commutative ring; no random testing involved.
N = 6
zero = (0,) * N

def const(n):
    return {} if n == 0 else {zero: n}

def var(i):
    m = list(zero)
    m[i] = 1
    return {tuple(m): 1}

def add(a, b):
    r = dict(a)
    for monomial, coefficient in b.items():
        r[monomial] = r.get(monomial, 0) + coefficient
        if not r[monomial]:
            del r[monomial]
    return r

def neg(a):
    return {m: -c for m, c in a.items()}

def sub(a, b):
    return add(a, neg(b))

def mul(a, b):
    r = {}
    for am, av in a.items():
        for bm, bv in b.items():
            m = tuple(x + y for x, y in zip(am, bm))
            r[m] = r.get(m, 0) + av * bv
    return {m: c for m, c in r.items() if c}

Q, b, W, s, B, H = (var(i) for i in range(N))
Y = mul(Q, s)
M = mul(Q, b)
old_Z = sub(add(mul(M, W), mul(Y, b)), mul(Q, B))
new_Z = sub(mul(b, add(W, s)), B)
must(old_Z == mul(Q, new_Z), 'exact root identity failed')
old_A0 = sub(mul(old_Z, old_Z), mul(mul(M, M), H))
new_A0 = sub(mul(new_Z, new_Z), mul(mul(b, b), H))
must(old_A0 == mul(mul(Q, Q), new_A0), 'exact residual identity failed')

# Independently certify the cancellation used in the degree bound for h.
Q, V, n = (var(i) for i in range(3))
one = const(1)
vplus = add(V, n)
lhs = add(mul(sub(one, Q), mul(vplus, vplus)), sub(mul(Q, mul(V, V)), one))
rhs = sub(sub(mul(vplus, vplus), one), mul(mul(Q, n), add(add(V, V), n)))
must(lhs == rhs, 'exact degree-cancellation identity failed')
lookup = {row[0]: row[1:] for row in new['source']}
shape = {'vn': ['+', 'V', 'n'], 'vn2': ['*', 'vn', 'vn'],
         'polarV2': ['*', 'V', 'V'], 'polarQV2': ['*', 'Q', 'polarV2'],
         'polarCy': ['-', 'polarQV2', 1], 'oneQ': ['-', 1, 'Q'],
         'polarHpart': ['*', 'oneQ', 'vn2'], 'h': ['+', 'polarHpart', 'polarCy']}
must(all(lookup[k] == v for k, v in shape.items()), 'unexpected h source graph')
degrees = {name: 1 for name in new['witnesses']}
degrees.update({name: 0 for name in new['fixed_numerals']})
for name, op, left, right in new['source']:
    x = degrees[left] if isinstance(left, str) else 0
    y = degrees[right] if isinstance(right, str) else 0
    degrees[name] = x + y if op == '*' else max(x, y)
    if name == 'h':
        must((degrees['Q'], degrees['V'], degrees['n']) == (12, 8, 1), 'unexpected h degree premises')
        degrees[name] = max(2 * max(degrees['V'], degrees['n']),
                            degrees['Q'] + degrees['n'] + max(degrees['V'], degrees['n']))
upper_nodes = ['Q', 'V', 'h', 'den', 'polarT', 'polarA', 'polarCorrection', 'N', 'A0', 'A1', 'P12']
upper = {name: degrees[name] for name in upper_nodes}
must(upper == {'Q': 12, 'V': 8, 'h': 21, 'den': 20, 'polarT': 24,
               'polarA': 41, 'polarCorrection': 72, 'N': 82,
               'A0': 22, 'A1': 32, 'P12': 164}, 'unexpected degree bounds')

# Evaluate a univariate substitution modulo a prime using the exact fixed ports.
coefficients = D / 'con-zfc-diophantine-forms/115-synchronized-exponents/supplement/coefficients'
binding_file = coefficients / 'BINDING.json'
binding_hash = 'dd13365e1c68cd244e67a61abfeb5b351c3ad679acb55a73f714d2885341ee01'
must(digest(binding_file) == binding_hash, 'coefficient binding hash mismatch')
binding = json.loads(binding_file.read_text())
prime = 1_000_000_007
values = {name: [0, i + 2] for i, name in enumerate(new['witnesses'])}
payloads = {}
for name in new['fixed_numerals']:
    meta = binding['ports'][name]
    file = coefficients / meta['file']
    data = file.read_bytes()
    must(sha256(data).hexdigest() == meta['sha256_gzip'], 'gzip payload hash mismatch: ' + name)
    raw = gzip.decompress(data)
    must(sha256(raw).hexdigest() == meta['sha256_raw'] and len(raw) == meta['raw_bytes'], 'raw payload mismatch: ' + name)
    values[name] = [int.from_bytes(raw, 'little') % prime]
    payloads[file] = meta['sha256_gzip']

def poly_add(a, b, sign):
    out = [((a[i] if i < len(a) else 0) + sign*(b[i] if i < len(b) else 0)) % prime
           for i in range(max(len(a), len(b)))]
    while len(out) > 1 and not out[-1]:
        out.pop()
    return out

def poly_mul(a, b):
    out = [0] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            out[i+j] = (out[i+j] + x*y) % prime
    while len(out) > 1 and not out[-1]:
        out.pop()
    return out

for name, op, left, right in new['source']:
    x = values[left] if isinstance(left, str) else [left]
    y = values[right] if isinstance(right, str) else [right]
    values[name] = poly_mul(x, y) if op == '*' else poly_add(x, y, 1 if op == '+' else -1)
must(len(values['P12']) - 1 == 164 and values['P12'][-1] == 311486212, 'degree lower witness failed')

# Additional sanity checks evaluate full actual integer DAGs at positive inputs.
def evaluate(graph, initial):
    vals = dict(initial)
    for name, op, a, b in graph['source']:
        a = vals[a] if isinstance(a, str) else a
        b = vals[b] if isinstance(b, str) else b
        vals[name] = {'+': lambda: a+b, '-': lambda: a-b, '*': lambda: a*b}[op]()
    return vals

rng = random.Random(69321)
for _ in range(400):
    inputs = {name: rng.randrange(1, 9) for name in new['witnesses'] + new['fixed_numerals']}
    got = evaluate(new, inputs)
    old_inputs = {name: inputs[name] for name in old['witnesses'] + old['fixed_numerals'] if name != 'Y'}
    old_inputs['Y'] = got['Y']
    parent = evaluate(old, old_inputs)
    must(parent['Z'] == got['q3'] * got['Z'], 'concrete root identity failed')
    must(parent['A0'] == got['q3']**2 * got['A0'], 'concrete residual identity failed')
    must((parent['A1'], parent['N']) == (got['A1'], got['N']), 'other residual changed')
    must((parent['P12'] == 0) == (got['P12'] == 0), 'concrete zero equivalence failed')
for path, value in pins.items():
    must(digest(path) == value, 'input changed during review')
must(digest(binding_file) == binding_hash and all(digest(p) == h for p, h in payloads.items()), 'coefficient inputs changed during review')
print(json.dumps({'old_live_operations': old_stats[0], 'new_live_operations': new_stats[0],
                  'new_breakdown': new_stats[1], 'exact_sparse_polynomial_identities': 3,
                  'tight_degree_upper_bounds': upper, 'prime': prime,
                  'degree_lower_witness': {'degree': len(values['P12'])-1, 'leading_coefficient': values['P12'][-1]},
                  'exact_positive_full_graph_examples': 400}, indent=2))
