#!/usr/bin/env python3
"""Independent graph and signed-identity review; never invokes Lean."""
from pathlib import Path
from collections import Counter
import gzip
import hashlib
import json
import subprocess
import sys

D = Path(__file__).resolve().parents[2]
A = D / 'research/ordinary13-residue-first82'
P = D / 'research/ordinary13-qcube-unscale84'
Q = D / 'research/ordinary14-shifted-guard87-calibration'

def digest(data): return hashlib.sha256(data).hexdigest()
def pinned(path, expected):
    data = path.read_bytes()
    assert digest(data) == expected, str(path)
    return data

new = json.loads(pinned(A / 'candidate.json', 'bb90faa3815c5ff46f5fdbf41c2d001790d565baa17d97c79514c33fa928f1d2'))
old = json.loads(pinned(P / 'candidate.json', '2293d98affce104dc1522ddd69a0cf904ee752034dbd8959f4d3f41a3c604a77'))
readme = (A / 'README.md').read_bytes()
tail = (b'\nIndependent external review is recorded in\n'
        b'`../../reviews/ordinary13-residue-first82-independent/`.\n')
assert readme.endswith(tail)
assert digest(readme[:-len(tail)]) == '867ba1550c562883caf3377ee20b705a061eef5e76ae03b4f012b4817b988e0d'
assert new['witnesses'] == old['witnesses'] and new['fixed_numerals'] == old['fixed_numerals']
rows = []
for row in old['source']:
    name = row[0]
    if name in {'g25', 'g28'}: continue
    if name == 'g26': rows.append(['g26', '+', 'X', 'K0'])
    elif name == 'Bt': rows.append(['Bt', '-', 'g27', 'F'])
    else: rows.append(row)
assert rows == new['source'] and len(rows) == 82
known = set(new['witnesses'] + new['fixed_numerals'])
assert len(known) == 17
for name, op, a, b in rows:
    assert name not in known and op in {'+', '-', '*'}
    assert all(isinstance(x, int) or x in known for x in (a, b))
    known.add(name)
live = {new['output']}
for name, _, a, b in reversed(rows):
    if name in live: live.update(x for x in (a, b) if isinstance(x, str))
assert all(row[0] in live for row in rows)
assert set(new['witnesses'] + new['fixed_numerals']) <= live

# Exact signed transport and carrier identities in Z[b,C,X,K,F,k,ell,r].
def const(n): return {(): n} if n else {}
def var(name): return {(name,): 1}
def add(a, b, sign=1):
    z = dict(a)
    for key, val in b.items(): z[key] = z.get(key, 0) + sign*val
    return {key: val for key, val in z.items() if val}
def mul(a, b):
    z = {}
    for ka, va in a.items():
        for kb, vb in b.items():
            key = tuple(sorted(ka + kb))
            z[key] = z.get(key, 0) + va*vb
    return {key: val for key, val in z.items() if val}
b, c, x, kk, f, k, ell, r = map(var, ('b', 'C', 'X', 'K', 'F', 'k', 'ell', 'r'))
q = add(b, const(1))
old_b = add(mul(c, add(x, mul(kk, q))), mul(f, q), -1)
new_b = add(mul(c, add(x, kk)), f, -1)
shift = add(mul(c, kk), f, -1)
assert old_b == add(new_b, mul(b, shift))
old_r = add(r, mul(add(mul(k, b), const(1)), shift))
old_z = add(mul(b, add(add(ell, k), add(old_r, mul(k, old_b), -1))), old_b, -1)
new_z = add(mul(b, add(add(ell, k), add(r, mul(k, new_b), -1))), new_b, -1)
assert old_z == new_z

pinned(Q / 'README.md', '005fd2c04cef4c997383bf373cc48acd326e829eb01ff4d30c218dadaf9f758a')
base = D / 'con-zfc-diophantine-forms/72-congruence-sextic/positive13'
bind72 = json.loads(pinned(base / 'ACTIVE_BINDING.json', '6927456a832f956244d4816c20aa96ff0212cb05173f73a11c55e0d8ddc87fbf'))
bind115 = json.loads(pinned(D / 'con-zfc-diophantine-forms/115-synchronized-exponents/supplement/coefficients/BINDING.json', 'dd13365e1c68cd244e67a61abfeb5b351c3ad679acb55a73f714d2885341ee01'))
ports = {}
for name, info in bind72['ports'].items():
    assert all(bind115['ports'][name][key] == info[key] for key in ('sha256_raw', 'sha256_gzip'))
    compressed = (base / info['path']).read_bytes()
    assert digest(compressed) == info['sha256_gzip']
    raw = gzip.decompress(compressed)
    assert len(raw) == info['raw_bytes'] and digest(raw) == info['sha256_raw']
    ports[name] = int.from_bytes(raw, 'little')
assert ports['beta'] >= 46 and ports['K0'] >= 0
assert 0 < ports['MC'] < ports['beta'] and 0 < ports['MF'] < 2*ports['beta']

prime = 1000000009
env = {name: [5*i+1, i+2] for i, name in enumerate(new['witnesses'])}
env.update({name: [value % prime] for name, value in ports.items()})
def trim(a):
    while len(a) > 1 and a[-1] == 0: a.pop()
    return a
def plus(a, b, sign):
    return trim([((a[i] if i < len(a) else 0) + sign*(b[i] if i < len(b) else 0)) % prime for i in range(max(len(a), len(b)))])
def times(a, b):
    z = [0] * (len(a)+len(b)-1)
    for i, x in enumerate(a):
        for j, y in enumerate(b): z[i+j] = (z[i+j] + x*y) % prime
    return trim(z)
def value(x): return [x % prime] if isinstance(x, int) else env[x]
for name, op, a, b in rows:
    env[name] = times(value(a), value(b)) if op == '*' else plus(value(a), value(b), 1 if op == '+' else -1)
ray = env[new['output']]
assert len(ray)-1 == 56 and ray[-1] != 0

for packet in (A, Q):
    run = subprocess.run([sys.executable, '-I', '-S', '-B', str(packet / 'check.py')],
                         cwd=D, stdout=subprocess.PIPE, stderr=subprocess.PIPE, timeout=120, check=True)
    assert not run.stderr and run.stdout == (packet / 'result.json').read_bytes()
print(json.dumps({'scope': 'external source and arithmetic review; no Lean/PDF theorem',
                  'operations': len(rows), 'counts': dict(Counter(row[1] for row in rows)),
                  'all_live': True, 'formal_transport_and_carrier_identities': True,
                  'source_calibration_receipt_replayed': True,
                  'prime': prime, 'weighted_ray_degree': len(ray)-1, 'weighted_ray_leader': ray[-1],
                  'author_readme_prelink_sha256': digest(readme[:-len(tail)])}, sort_keys=True, indent=2))
