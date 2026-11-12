#!/usr/bin/env python3
"""Independent source/port/ray review; never invokes Lean."""
from pathlib import Path
from collections import Counter
import gzip
import hashlib
import json
import subprocess
import sys

D = Path(__file__).resolve().parents[2]
A = D / 'research/ordinary13-qcube-unscale84'
P = D / 'research/ordinary13-aux-root87-36'

def digest(data):
    return hashlib.sha256(data).hexdigest()

def pinned(path, expected):
    data = path.read_bytes()
    assert digest(data) == expected, str(path)
    return data

new = json.loads(pinned(A / 'candidate.json', '2293d98affce104dc1522ddd69a0cf904ee752034dbd8959f4d3f41a3c604a77'))
old = json.loads(pinned(P / 'candidate.json', 'abdd93cebd85dc2194478a76297d16ea04ca06855265420abf0b6c1b7e70db51'))
readme = (A / 'README.md').read_bytes()
tail = (b'\nIndependent external review is recorded in\n'
        b'`../../reviews/ordinary13-qcube-unscale84-independent/`.\n')
assert readme.endswith(tail)
assert digest(readme[:-len(tail)]) == 'cad7b6da824a7d5870bc00e1adb2c426d600863c63bb85d33fc0ab9afac9da67'
assert new['witnesses'] == ['s' if x == 'Y' else x for x in old['witnesses']]
assert new['fixed_numerals'] == old['fixed_numerals']

rows = []
for row in old['source']:
    name = row[0]
    if name in {'M', 'g33', 'g34', 'folded_q3Bt'}:
        continue
    if name == 'q3':
        rows += [row, ['Y', '*', 'q3', 's']]
    elif name == 'g32':
        rows.append(['g32', '*', 'qm', 'folded_g31'])
    elif name == 'Z':
        rows.append(['Z', '-', 'g32', 'Bt'])
    elif name == 'g39':
        rows.append(['g39', '*', 'qm', 'qm'])
    else:
        rows.append(row)
assert rows == new['source'] and len(rows) == 84
known = set(new['witnesses'] + new['fixed_numerals'])
assert len(known) == 17
for name, op, a, b in rows:
    assert name not in known and op in {'+', '-', '*'}
    assert all(isinstance(x, int) or x in known for x in (a, b))
    known.add(name)
live = {new['output']}
for name, _, a, b in reversed(rows):
    if name in live:
        live.update(x for x in (a, b) if isinstance(x, str))
assert all(row[0] in live for row in rows)
assert set(new['witnesses'] + new['fixed_numerals']) <= live

# Exact unscaling identity in Z[ell,k,r,s,Bt,b,q3]; no sampled substitution.
def const(n): return {(): n} if n else {}
def var(name): return {(name,): 1}
def add(a, b, sign=1):
    z = dict(a)
    for key, value in b.items(): z[key] = z.get(key, 0) + sign * value
    return {key: value for key, value in z.items() if value}
def mul(a, b):
    z = {}
    for ka, va in a.items():
        for kb, vb in b.items():
            key = tuple(sorted(ka + kb))
            z[key] = z.get(key, 0) + va * vb
    return {key: value for key, value in z.items() if value}
ell, k, r, s, bt, b, q3 = map(var, ('ell', 'k', 'r', 's', 'bt', 'b', 'q3'))
ellk = add(ell, k)
core = add(add(ellk, r), mul(k, bt), -1)
new_z = add(mul(b, core), bt, -1)
old_core = add(core, s, -1)
old_z = add(add(mul(mul(q3, b), old_core), mul(mul(q3, s), b)), mul(q3, bt), -1)
assert old_z == mul(q3, new_z)
norm = add(const(1), mul(ell, ellk))
old_res = add(mul(old_z, old_z), mul(mul(mul(q3, b), mul(q3, b)), norm), -1)
new_res = add(mul(new_z, new_z), mul(mul(b, b), norm), -1)
assert old_res == mul(mul(q3, q3), new_res)

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
assert ports['beta'] > 0

prime = 1000000009
env = {name: [2*i+1, i+2] for i, name in enumerate(new['witnesses'])}
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

run = subprocess.run([sys.executable, '-I', '-S', '-B', str(A / 'check.py')],
                     cwd=D, stdout=subprocess.PIPE, stderr=subprocess.PIPE, timeout=120, check=True)
assert not run.stderr and run.stdout == (A / 'result.json').read_bytes()
print(json.dumps({'scope': 'external source and arithmetic review; no Lean/PDF theorem',
                  'operations': len(rows), 'counts': dict(Counter(row[1] for row in rows)),
                  'all_live': True, 'formal_cut_identity': True, 'beta_positive': True,
                  'prime': prime, 'weighted_ray_degree': len(ray)-1, 'weighted_ray_leader': ray[-1],
                  'author_readme_prelink_sha256': digest(readme[:-len(tail)])}, sort_keys=True, indent=2))
