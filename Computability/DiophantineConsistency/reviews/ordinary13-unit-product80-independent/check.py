#!/usr/bin/env python3
"""Independent product-factor review; never invokes Lean."""
from pathlib import Path
from collections import Counter
import gzip
import hashlib
import itertools
import json
import subprocess
import sys

D = Path(__file__).resolve().parents[2]
A = D / 'research/ordinary13-unit-product80'
P = D / 'research/ordinary13-residue-first81'

def digest(data): return hashlib.sha256(data).hexdigest()
def pinned(path, expected):
    data = path.read_bytes()
    assert digest(data) == expected, str(path)
    return data

new = json.loads(pinned(A / 'candidate.json', '449adf0f03f08cbb73b4ca8c823cb88b79111243c93705b5404f89d18568a22b'))
old = json.loads(pinned(P / 'candidate.json', '067d3cf0e92961d272e9018dde38bbe8b00ad55ec8e9145fbdd34c0f13e18352'))
pinned(A / 'check.py', 'c2ee0397a4b148d246b36425d19e0e1bd2b31333f68297c6743ac73f88411f85')
readme = (A / 'README.md').read_bytes()
tail = (b'\nIndependent external review is recorded in\n'
        b'`../../reviews/ordinary13-unit-product80-independent/`.\n')
assert readme.endswith(tail)
assert digest(readme[:-len(tail)]) == 'a60ef03d2d252e91b7fe3c622301ee252f7ca5b150f0fc3de3653cb89945afc2'
assert new['witnesses'] == old['witnesses'] and new['fixed_numerals'] == old['fixed_numerals']
gone = {'A0sq','A1sq','Fam','Fam2','Fsm2','sum01','sum23','out'}
rows = [row for row in old['source'] if row[0] not in gone]
rows += [['F0','+',1,'A0'], ['F1','+',1,'A1'], ['Fs','+',1,'g72'],
         ['P01','*','F0','F1'], ['P012','*','P01','Fa'],
         ['P0123','*','P012','Fs'], ['out','-','P0123',1]]
assert rows == new['source'] and len(rows) == 80
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

parity_cases = [0, 0]
for b, x, s, k, z in itertools.product(range(4), repeat=5):
    q = b+1
    y = q**3*s
    ell = x*y*y*k
    factor = 1+z*z-b*b*(1+ell*(ell+k))
    assert factor % 4 != 3
    if b % 2: assert y % 8 == 0 and ell % 4 == 0 and factor % 4 == z*z % 4
    else: assert factor % 4 == (1+z*z) % 4
    parity_cases[b % 2] += 1
for a, u, c, d in itertools.product(range(4), repeat=4):
    delta = a*a+4*a+3
    assert delta % 4 in {0, 3}
    assert (u*u*(1+delta*c*c)) % 4 in {0, 1}
    assert (1+d*d-u*u*(1+delta*c*c)) % 4 != 3
for a, f, i, c, y, v in itertools.product(range(4), repeat=6):
    delta = a*a+4*a+3
    q = delta*(f*f-1)
    ii = i*c*c
    assert q % 4 in {0, 1}
    assert (y*y-q*(y*y-v*v)) % 4 != 3
    assert (1+ii*ii-q) % 4 != 3
assert parity_cases == [512, 512]

# Exact first-residual cancellation in Z[b,ell,delta,k].
def const(n): return {(): n} if n else {}
def var(name): return {(name,): 1}
def add(a, b, sign=1):
    out = dict(a)
    for key, val in b.items(): out[key] = out.get(key, 0) + sign*val
    return {key: val for key, val in out.items() if val}
def mul(a, b):
    out = {}
    for ka, va in a.items():
        for kb, vb in b.items():
            key = tuple(sorted(ka + kb))
            out[key] = out.get(key, 0) + va*vb
    return {key: val for key, val in out.items() if val}
b, ell, delta, k = map(var, ('b', 'ell', 'delta', 'k'))
be = mul(b, ell)
lhs = add(mul(add(be, delta), add(be, delta)),
          mul(mul(b,b), add(const(1), mul(ell, add(ell,k)))), -1)
rhs = add(add(mul(const(2), mul(be, delta)), mul(delta,delta)),
          mul(mul(b,b), add(const(1), mul(ell,k))), -1)
assert lhs == rhs

base = D / 'con-zfc-diophantine-forms/72-congruence-sextic/positive13'
bind72 = json.loads(pinned(base / 'ACTIVE_BINDING.json', '6927456a832f956244d4816c20aa96ff0212cb05173f73a11c55e0d8ddc87fbf'))
bind115 = json.loads(pinned(D / 'con-zfc-diophantine-forms/115-synchronized-exponents/supplement/coefficients/BINDING.json', 'dd13365e1c68cd244e67a61abfeb5b351c3ad679acb55a73f714d2885341ee01'))
ports = {}
for name, info in bind72['ports'].items():
    assert all(bind115['ports'][name][key] == info[key] for key in ('sha256_raw','sha256_gzip'))
    compressed = (base / info['path']).read_bytes()
    assert digest(compressed) == info['sha256_gzip']
    raw = gzip.decompress(compressed)
    assert len(raw) == info['raw_bytes'] and digest(raw) == info['sha256_raw']
    ports[name] = int.from_bytes(raw, 'little')

prime = 1000000009
env = {name: [7*i+1, i+2] for i, name in enumerate(new['witnesses'])}
env.update({name: [value % prime] for name, value in ports.items()})
def trim(a):
    while len(a) > 1 and a[-1] == 0: a.pop()
    return a
def plus(a, b, sign):
    return trim([((a[i] if i < len(a) else 0) + sign*(b[i] if i < len(b) else 0)) % prime for i in range(max(len(a), len(b)))])
def times(a, b):
    out = [0] * (len(a)+len(b)-1)
    for i, x in enumerate(a):
        for j, y in enumerate(b): out[i+j] = (out[i+j] + x*y) % prime
    return trim(out)
def value(x): return [x % prime] if isinstance(x, int) else env[x]
for name, op, a, b in rows:
    env[name] = times(value(a), value(b)) if op == '*' else plus(value(a), value(b), 1 if op == '+' else -1)
ray = env[new['output']]
assert len(ray)-1 == 99 and ray[-1] != 0

run = subprocess.run([sys.executable, '-I', '-S', '-B', str(A / 'check.py')],
                     cwd=D, stdout=subprocess.PIPE, stderr=subprocess.PIPE, timeout=120, check=True)
assert not run.stderr and run.stdout == (A / 'result.json').read_bytes()
print(json.dumps({'scope': 'external source and arithmetic review; no Lean/PDF theorem',
                  'operations': len(rows), 'counts': dict(Counter(row[1] for row in rows)),
                  'all_live': True, 'first_residual_formal_identity': True,
                  'even_odd_b_controls': parity_cases,
                  'prime': prime, 'weighted_ray_degree': len(ray)-1, 'weighted_ray_leader': ray[-1],
                  'author_readme_prelink_sha256': digest(readme[:-len(tail)])}, sort_keys=True, indent=2))
