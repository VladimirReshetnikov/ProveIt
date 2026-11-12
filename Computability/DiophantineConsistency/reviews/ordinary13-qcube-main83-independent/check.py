#!/usr/bin/env python3
"""Independent graph, source and degree checks; no Lean invocation."""
from pathlib import Path
from collections import Counter
import gzip
import hashlib
import json
import subprocess
import sys

D = Path(__file__).resolve().parents[2]
A = D / 'research/ordinary13-qcube-main83'
P = D / 'research/ordinary13-qcube-unscale84'

def digest(data): return hashlib.sha256(data).hexdigest()
def pinned(path, expected):
    data = path.read_bytes()
    assert digest(data) == expected, str(path)
    return data

new = json.loads(pinned(A / 'candidate.json', 'd19de596305c838c4b58f011a7fd233fedc4f7a7a87923cca60d00f46b408789'))
old = json.loads(pinned(P / 'candidate.json', '2293d98affce104dc1522ddd69a0cf904ee752034dbd8959f4d3f41a3c604a77'))
readme = (A / 'README.md').read_bytes()
tail = (b'\nIndependent external review is recorded in\n'
        b'`../../reviews/ordinary13-qcube-main83-independent/`.\n')
assert readme.endswith(tail)
assert digest(readme[:-len(tail)]) == '689041a04799cc745b6d88ee06499045d4a39dcb6ef5ec273dd4775962d6e1ef'
assert new['witnesses'] == ['w' if x == 'X' else x for x in old['witnesses']]
assert new['fixed_numerals'] == old['fixed_numerals']
rows = []
for row in old['source']:
    name = row[0]
    if name in {'g55', 'g56'}: continue
    if name == 'q': rows.extend([row, ['X', '*', 'q', 'w']])
    elif name == 'shift': rows.append(['shift', '-', 'g54', 'r0'])
    else: rows.append(row)
assert rows == new['source'] and len(rows) == 83
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

# Exact identity after U=Yq², X=qw and gamma_old=gamma_prime−w.
def var(name): return {(name,): 1}
def add(a, b, sign=1):
    z = dict(a)
    for key, value in b.items(): z[key] = z.get(key, 0) + sign*value
    return {key: value for key, value in z.items() if value}
def mul(a, b):
    z = {}
    for ka, va in a.items():
        for kb, vb in b.items():
            key = tuple(sorted(ka + kb))
            z[key] = z.get(key, 0) + va*vb
    return {key: value for key, value in z.items() if value}
q, y, w, gamma, r0 = map(var, ('q', 'Y', 'w', 'gamma', 'r0'))
u = mul(y, mul(q, q))
e = mul(mul(q, w), y)
old_shift = add(add(mul(u, add(gamma, w, -1)), mul(e, q)), r0, -1)
new_shift = add(mul(u, gamma), r0, -1)
assert old_shift == new_shift

files = {
    'Compact44/P72Exact.lean': 'a07730d92aefd39d86083d037f4772bacd7741788e2fff1f7669d33fa0ad05d3',
    'Compact44/P72Power.lean': 'f46584fb3977ae5fc33b31bee18e8c27435d97bea10138f163af2de5ee66d462',
    'Compact44/FreeJ13Halt.lean': '18b17a1c81e6ff58d74fd6a7160948b75c71203ee8f5c3bd29e4d3fc9a76218a',
    'Compact44/FreeJPowerFinish.lean': 'e4b2e84586b6232b9accc7775f094d4e1047453f1e8337f6241d39a6657d8816',
    'Compact44/FreeJPowerProjection.lean': 'fee95da196452c374b5d6aeaf2b3bb330e8d690224ad8dab523760df79da2749',
}
sources = {name: pinned(D / 'Lean/DiophantineConsistency' / name, sha).decode() for name, sha in files.items()}
assert 'theorem indices_ordinary' in sources['Compact44/P72Exact.lean']
assert '(hRμ : R + 1 < μ)' in sources['Compact44/P72Exact.lean']
assert 'theorem power_of_mod' in sources['Compact44/P72Power.lean']
assert '![v 0, v 1, v 2, t, v 5, v 6, v 7, v 8, v 9, v 10, v 4 + v 11, v 12]' in sources['Compact44/FreeJ13Halt.lean']
assert 'theorem graph_power' in sources['Compact44/FreeJPowerFinish.lean']
assert 'theorem graph_projection' in sources['Compact44/FreeJPowerProjection.lean']

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
B = 590069
assert ports['beta'] == 2**B - 1 and ports['K0'] >= 0
assert ports['beta'] >= 46 and 0 < ports['MC'] < ports['beta'] and 0 < ports['MF'] < 2*ports['beta']
for bits in range(4, 15):
    beta = 2**bits - 1
    for j in range(3*bits):
        assert (3*pow(2, j, beta)) % beta != 1

prime = 1000000009
env = {name: [3*i+1, i+2] for i, name in enumerate(new['witnesses'])}
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
assert len(ray)-1 == 60 and ray[-1] != 0

run = subprocess.run([sys.executable, '-I', '-S', '-B', str(A / 'check.py')],
                     cwd=D, stdout=subprocess.PIPE, stderr=subprocess.PIPE, timeout=120, check=True)
assert not run.stderr and run.stdout == (A / 'result.json').read_bytes()
print(json.dumps({'scope': 'external source and arithmetic review; no Lean/PDF theorem',
                  'operations': len(rows), 'counts': dict(Counter(row[1] for row in rows)),
                  'all_live': True, 'formal_carrier_identity': True, 'source_statements_pinned': True,
                  'prime': prime, 'weighted_ray_degree': len(ray)-1, 'weighted_ray_leader': ray[-1],
                  'author_readme_prelink_sha256': digest(readme[:-len(tail)])}, sort_keys=True, indent=2))
