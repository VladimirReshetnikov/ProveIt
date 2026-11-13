#!/usr/bin/env python3
"""Independent descent, graph and degree checks; never invokes Lean."""
from pathlib import Path
from collections import Counter
import gzip
import hashlib
import itertools
import json
import math
import subprocess
import sys

D = Path(__file__).resolve().parents[2]
A = D / 'research/ordinary14-negative-pell75'
P = D / 'research/ordinary14-aux-root78'

def digest(data): return hashlib.sha256(data).hexdigest()
def pinned(path, expected):
    data = path.read_bytes()
    assert digest(data) == expected, str(path)
    return data

new = json.loads(pinned(A / 'candidate.json', '89a9a0217d28d655fbf2592d995f4d766175a45560fa4d33b251dd3711e5b1c1'))
old = json.loads(pinned(P / 'candidate.json', 'd579ba32a40eed91a336b0015086104e1d1a7c6569092f757328769a3128ab43'))
readme = (A / 'README.md').read_bytes()
tail = (b'\nIndependent external review is recorded in\n'
        b'`../../reviews/ordinary14-negative-pell75-independent/`.\n')
assert readme.endswith(tail)
assert digest(readme[:-len(tail)]) == 'be2665b4f5fdc8ff2a8c99475088cd37543d88453e0b4ac00d4faf97606368d7'
assert new['witnesses'] == old['witnesses'] and new['fixed_numerals'] == old['fixed_numerals']
gone={'g41','A0','A0sq','A1sq','Fam','Fam2','Fsm2','sum01','sum23','out','guard2','guarded_out'}
rows = [row for row in old['source'] if row[0] not in gone]
rows += [['F0','-','g38','g40'], ['F1','+',1,'A1'], ['Fs','+',1,'g72'],
         ['Fg','+',1,'guard'], ['P01','*','F0','F1'], ['P012','*','P01','Fa'],
         ['P0123','*','P012','Fs'], ['P01234','*','P0123','Fg'], ['out','-','P01234',1]]
assert rows == new['source'] and len(rows) == 75
known = set(new['witnesses'] + new['fixed_numerals'])
assert len(known) == 18
for name, op, a, b in rows:
    assert name not in known and op in {'+', '-', '*'}
    assert all(isinstance(x, int) or x in known for x in (a, b))
    known.add(name)
live = {new['output']}
for name, _, a, b in reversed(rows):
    if name in live: live.update(x for x in (a, b) if isinstance(x, str))
assert all(row[0] in live for row in rows)
assert set(new['witnesses'] + new['fixed_numerals']) <= live

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
def square(a): return mul(a,a)
m, r, k = map(var, ('m', 'r', 'k'))
two = const(2)
disc = mul(m,add(m,const(1)))
unit = add(mul(two,m),const(1))
rp = add(mul(unit,r),mul(mul(two,disc),k),-1)
kp = add(mul(unit,k),mul(two,r),-1)
norm = add(square(r),mul(disc,square(k)),-1)
assert add(square(unit),mul(const(4),disc),-1) == const(1)
assert add(square(rp),mul(disc,square(kp)),-1) == norm
assert add(square(mul(unit,k)),square(mul(two,r)),-1) == add(square(k),mul(const(4),norm),-1)
assert add(square(mul(unit,r)),square(mul(mul(two,disc),k)),-1) == add(mul(square(unit),norm),mul(disc,square(k)))

for m0 in range(2, 80):
    for k0 in range(1, 1001):
        candidate=m0*(m0+1)*k0*k0-1
        assert math.isqrt(candidate)**2 != candidate
    assert m0*m0 < m0*(m0+1)-1 < (m0+1)**2
assert 1*1-1*2*1*1 == -1
for a,u,c,d in itertools.product(range(4), repeat=4):
    delta=a*a+4*a+3
    assert (1+d*d-u*u*(1+delta*c*c))%4 != 3
for a,f,i,c,y,v in itertools.product(range(4), repeat=6):
    delta=a*a+4*a+3
    q=delta*(f*f-1)
    assert q%4 in {0,1}
    assert (y*y-q*(y*y-v*v))%4 != 3
    assert (1+(i*c*c)**2-q)%4 != 3
for factors in itertools.product((-1,1), repeat=5):
    if all(x != -1 for x in factors[:4]) and math.prod(factors)==1:
        assert factors == (1,1,1,1,1)
assert math.prod((1,1,1,1,-1)) == -1  # The guard factor may itself be −1.

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
assert ports['beta'] > 0

prime = 1000000009
env = {name: [9*i+1, i+2] for i, name in enumerate(new['witnesses'])}
env.update({name: [value % prime] for name, value in ports.items()})
def trim(a):
    while len(a) > 1 and a[-1] == 0: a.pop()
    return a
def plus(a,b,sign):
    return trim([((a[i] if i<len(a) else 0)+sign*(b[i] if i<len(b) else 0))%prime for i in range(max(len(a),len(b)))])
def times(a,b):
    out=[0]*(len(a)+len(b)-1)
    for i,x in enumerate(a):
        for j,y in enumerate(b): out[i+j]=(out[i+j]+x*y)%prime
    return trim(out)
def value(x): return [x%prime] if isinstance(x,int) else env[x]
for name,op,a,b in rows:
    env[name]=times(value(a),value(b)) if op=='*' else plus(value(a),value(b),1 if op=='+' else -1)
ray = env[new['output']]
assert len(ray)-1 == 107 and ray[-1] != 0

run = subprocess.run([sys.executable,'-I','-S','-B',str(A/'check.py')],cwd=D,
                     stdout=subprocess.PIPE,stderr=subprocess.PIPE,timeout=120,check=True)
assert not run.stderr and run.stdout == (A/'result.json').read_bytes()
print(json.dumps({'scope':'external standard-integer review; no Lean/PDF theorem',
                  'operations':len(rows),'counts':dict(Counter(row[1] for row in rows)),
                  'all_live':True,'formal_descent_identities':True,
                  'negative_pell_m2_to_79_k1_to_1000_controls':True,
                  'unrestricted_guard_factor':True,'prime':prime,
                  'weighted_ray_degree':len(ray)-1,'weighted_ray_leader':ray[-1],
                  'author_readme_prelink_sha256':digest(readme[:-len(tail)])},sort_keys=True,indent=2))
