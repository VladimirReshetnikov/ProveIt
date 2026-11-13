#!/usr/bin/env python3
"""Independent bounded audit of the shifted-Pell candidate; no Lean claims."""
import gzip
import hashlib
import json
import math
from pathlib import Path

D = Path(__file__).resolve().parents[2]

def sha(data):
    return hashlib.sha256(data).hexdigest()

def read_json(path, expected):
    data = path.read_bytes()
    assert sha(data) == expected
    return json.loads(data)

p = read_json(D / 'research/ordinary14-positive-guard74/candidate.json',
              'e70af4f896013695368180743f514c027faa86f8b3cedd5479b22e64e4c26093')
c = read_json(D / 'research/ordinary14-shifted-pell75/candidate.json',
              'cf9c2af177038c65618f351e0112c9adb21ac3726af7c83e52f7dac4224b52be')
old = {r[0]: r[1:] for r in p['source']}
new = {r[0]: r[1:] for r in c['source']}
assert len(old) == 74 and len(new) == 75
removed = {'g30', 'g38', 'g40', 'F0'}
added = {'t2', 'two_t', 'difference', 'ell_product', 'F0'}
assert set(old) - removed == set(new) - added
assert all(old[n] == new[n] for n in set(old) - removed)
assert {n: old[n] for n in removed} == {
    'g30': ['+', 'ell', 'k'], 'g38': ['*', 'r', 'r'],
    'g40': ['*', 'ell', 'g30'], 'F0': ['-', 'g38', 'g40']}
assert {n: new[n] for n in added} == {
    't2': ['*', 't', 't'], 'two_t': ['*', 2, 't'],
    'difference': ['-', 'two_t', 'k'], 'ell_product': ['*', 'ell', 'difference'],
    'F0': ['+', 't2', 'ell_product']}
assert p['domain'] == c['domain'] == 'strictly positive integers'
assert c['witnesses'] == ['t' if x == 'r' else x for x in p['witnesses']]
assert p['fixed_numerals'] == c['fixed_numerals'] and len(c['witnesses']) == 14

# Independently check topology, all-node liveness, and that r occurs nowhere
# outside the replaced parent nodes. This establishes output equality after
# r = ell + t once the elementary square identity is checked below.
deps = {x: {x} for x in c['witnesses'] + c['fixed_numerals']}
degrees = {x: 1 for x in c['witnesses']}
degrees.update({x: 0 for x in c['fixed_numerals']})
for n, op, x, y in c['source']:
    assert n not in deps and op in ('+', '-', '*')
    assert all(isinstance(z, int) or z in deps for z in (x, y))
    deps[n] = set().union(*(deps[z] for z in (x, y) if isinstance(z, str)))
    d = [0 if isinstance(z, int) else degrees[z] for z in (x, y)]
    degrees[n] = sum(d) if op == '*' else max(d)
    if n == 'A1':
        # The separately checked exact identity below proves this sharper bound.
        degrees[n] = 30
live = {'out'}
for n, op, x, y in reversed(c['source']):
    if n in live:
        live.update(z for z in (x, y) if isinstance(z, str))
assert all(n in live for n, *_ in c['source'])
assert set(c['witnesses'] + c['fixed_numerals']) <= live
assert all('r' not in (x, y) for n, _, x, y in p['source'] if n not in removed)
assert 't' not in deps['ell'] and 't' not in deps['k']
assert [degrees[n] for n in ('F0', 'F1', 'Fa', 'Fs', 'guard', 'out')] == [12, 30, 30, 22, 3, 97]

# Sparse formal integer-polynomial arithmetic checks both identities without
# numerical sampling or reliance on a computer-algebra package.
def const(n): return {(): n} if n else {}
def var(s): return {(s,): 1}
def add(a, b):
    r = dict(a)
    for m, v in b.items(): r[m] = r.get(m, 0) + v
    return {m: v for m, v in r.items() if v}
def neg(a): return {m: -v for m, v in a.items()}
def sub(a, b): return add(a, neg(b))
def mul(a, b):
    r = {}
    for x, vx in a.items():
        for y, vy in b.items():
            key = tuple(sorted(x+y))
            r[key] = r.get(key, 0) + vx*vy
    return {m: v for m, v in r.items() if v}
def sq(a): return mul(a, a)

ell, k, t = map(var, ('ell', 'k', 't'))
assert sub(sq(add(ell,t)), mul(ell,add(ell,k))) == add(sq(t),mul(ell,sub(mul(const(2),t),k)))
U, X, a, cc, H, s = map(var, ('U', 'X', 'a', 'c', 'H', 's'))
b0 = add(X, mul(a, cc))
actual = sub(sq(add(mul(U,b0),mul(H,s))),mul(sq(U),add(const(1),mul(add(sq(a),H),sq(cc)))))
inner = sub(sub(add(sq(X),mul(const(2),mul(X,mul(a,cc)))),mul(H,sq(cc))),const(1))
expanded = add(add(mul(sq(U),inner),mul(const(2),mul(mul(mul(U,b0),H),s))),mul(sq(H),sq(s)))
assert actual == expanded
shape = {'g15':['*',4,'a'], 'H':['+',3,'g15'], 'g17':['*','a','a'],
         'Delta':['+','H','g17'], 'g19':['*','a','c'], 'b0':['+','X','g19'],
         'g58':['*','U','b0'], 'g59':['*','H','shift'],
         'Dstar':['+','g58','g59'], 'g61':['*','Dstar','Dstar'],
         'g62':['*','U','U'], 'g63':['*','Delta','c2'], 'c2':['*','c','c'],
         'g64':['+',1,'g63'], 'g65':['*','g62','g64'], 'A1':['-','g61','g65']}
assert {n:new[n] for n in shape} == shape
for n in ('a','c','U','H','b0','shift'):
    assert degrees[n] <= {'a':6,'c':5,'U':6,'H':6,'b0':11,'shift':7}[n]
assert max(2*6+max(2*2,2+6+5,6+2*5,0),6+11+6+7,2*6+2*7) == 30

# Authenticate the fixed bytes and use finite differences, independently of
# the candidate's coefficient-propagation implementation, for the degree-97
# ray lower bound. The sharper A1 identity above gives the matching upper bound.
root = D / 'con-zfc-diophantine-forms/72-congruence-sextic/positive13'
binding = read_json(root / 'ACTIVE_BINDING.json', '6927456a832f956244d4816c20aa96ff0212cb05173f73a11c55e0d8ddc87fbf')
sync = read_json(D / 'con-zfc-diophantine-forms/115-synchronized-exponents/supplement/coefficients/BINDING.json',
                 'dd13365e1c68cd244e67a61abfeb5b351c3ad679acb55a73f714d2885341ee01')
ports = {}
for name, meta in binding['ports'].items():
    assert sync['ports'][name]['sha256_gzip'] == meta['sha256_gzip']
    assert sync['ports'][name]['sha256_raw'] == meta['sha256_raw']
    data = (root / meta['path']).read_bytes()
    assert sha(data) == meta['sha256_gzip']
    raw = gzip.decompress(data)
    assert len(raw) == meta['raw_bytes'] and sha(raw) == meta['sha256_raw']
    ports[name] = int.from_bytes(raw, 'little')
assert set(ports) == set(c['fixed_numerals']) and ports['beta'] > 0 and ports['K0'] >= 0
prime = 1000000007
def evaluate(x):
    e = {v:x for v in c['witnesses']}
    e['t'] = 2*x
    e.update({n:v % prime for n,v in ports.items()})
    def v(z): return z if isinstance(z,int) else e[z]
    for n, op, a, b in c['source']:
        a,b = v(a),v(b)
        e[n] = (a*b if op == '*' else a+b if op == '+' else a-b) % prime
    return e['out']
row = [evaluate(x) for x in range(98)]
for _ in range(97): row = [(y-x) % prime for x,y in zip(row,row[1:])]
leader = row[0] * pow(math.factorial(97), -1, prime) % prime
assert leader == 979034495
print(json.dumps({'external_scope':'positive-zero bijection and specialized degree; no Lean, iPRA or PDF binding',
                  'parent_gates':74, 'candidate_gates':75, 'witnesses':14,
                  'identity_checks':['Pell shift','F1 degree cancellation'],
                  'degree_upper':97, 'ray_degree':97, 'ray_leader':leader,
                  'prime':prime, 'ray_method':'97th finite difference'}, indent=2, sort_keys=True))
