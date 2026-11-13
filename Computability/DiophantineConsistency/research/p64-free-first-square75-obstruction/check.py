#!/usr/bin/env python3
"""Exact core and modular controls for the free first-root-square graph."""
import hashlib
import json
import math
from pathlib import Path

if not __debug__:
    raise SystemExit("Optimized Python disables required assertions")

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent.parent
SOURCE = ROOT / 'research/p64-qcube76-independent-y-candidate/graph.json'
EXPECTED = '196ef3bdf6805c7ed7d44c278359e32c0f658634db357cc19f0e87464ed6b11c'
assert hashlib.sha256(SOURCE.read_bytes()).hexdigest() == EXPECTED
original = json.loads(SOURCE.read_text())
rows = original['source']
assert len(rows) == 76
assert [r for r in rows if r[0] == 'first_unscaled_square'] == [
    ['first_unscaled_square', '*', 't', 't']]
assert [r[0] for r in rows if 'first_unscaled_square' in r[2:]] == ['A0']
assert [r for r in rows if 't' in r[2:]] == [
    ['first_unscaled_square', '*', 't', 't']]
candidate = []
for row in rows:
    if row[0] == 'first_unscaled_square':
        continue
    candidate.append([('tFirst' if x == 'first_unscaled_square' else x) for x in row])
assert len(candidate) == 75
candidate_witnesses = [('tFirst' if x == 't' else x) for x in original['witnesses']]
graph = json.loads((HERE / 'graph.json').read_text())
assert graph['source'] == candidate and graph['witnesses'] == candidate_witnesses
assert graph['output'] == original['output'] and graph['operations'] == 75
used = {'polynomial'}
for name, op, left, right in reversed(candidate):
    if name in used:
        used.update(x for x in (left, right) if isinstance(x, str))
assert all(row[0] in used for row in candidate)
assert all(name in used for name in candidate_witnesses)
counts = {op: sum(row[1] == op for row in candidate) for op in ('*', '+', '-')}
assert counts == {'*': 41, '+': 18, '-': 16}

q, X, Y, m = 3, 3, 162, 199
U = Y * Y
a, H, D = (X + 1) * Y, 4 * (X + 1) * Y + 3, ((X + 1) * Y + 1) * ((X + 1) * Y + 3)
P = X * U
def mul(pair, other, d, mod=None):
    x, y = pair
    u, v = other
    z = (x*u + d*y*v, x*v + y*u)
    return z if mod is None else (z[0] % mod, z[1] % mod)
def power(pair, exponent, d, mod=None):
    acc = (1, 0)
    while exponent:
        if exponent & 1:
            acc = mul(acc, pair, d, mod)
        pair = mul(pair, pair, d, mod)
        exponent >>= 1
    return acc
g, c = power((a + 2, 1), m, D)
assert g*g == 1+D*c*c
h, rem = divmod(U*(g-X-a*c), H)
assert rem == 0 and h > 0
lo, hi = c // (Y + 1) + 1, (c - 1) // Y
k = lo + (m + 1 - h - lo) % U
assert lo <= k <= hi
eta, zeta = c - Y*k, (Y+1)*k - c
assert eta > 0 and zeta > 0 and eta + zeta == k
gamma, rem = divmod(h+k-m-1, U)
assert rem == 0 and gamma > 0
T2 = 1 + P*(P+1)*k*k
assert T2 % 5 == 2
assert math.isqrt(T2)**2 != T2
assert 2**m % (H // math.gcd(H, U)) == X % (H // math.gcd(H, U))
assert (2, 2, 159, 0) == (2, 2, m-40, 0)

def evaluate(mod):
    # Strong and auxiliary witnesses are evaluated modulo mod. Exact division
    # is justified by the symbolic proof in README; invertibility is guarded.
    f, L = power((g % mod, c % mod), c, D, mod)
    inv = lambda x: pow(x % mod, -1, mod)
    i = D * L * inv(c*c) % mod
    I = i * c*c % mod
    ax, y = power((I, 1), m, (I*I-1) % mod, mod)
    V = ax * inv(I) % mod
    Q = (c+V) * inv(f*f) % mod
    T = (m+Q) * inv(c) % mod
    env = dict(beta=2, K0=2, MC=159, MF=0, J=1, F=1,
               alpha=1, z=1, f=f, i=i, T=T, s=6, w=1,
               tFirst=T2, eta=eta, zeta=zeta, y=y, gamma=gamma)
    for name, op, left, right in candidate:
        x = env[left] if isinstance(left, str) else left
        y0 = env[right] if isinstance(right, str) else right
        env[name] = {'+': lambda:x+y0, '-': lambda:x-y0,
                     '*': lambda:x*y0}[op]() % mod
    assert [env[x] for x in ('A0', 'M', 'W', 'Na', 'Lt', 'polynomial')] == [1, 0, 0, 1, 0, 0]
    return mod

controls = [evaluate(p) for p in (1000000007, 1000000009)]
print(json.dumps({'status':'PASS_EXACT_CORE_AND_MODULAR_CONTROLS',
    'parent_sha256':EXPECTED, 'operations':len(candidate), 'operation_counts':counts,
    'm':m, 'q':q, 'X':X, 'Y':Y, 'U':U, 'H':H,
    'g_bits':g.bit_length(), 'c_bits':c.bit_length(), 'k_bits':k.bit_length(),
    'T2_mod_5':T2%5, 'gamma_positive':gamma>0,
    'modular_full_graph_controls':controls,
    'scope':'Exact finite core and modular DAG controls; enormous witnesses are symbolic, not expanded or Lean-checked.'}, sort_keys=True))
