#!/usr/bin/env python3
"""Build/check the conditional transport-coordinate 64-gate proposal."""
from collections import Counter
import gzip
import hashlib
import json
from pathlib import Path
import random
import sys

HERE = Path(__file__).resolve().parent
D = HERE.parents[1]
SOURCE = D / 'candidates/one-page-padding-staircase-carrier65-2011/polynomial.json'
PIN = 'f1f7611842896806fa9e70ad102c6a0e7aa11747a650968f1c74cb169f0e253e'
raw = SOURCE.read_bytes()
if hashlib.sha256(raw).hexdigest() != PIN:
    raise RuntimeError('current graph hash changed')
old = json.loads(raw)
rows = [r[:] for r in old['source'] if r[0] != 'C']
if len(rows) != 64:
    raise RuntimeError('expected exactly one removed C gate')
for row in rows:
    if row[0] == 'gap_product':
        if row != ['gap_product', '*', 'qm', 'qF']:
            raise RuntimeError('unexpected gap product')
        row[2] = 'q'
    elif row[0] == 'gap':
        if row != ['gap', '+', 'gap_product', 'alpha']:
            raise RuntimeError('unexpected gap')
        row[1], row[3] = '-', 'C'
witnesses = ['C' if x == 'alpha' else x for x in old['witnesses']]
candidate = {'schema': 'literal_integer_arithmetic_dag_v1',
             'name': 'conditional_Carrier64_transport_coordinates',
             'status': 'conditional: reverse positive-witness guard unproved',
             'source_parent_sha256': PIN, 'witness_domain': 'strictly positive integers',
             'witnesses': witnesses, 'fixed_numerals': old['fixed_numerals'],
             'coefficient_binding_parent': str(SOURCE.relative_to(D)),
             'source': rows, 'output': old['output'],
             'operation_counts': dict(sorted(Counter(r[1] for r in rows).items()))}

def checked_graph(g):
    available = set(g['witnesses'] + g['fixed_numerals'])
    deps = {}
    for n, op, x, y in g['source']:
        if n in available or op not in '+-*' or any(isinstance(a, str) and a not in available for a in (x, y)):
            raise RuntimeError(f'invalid row {n}')
        available.add(n); deps[n] = (x, y)
    live, pending = set(), [g['output']]
    while pending:
        x = pending.pop()
        if x not in live:
            live.add(x)
            if x in deps: pending.extend(deps[x])
    if any(x not in live for x in g['witnesses'] + g['fixed_numerals'] + list(deps)):
        raise RuntimeError('dead input or gate')
checked_graph(candidate)
if candidate['operation_counts'] != {'*': 37, '+': 15, '-': 12}:
    raise RuntimeError('unexpected gate census')

# Exact coefficient arithmetic for q, F, C, proving the local substitution.
Q, F, C = ({(1,0,0): 1}, {(0,1,0): 1}, {(0,0,1): 1})
one = {(0,0,0): 1}
def add(a, b):
    out = Counter(a); out.update(b)
    return {k: v for k, v in out.items() if v}
def neg(a): return {k: -v for k, v in a.items()}
def sub(a, b): return add(a, neg(b))
def mul(a, b):
    out = Counter()
    for x, cx in a.items():
        for y, cy in b.items():
            out[tuple(u + v for u, v in zip(x, y))] += cx * cy
    return {k: v for k, v in out.items() if v}
qf = sub(Q, F)
if add(mul(sub(Q, one), qf), sub(qf, C)) != sub(mul(Q, qf), C):
    raise RuntimeError('exact local substitution failed')

# Symbolic conditional full-zero symmetry, with q,F,C,z,K,w,d,h independent.
def variable8(index):
    exponent = [0]*8; exponent[index] = 1
    return {tuple(exponent): 1}
qq, ff, cc, zz, kk, ww, dd, hh = [variable8(j) for j in range(8)]
one8 = {(0,)*8: 1}
fp = sub(ff, dd); cp = add(cc, mul(qq, dd))
zp = add(add(zz, mul(dd, add(kk, ww))), hh)
old_gap = sub(mul(qq, sub(qq, ff)), cc)
new_gap = sub(mul(qq, sub(qq, fp)), cp)
if old_gap != new_gap:
    raise RuntimeError('conditional symmetry gap mismatch')
def transport_poly(fval, cval, zval):
    return sub(add(mul(add(kk, ww), cval), sub(qq, fval)), mul(zval, sub(qq, one8)))
change = sub(transport_poly(fp, cp, zp), transport_poly(ff, cc, zz))
expected = sub(mul(dd, add(add(kk, ww), one8)), mul(hh, sub(qq, one8)))
if change != expected:
    raise RuntimeError('conditional symmetry transport mismatch')

# Symbolic Pell step, norm preservation and induction on x ≡ 1, k ≡ 2j (mod E).
ee, yy, xh, kh, jj = [variable8(j) for j in range(5)]
two8 = add(one8, one8)
mm = mul(ee, yy); discriminant = mul(mm, add(mm, one8))
root = add(mul(two8, mm), one8)
xx = add(one8, mul(ee, xh)); kval = add(mul(two8, jj), mul(ee, kh))
xp = add(mul(root, xx), mul(mul(two8, discriminant), kval))
kp = add(mul(two8, xx), mul(root, kval))
if sub(mul(xp, xp), mul(discriminant, mul(kp, kp))) != sub(mul(xx, xx), mul(discriminant, mul(kval, kval))):
    raise RuntimeError('Pell norm preservation failed')
if any(exponent[0] == 0 for exponent in sub(xp, one8)) or any(
        exponent[0] == 0 for exponent in sub(kp, mul(two8, add(jj, one8)))):
    raise RuntimeError('Pell induction congruence failed')

# Guarded fixed-port partial assignment: transport, rank and carrier bounds
# hold, but alpha = -1.  The first Pell factor explicitly fails to be +1.
ports = {}
for name, meta in old['coefficient_binding']['ports'].items():
    compressed = (SOURCE.parent / 'coefficients' / meta['file']).read_bytes()
    if hashlib.sha256(compressed).hexdigest() != meta['gzip_sha256']:
        raise RuntimeError('compressed port hash mismatch')
    data = gzip.decompress(compressed)
    if hashlib.sha256(data).hexdigest() != meta['raw_sha256']:
        raise RuntimeError('raw port hash mismatch')
    ports[name] = int.from_bytes(data, 'big')
beta, K, mc, mf = [ports[x] for x in ('beta', 'K0', 'MC', 'MF')]
if not (beta >= 31 and K > 0 and 0 < mc < beta < mf < 2*beta):
    raise RuntimeError('fixed-port box failed')
q = beta + 1; f = s = n = eta = zeta = 1; c = q
w = 1 + (q - 2) * K; z = 2 + q * K
gap = q * (q - f) - c
rank = gap * (q*q - 1) + mc + q*mf
transport = (K + w)*c + (q - f) - z*(q - 1)
Y = s*q**3; E = w*q*Y; k = eta + zeta
tau = E*n + k - rank; ell = E*k*Y
if not (q-f-c == -1 and gap == q*(q-2) and transport == 1 and
        1 < rank < q**4-q**3 < E and tau > k+2 and tau*tau-ell*(ell+k) < 0):
    raise RuntimeError('fixed-port partial obstruction failed')
if not (beta % 2 == 1 and mc % 2 == 0 and q % 2 == 0 and rank % 2 == 0 and E % 2 == 0):
    raise RuntimeError('fixed-port parity obstruction failed')
u, remainder = divmod(gap, q-1)
if not (u == remainder == q-2):
    raise RuntimeError('rank-equal old scalar obstruction failed')

# A different fixed-port scalar assignment has odd rank.  An unevaluated
# Pell power (whose exponent is enormous) then satisfies the first norm and
# carrier by the exact congruence induction above; no full zero is asserted.
if q % 2:
    raise RuntimeError('even q required')
c2 = q + 1
w2 = q//2 + (q-2)*K
z2 = 1 + (q+2)//2 + K*(q+1)
gap2 = q*(q-1)-c2
rank2 = gap2*(q*q-1) + mc + q*mf
transport2 = (K+w2)*c2 + q-1-z2*(q-1)
E2 = w2*q**4
if not (q-1-c2 == -2 and transport2 == 1 and rank2 % 2 == 1 and
        1 < rank2 < q**4-q**3 < E2):
    raise RuntimeError('fixed-port odd-rank scalar obstruction failed')
u2, rem2 = divmod(gap2, q-1)
if not (u2 == q-2 and rem2 == q-3 and (K+w2) % (q-1) == q//2 and q//2 != 2):
    raise RuntimeError('odd-rank fixed-q/w repair obstruction failed')
j2 = (rank2+1)//2
if not (j2 > 0 and (2*j2-rank2-1) % E2 == 0):
    raise RuntimeError('Pell exponent integrality failed')

def evaluate(g, inputs, modulus):
    e = dict(inputs)
    for name, op, a, b in g['source']:
        x = e[a] if isinstance(a, str) else a
        y = e[b] if isinstance(b, str) else b
        e[name] = {'+': lambda: x+y, '-': lambda: x-y, '*': lambda: x*y}[op]() % modulus
    return e[g['output']]
rng = random.Random(0x64c)
for _ in range(200):
    x = {key: rng.randrange(1, 1000) for key in candidate['witnesses']+candidate['fixed_numerals']}
    previous = dict(x); previous['alpha'] = x['beta']*x['J'] + 1 - x['F'] - x['C']
    if evaluate(old, previous, 1000000007) != evaluate(candidate, x, 1000000007):
        raise RuntimeError('full-graph modular substitution mismatch')

data = json.dumps(candidate, sort_keys=True, indent=2) + '\n'
result = {'source_sha256': PIN, 'graph_sha256': hashlib.sha256(data.encode()).hexdigest(),
          'checker_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
          'operation_counts': candidate['operation_counts'], 'witness_count': len(witnesses),
          'gap_identity': 'exact sparse integer polynomial', 'modular_graph_substitution_cases': 200,
          'conditional_zero_symmetry': 'exact gap and transport identities',
          'pell_induction': 'exact symbolic norm and E-divisibility',
          'fixed_port_partial': {'alpha': -1, 'transport': 1, 'rank_window': True,
                                 'carrier_positive': True, 'first_norm_negative': True,
                                 'rank_equal_old_positive_scalars_impossible': True,
                                 'even_rank_and_carrier_scale': True},
          'fixed_port_first_pell_extension': {'alpha': -2, 'transport': 1,
                    'rank_window': True, 'odd_rank': True, 'pell_exponent_integral': True,
                    'rank_and_transport_repair_fixed_q_w_impossible': True,
                    'full_zero_claimed': False},
          'qualification': 'conditional candidate; full-zero reverse positivity not proved'}
out = json.dumps(result, sort_keys=True, indent=2) + '\n'
if sys.argv[1:] == ['--write']:
    (HERE / 'graph.json').write_text(data)
    (HERE / 'result.json').write_text(out)
elif sys.argv[1:] == []:
    if (HERE / 'graph.json').read_text() != data or (HERE / 'result.json').read_text() != out:
        raise RuntimeError('frozen output drift')
    print(out, end='')
else:
    raise SystemExit('usage: check.py [--write]')
