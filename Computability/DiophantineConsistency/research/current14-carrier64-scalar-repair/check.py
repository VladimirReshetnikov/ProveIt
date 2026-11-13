#!/usr/bin/env python3
"""Exhaustively test the explicit restricted scalar-repair criterion."""
import gzip
import hashlib
import json
from pathlib import Path
from collections import Counter

HERE = Path(__file__).resolve().parent
D = HERE.parents[1]
SOURCE = D / 'candidates/one-page-padding-staircase-carrier65-2011/polynomial.json'
PIN = 'f1f7611842896806fa9e70ad102c6a0e7aa11747a650968f1c74cb169f0e253e'
raw = SOURCE.read_bytes()
if hashlib.sha256(raw).hexdigest() != PIN:
    raise RuntimeError('current graph pin changed')
graph = json.loads(raw)
ports = {}
for name, meta in graph['coefficient_binding']['ports'].items():
    packed = (SOURCE.parent / 'coefficients' / meta['file']).read_bytes()
    if hashlib.sha256(packed).hexdigest() != meta['gzip_sha256']:
        raise RuntimeError('compressed port hash mismatch')
    raw = gzip.decompress(packed)
    if hashlib.sha256(raw).hexdigest() != meta['raw_sha256']:
        raise RuntimeError('raw port hash mismatch')
    ports[name] = int.from_bytes(raw, 'big')

def criterion(q, M, F, C):
    b = q-1
    gap = q*(q-F)-C
    u, r = divmod(gap, b)
    if not (2 <= u <= b and 1 <= r < u):
        return None
    F0, alpha0, C0 = q-u, r, u-r
    t = M*C0-F0
    if t < 0 or t % b:
        return None
    return (F0, alpha0, C0, 1+t//b)

def brute(q, M, gap):
    b = q-1
    answers = []
    for F0 in range(1, q):
        for alpha0 in range(1, q-F0):
            C0 = q-F0-alpha0
            if C0 <= 0 or b*(q-F0)+alpha0 != gap:
                continue
            t = M*C0-F0
            if t >= 0 and t % b == 0:
                answers.append((F0, alpha0, C0, 1+t//b))
    return answers

cases = repairs = failures = 0
examples = {'direct': None, 'alternate': None, 'unrepairable': None}
for q in range(2, 13):
 for M in range(1, 21):
  for F in range(1, 16):
   for C in range(1, 16):
    b = q-1; t = M*C-F
    if t < 0 or t % b:
        continue
    z = 1+t//b
    if M*C+q-F-z*b != 1:
        raise RuntimeError('candidate transport error')
    gap = q*(q-F)-C
    actual = brute(q, M, gap)
    predicted = criterion(q, M, F, C)
    if actual != ([] if predicted is None else [predicted]):
        raise RuntimeError(f'criterion mismatch for {(q,M,F,C)}')
    cases += 1
    if predicted is None:
        failures += 1; kind = 'unrepairable'
    else:
        repairs += 1
        kind = 'direct' if F == predicted[0] and C == predicted[2] else 'alternate'
    if examples[kind] is None:
        examples[kind] = {'q': q, 'M': M, 'F': F, 'C': C, 'z': z,
                          'gap': gap, 'repair': predicted}
if not all(examples.values()):
    raise RuntimeError('missing expected controls')

beta, K, mc, mf = [ports[x] for x in ('beta', 'K0', 'MC', 'MF')]
q = beta+1
if not (beta >= 31 and beta % 2 == 1 and mc % 2 == 0):
    raise RuntimeError('unexpected fixed ports')
M = K + q//2 + (q-2)*K
F, C = 1, q+1
z = 1+(q+2)//2+K*(q+1)
if not (M*C+q-F-z*(q-1) == 1 and criterion(q, M, F, C) is None):
    raise RuntimeError('fixed-port obstruction failed')
gap = q*(q-F)-C
u, r = divmod(gap, q-1)
if not (u == q-2 and r == q-3 and (M*(u-r)-(q-u)) % (q-1) != 0):
    raise RuntimeError('fixed-port failure was not the transport congruence')

# A second actual-port scalar assignment has an unrecoverable gap, odd R,
# and hence the symbolic first-Pell extension from the preceding packet.
C2 = 2*q-1
w2 = 1+(q-2)*K
M2 = K+w2
z2 = 3+K*(2*q-1)
gap2 = q*(q-1)-C2
rank2 = gap2*(q*q-1)+mc+q*mf
E2 = w2*q**4
u2, r2 = divmod(gap2, q-1)
if not (M2*C2+q-1-z2*(q-1) == 1 and q-1-C2 == -q and
        u2 == q-3 and r2 == q-2 and r2 >= u2 and
        rank2 % 2 == 1 and 1 < rank2 < q**4-q**3 < E2 and
        (2*((rank2+1)//2)-rank2-1) % E2 == 0):
    raise RuntimeError('fixed-port first-Pell unrecoverable-gap obstruction failed')

# Exact main Pell unit-step norm identity in Z[p,x,y].
one = {(0,0,0): 1}; p = {(1,0,0): 1}; x = {(0,1,0): 1}; y = {(0,0,1): 1}
def add(a, b):
    out = Counter(a); out.update(b)
    return {k: v for k, v in out.items() if v}
def sub(a, b): return add(a, {k: -v for k, v in b.items()})
def mul(a, b):
    out = Counter()
    for aa, av in a.items():
        for bb, bv in b.items():
            out[tuple(v+w for v, w in zip(aa, bb))] += av*bv
    return {k: v for k, v in out.items() if v}
disc = sub(mul(p,p), one)
xp, yp = add(mul(p,x),mul(disc,y)), add(x,mul(p,y))
if sub(mul(xp,xp),mul(disc,mul(yp,yp))) != sub(mul(x,x),mul(disc,mul(y,y))):
    raise RuntimeError('main Pell step failed')

result = {'source_sha256': PIN, 'checker_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
          'bounded_ranges': {'q': [2,12], 'M': [1,20], 'F': [1,15], 'C': [1,15]},
          'candidate_transport_cases': cases, 'repairable': repairs, 'unrepairable': failures,
          'examples': examples, 'fixed_port_first_pell_scalar':
              {'candidate_transport': 1, 'gap_division_ok': True, 'old_transport_congruence': False},
          'fixed_port_unrecoverable_gap_first_pell_scalar':
              {'candidate_transport': 1, 'alpha': 'minus_q', 'rank_window': True,
               'rank_odd': True, 'remainder_not_less_than_quotient': True,
               'symbolic_pell_extension': True, 'full_zero_claimed': False},
          'main_pell_step_identity': 'exact sparse polynomial',
          'scope': 'exact bounded scalar check; no remaining norm or full-zero conclusion'}
print(json.dumps(result, sort_keys=True, indent=2))
