#!/usr/bin/env python3
"""Exact first-factor witness; the full 88 graph is deliberately nonzero."""
import hashlib
import json
from math import isqrt
from pathlib import Path


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


graph_path = Path(__file__).resolve().parent.parent / 'ordinary12-absorb88-probe' / 'graph-dag.json'
graph_bytes = graph_path.read_bytes()
require(hashlib.sha256(graph_bytes).hexdigest() == '84a9a529636d6cadcf0f0c673c0728aa7b6fcbc0e2f2ac562a377553de831b25', 'graph drift')
graph = json.loads(graph_bytes)
v = {i: i for i in range(5)}
v.update({name: 1 for name in graph['witnesses'] + graph['fixed_numerals']})
P = 16384
k = 4 * (2 * P + 1)
tau = 2 * (2 * P + 1) ** 2 - 1
transport_magnitude = 1548
b = 3
require(transport_magnitude % b == 0, 'transport divisibility')
r = tau - (b * k + 1) * (transport_magnitude // b)
v.update(beta=3, K0=1, MC=0, MF=0, F=1, alpha=196, eta=1, zeta=k-1, r=r)
for name, op, x, y in graph['source']:
    left, right = v[x], v[y]
    if op == '+':
        value = left + right
    elif op == '-':
        value = left - right
    elif op == '*':
        value = left * right
    else:
        raise RuntimeError(f'unknown operation {op}')
    v[name] = value

require(all(v[name] > 0 for name in graph['witnesses']), 'positive input witnesses')
require((v['beta'], v['K0'], v['MC'], v['MF']) == (3, 1, 0, 0), 'symbolic ports')
require(v['K0'] < v['beta'] ** 2 and v['MC'] < v['beta'] and v['MF'] < 2*v['beta'], 'port inequalities')
require((v['qm'], v['q'], v['X'], v['Y'], v['k']) == (3, 4, 4, 64, k), 'graph register values')
require(v['X'] * v['Y'] ** 2 == P, 'P')
require(k == 8*P+4 and tau*tau == 1+P*(P+1)*k*k, 'second first-Pell index and gap')
require(v['Bt'] == -transport_magnitude and 0 < transport_magnitude <= P, 'negative transport bound')
require(v['Z'] == b*tau and v['A0'] == 0, 'actual first residual')
require((v['G'],v['R']) == (205,3075), 'signed rank')
require((2*2-v['R']-1) % v['q']**4 == 0, 'signed early-index congruence')
require((k-v['R']-1) % v['q']**4 == 0, 'signed rank congruence')
require(v['Dstar'] > 0, 'expanded main expression')
require(v['A1'] != 0 and v['N'] != 0 and v['P12'] > 0, 'full graph must not vanish')

q, A = v['q'], v['K0']+v['w']
possible = []
for F in range(1, q):
    for alpha in range(1, q-F):
        if (q-F-alpha)*A-F > 0:
            possible.append(alpha+(q-1)*(q-F))
require(possible and max(possible) <= 11 and v['G'] not in possible, 'G-preserving positive transport')
a = v['X']*v['Y']+v['Y']
c = v['eta']+v['Y']*v['k']
main_norm = 1+(a*a+4*a+3)*c*c
require(isqrt(main_norm)**2 < main_norm, 'main Pell norm must not be square')
print(json.dumps({'graph_sha256': hashlib.sha256(graph_bytes).hexdigest(),
    'status': 'PASS', 'scope': 'first factor and listed scalar conditions only; not a full graph zero',
    'ports': {name:v[name] for name in graph['fixed_numerals']},
    'key_witnesses': {name:v[name] for name in ('J','F','alpha','w','s','r','eta','zeta')},
    'q':q, 'P':P, 'k':k, 'first_index':2, 'first_root':tau,
    'transport_magnitude':transport_magnitude, 'G':v['G'], 'rank':v['R'],
    'first_residual':v['A0'], 'main_residual_nonzero':v['A1']!=0,
    'ordinary_residual_nonzero':v['N']!=0, 'main_norm_is_square':False,
    'max_G_among_positive_transport_representatives':max(possible)}, indent=2, sort_keys=True))
