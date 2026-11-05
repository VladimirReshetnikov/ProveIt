#!/usr/bin/env python3
"""Exact bounded partial-constraint example; no graph zero is constructed."""
import hashlib
import json
import sys
from pathlib import Path

if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:
    raise SystemExit('use python3 -I -S -B without optimization')

q, beta, J, F, alpha, w, s, z, K0 = 3, 2, 1, 1, 1, 1, 1, 1, 2
Y, X = q**3*s, w*q
a = Y*(X+1)
delta = a*a+4*a+3
if (Y, X, a, delta) != (27, 3, 108, 12099):
    raise RuntimeError('base parameters differ')

# The 12,099 iterations are explicit; intermediate operands are capped.
g, c = 1, 0
for _ in range(delta):
    g, c = (a+2)*g + delta*c, g + (a+2)*c
    if max(g.bit_length(), c.bit_length()) > 100000:
        raise RuntimeError('Pell operand bound exceeded')
if c.bit_length() != 94139 or c % Y != 15:
    raise RuntimeError('Pell size or residue differs')
c4 = c**4
if c4.bit_length() > 400000 or c4 % delta:
    raise RuntimeError('fourth power bound or divisibility failed')
h, i = 1+c4//delta, 1
eta = 15
k = (c-eta)//Y
zeta = k-eta
C = q-F-alpha
if min(k, zeta, C) <= 0:
    raise RuntimeError('positive witness condition failed')
if q != beta*J+1 or Y != q**3*s or X != w*q or c != k*Y+eta:
    raise RuntimeError('q-cube coordinate relations failed')
if (K0+w)*C-F-z*(q-1) != 0:
    raise RuntimeError('transport equation failed')
if g*g != 1+delta*c*c or delta*(h-1) != i*i*c4:
    raise RuntimeError('main or strong norm failed')
if h % 7 != 6 or h % 7 in {r*r % 7 for r in range(7)}:
    raise RuntimeError('nonsquare residue certificate failed')

result = {
    'status': 'PASS_PARTIAL_CONSTRAINTS_ONLY',
    'script_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
    'pell_iterations': delta,
    'c_bits': c.bit_length(),
    'h_bits': h.bit_length(),
    'c_mod_27': c % 27,
    'h_mod_7': h % 7,
    'scope': 'q-cube coordinates, transport and two norm equations; no full graph zero or equivalence',
}
print(json.dumps(result, indent=2, sort_keys=True))
