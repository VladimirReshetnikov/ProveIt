#!/usr/bin/env python3
"""Exact full zero of the independent-I modification, at explicit natural ports."""
import hashlib
import json
import math
import sys
from pathlib import Path

if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:
    raise SystemExit('Use python3 -I -S -B without optimization')

def require(ok, message):
    if not ok:
        raise RuntimeError(message)

def mul(u, v, d):
    x, y = u
    z, w = v
    return x*z + d*y*w, x*w + y*z

def power(x, y, d, exponent):
    out, base = (1, 0), (x, y)
    while exponent:
        if exponent & 1:
            out = mul(out, base, d)
        exponent //= 2
        if exponent:
            base = mul(base, base, d)
    return out

def digest(n):
    require(n >= 0, 'negative digest operand')
    return hashlib.sha256(n.to_bytes(max(1, (n.bit_length()+7)//8), 'big')).hexdigest()

# Fixed small constants, and exact algebraic integers defining the finite witness.
q, Y, X, a, H, U, D, P, n = 3, 27, 6, 189, 759, 729, 36480, 4374, 191
(t, k) = power(2*P+1, 2, P*(P+1), 11720)
(g, c) = power(n, 1, D, 19259)
I = D
(aux_x, y) = power(I, 1, I*I-1, 561)
require(aux_x % I == 0, 'auxiliary index division')
V = aux_x // I
require(27*k < c < 28*k, 'positive eta/zeta')
require(c % (n*n) == n*n-1, 'auxiliary sign')
require((c+V) % (n*n) == 0, 'quotient division')
L = (c+V) // (n*n)
require(U*(g-X-a*c) % H == 0, 'main index division')
A = U*(g-X-a*c) // H
B = k-1+A
require(math.gcd(U,c) == 1, 'inverse assumption')
gamma = ((B+L)*pow(U,-1,c)) % c
require(gamma > 0, 'positive gamma')
R = B-U*gamma
require(R >= 40, 'natural MC port')
require((R+L) % c == 0, 'T division')
T = (R+L)//c
eta, zeta = c-27*k, 28*k-c
ports = dict(beta=2, K0=3, MC=R-40, MF=0)
witness = dict(J=1, F=1, alpha=1, z=2, f=n, I=I, T=T, s=1,
               w=2, t=t, eta=eta, zeta=zeta, y=y, gamma=gamma)
require(all(x >= 0 for x in ports.values()), 'negative port')
require(all(x > 0 for x in witness.values()), 'nonpositive witness')
require(I % (c*c) != 0, 'index unexpectedly recoverable')

# Independently interpret every gate in the pinned 76Y graph, changing precisely
# the single assignment I := i*c2 into the positive input I used above.
graph_path = Path(__file__).resolve().parent.parent / 'p64-qcube76-independent-y-candidate' / 'graph.json'
graph_bytes = graph_path.read_bytes()
require(hashlib.sha256(graph_bytes).hexdigest() == '196ef3bdf6805c7ed7d44c278359e32c0f658634db357cc19f0e87464ed6b11c', 'graph hash changed')
graph = json.loads(graph_bytes)
gates = graph['source']
require(sum(row[0] == 'I' for row in gates) == 1, 'unexpected I assignment count')
require(next(row for row in gates if row[0] == 'I') == ['I','*','i','c2'], 'unexpected I assignment')
values = dict(ports, **witness)
count = 0
for row in gates:
    name, op, left, right = row
    if name == 'I':
        continue
    require(name not in values, 'duplicate graph definition '+name)
    require(op in ('+', '-', '*'), 'unknown gate')
    x = values[left] if isinstance(left, str) else left
    y0 = values[right] if isinstance(right, str) else right
    values[name] = x+y0 if op == '+' else x-y0 if op == '-' else x*y0
    count += 1
max_gate_bits = max(abs(value).bit_length() for value in values.values())
require(c.bit_length() == 165184 and max_gate_bits <= 400000, 'unexpected integer size')
require(values['R'] == R and values['c'] == c and values['V'] == V, 'witness mapping')
require(values['A0'] == 1 and values['Na'] == 1, 'unit equations')
require(values['M'] == values['W'] == values['Lt'] == values['polynomial'] == 0, 'output is not zero')
result = {
    'status':'PASS_FULL_MODIFIED_GRAPH_ZERO',
    'graph_sha256':hashlib.sha256(graph_bytes).hexdigest(),
    'script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
    'checked_original_gates_except_I':count,
    'maximum_absolute_gate_or_input_bits':max_gate_bits,
    'ports':{'beta':2,'K0':3,'MC':'R-40, exactly as defined by check.py','MF':0,
             'MC_bits':ports['MC'].bit_length(),'MC_sha256_unsigned_big_endian':digest(ports['MC'])},
    'witness_bits':{name:value.bit_length() for name,value in witness.items()},
    'key_sha256_unsigned_big_endian':{name:digest(value) for name,value in [('c',c),('k',k),('R',R),('gamma',gamma),('T',T)]},
    'pell_exponents':{'first':11720,'main':19259,'auxiliary':561},
    'A0':1,'Na':1,'M':0,'W':0,'Lt':0,'polynomial':0,
    'I':I,'I_mod_c_squared':I%(c*c),
    'scope':'Modified graph at specified natural ports only; no original-graph nonexistence or compact44-port claim.'
}
print(json.dumps(result,indent=2,sort_keys=True))
