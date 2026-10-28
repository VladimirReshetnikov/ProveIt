#!/usr/bin/env python3
"""Small exact leading-component check, reading a pinned certificate as data.

No project module is imported; no graph or proposed equation is materialized.
The obstruction is limited to the explicitly bounded correction degrees.
"""
import hashlib
import json
from pathlib import Path
import resource

resource.setrlimit(resource.RLIMIT_AS, (512 * 1024**2, 512 * 1024**2))
resource.setrlimit(resource.RLIMIT_CPU, (20, 20))
HERE = Path(__file__).resolve().parent
PARENT = HERE.parent / 'thirteen-second-first-norm-corrections/CERTIFICATE.json'
PIN = 'b05205f7a5e40dcddf78d77fd6a170a79c4e0df45c3ba23c9bc8b68c3f44d3e5'
NAMES = ['J','F','alpha','f','i','T','s','w','n','eta','zeta','m','gamma',
         'beta','K0','MC','MF']
ZERO = (0,) * len(NAMES)

def require(ok, why):
    if not ok:
        raise ValueError(why)

def add(a, b, sign=1):
    out = dict(a)
    for m, c in b.items():
        out[m] = out.get(m, 0) + sign*c
    return {m:c for m,c in out.items() if c}

def mul(a, b):
    out = {}
    for ma, ca in a.items():
        for mb, cb in b.items():
            m = tuple(x+y for x,y in zip(ma,mb))
            out[m] = out.get(m, 0) + ca*cb
    return {m:c for m,c in out.items() if c}

def power(a, n):
    out = {ZERO:1}
    for _ in range(n):
        out = mul(out, a)
    return out

def symbol(s):
    m = list(ZERO)
    m[NAMES.index(s)] = 1
    return {tuple(m):1}

raw = PARENT.read_bytes()
require(hashlib.sha256(raw).hexdigest() == PIN, 'parent certificate pin')
data = json.loads(raw)['variants']['88']['exact_degree']
u = {tuple(m):c for m,c in data['complete_corrected_auxiliary_leader']}
p = {tuple(m):c for m,c in data['all_gate_leaders']['N0']['complete_leader']}
q = {tuple(m):c for m,c in data['all_gate_leaders']['N1']['complete_leader']}
require(all(sum(m[:13]) == 44 for m in u), 'auxiliary homogeneous degree')
require(all(m[7] >= 2 for m in p), 'P leading part divisible by w squared')
require(all(m[7] >= 2 for m in q), 'Q leading part divisible by w squared')

B = mul(symbol('beta'), symbol('J'))
K = add(symbol('eta'), symbol('zeta'))
C = add(add(B, symbol('F'), -1), symbol('alpha'), -1)
G = add(mul(symbol('K0'), C), symbol('F'), -1)
expected = {ZERO:-32}
for v,n in [(B,21),(K,4),(symbol('f'),6),(symbol('T'),4),
            (symbol('s'),6),(symbol('w'),1),(G,2)]:
    expected = mul(expected, power(v,n))
actual = {m:c for m,c in u.items() if m[7] == 1}
require(expected == actual, 'complete w-linear component factorization')

# This particular unknown monomial has one symbolic-port contribution.
selected = [21,0,2,6,0,4,6,1,0,0,4,0,0]
contributions = [(m,c) for m,c in actual.items() if list(m[:13]) == selected]
require(len(contributions) == 1, 'unique port contribution')
m,c = contributions[0]
require(m[13:] == (21,2,0,0) and c == -32, 'actual nonzero coefficient')
require(all(m[7] >= 1 for m in u), 'all auxiliary leader terms have w')

out = {
    'scope':'Exact bounded-degree obstruction; not a global degree lower bound',
    'script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
    'parent_sha256':PIN,
    'degree':44,
    'complete_leader_terms':len(u),
    'w_linear_terms':len(actual),
    'w_linear_factor':'-32 B^21 (eta+zeta)^4 f^6 T^4 s^6 w (K0*(B-F-alpha)-F)^2',
    'selected_unknown_exponents':selected,
    'selected_coefficient':'-32 beta^21 K0^2',
    'bounded_correction_degrees':{'A_times_Pminus1':22,'B_times_Qminus1':26},
    'reason':'The degree44 part of either bounded multiple is divisible by w^2, while this component is not.',
    'excluded_claims':['unbounded cancellation between correction coefficients',
                       'other norm combinations', 'global optimality']
}
print(json.dumps(out,indent=2))
