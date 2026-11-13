#!/usr/bin/env python3
"""Check a bounded degree obstruction for zero-set-preserving residual shears."""
from collections import Counter
import copy
import gzip
import hashlib
import json
from pathlib import Path

if not __debug__:
    raise RuntimeError('optimized Python is unsupported')

ROOT = Path(__file__).resolve().parents[2]
GRAPH = ROOT/'research/adaptive-square-sums/candidate.json'
PORTS = ROOT/'candidates/one-page-padding-staircase-carrier65-2011/polynomial.json'
BINDING = ROOT/'reviews/frontier13-pdf-historical-lean-binding-independent-audit/receipt.json'
PIN = '11fb3c192fb3a8ab9204ef0a5401198d986e002242e4f48442147aa356263828'
H = lambda data: hashlib.sha256(data).hexdigest()
raw = GRAPH.read_bytes()
assert H(raw) == PIN
graph = json.loads(raw)
witnesses, ports = graph['witnesses'], graph['fixed_numerals']
assert len(witnesses) == 13 and ports == ['beta','K0','MC','MF']
names = witnesses + ports
zero = (0,)*len(names)


def add(a,b,sign=1):
    result = dict(a)
    for monomial, value in b.items():
        result[monomial] = result.get(monomial,0) + sign*value
    return {m:v for m,v in result.items() if v}


def mul(a,b):
    result = {}
    for x,u in a.items():
        for y,v in b.items():
            key = tuple(i+j for i,j in zip(x,y))
            result[key] = result.get(key,0) + u*v
    return {m:v for m,v in result.items() if v}


def atom(name):
    key = list(zero); key[names.index(name)] = 1
    return {tuple(key):1}


def power(value,n):
    result = {zero:1}
    for _ in range(n): result = mul(result,value)
    return result


def evaluate(rows):
    values = {name:atom(name) for name in names}
    for name, kind, left, right in rows:
        if name == 'firstSquare': break
        assert name not in values and kind in ('+','-','*')
        a = {zero:left} if isinstance(left,int) else values[left]
        b = {zero:right} if isinstance(right,int) else values[right]
        values[name] = mul(a,b) if kind == '*' else add(a,b,-1 if kind == '-' else 1)
    return values


def degree(poly):
    return max((sum(m[:len(witnesses)]) for m in poly), default=-1)


def validate(g):
    values = evaluate(g['source'])
    factors = ['A0','A1','g72','auxResidual']
    degrees = {name:degree(values[name]) for name in factors}
    assert degrees == {'A0':15,'A1':13,'g72':10,'auxResidual':18}
    # All leading monomials of the three shear sources contain eta or zeta.
    for name in factors[:3]:
        lead = [m for m in values[name] if sum(m[:13]) == degrees[name]]
        assert lead and all(m[names.index('eta')] + m[names.index('zeta')] > 0 for m in lead), name
    # The aux coefficient at this witness monomial is exactly beta^8, with
    # no dependence on any other port, before actual-port specialization.
    wanted = {'J':8,'f':6,'X':2,'Y':2}
    target = tuple(wanted.get(n,0) for n in witnesses)
    coeff = {m[13:]:v for m,v in values['auxResidual'].items() if m[:13] == target}
    assert coeff == {(8,0,0,0):1}
    return values, degrees


values, degrees = validate(graph)
# Check the four-square output wiring separately; the theorem applies to its
# shear, not to a changed or assumed Diophantine equation.
rows = {row[0]:row for row in graph['source']}
def leaves(name):
    _, kind, a, b = rows[name]
    if kind == '+': return leaves(a) + leaves(b)
    assert kind == '*' and a == b
    return [a]
assert Counter(leaves(graph['output'])) == Counter(['A0','A1','auxResidual','g72'])

# Concrete maximum-degree multipliers exercise the general bound in the note.
sheared = add(add(add(values['auxResidual'],mul(power(atom('f'),3),values['A0'])),
                  mul(power(atom('J'),5),values['A1'])),mul(power(atom('i'),8),values['g72']))
assert degree(sheared) == 18
target = tuple({'J':8,'f':6,'X':2,'Y':2}.get(n,0) for n in witnesses)
assert {m[13:]:v for m,v in sheared.items() if m[:13] == target} == {(8,0,0,0):1}

# Tie the nonzero beta specialization to the recorded full port bytes, not a
# small-number sample. Its link to displayed TeX inherits the existing audit.
carrier_bytes = PORTS.read_bytes()
assert H(carrier_bytes) == 'f1f7611842896806fa9e70ad102c6a0e7aa11747a650968f1c74cb169f0e253e'
binding_bytes = BINDING.read_bytes()
assert H(binding_bytes) == '44d14b51deca8b68c033b28f6244ee857c187386269730bb144e8b11913890de'
binding = json.loads(binding_bytes)
assert binding['status'] == 'PASS_INDEPENDENT_FRONTIER13_PDF_BINDING_REVIEW'
carrier = json.loads(carrier_bytes)
meta = carrier['coefficient_binding']['ports']['beta']
packed = (PORTS.parent/'coefficients'/meta['file']).read_bytes()
assert H(packed) == meta['gzip_sha256']
beta_bytes = gzip.decompress(packed)
assert H(beta_bytes) == meta['raw_sha256'] == binding['ports'][0]['integer_sha256']
assert binding['ports'][0]['name'] == 'beta'
beta = int.from_bytes(beta_bytes,'big')
assert beta == (1 << 94517)-1 and beta > 0

# Reject changes that destroy the documented leading-degree certificate.
for changed_name, replacement in (
    ('qm',['qm','*','J',0]),
    ('A0',['A0','+','g38','g42']),
    ('g82',['g82','+','Q','g81']),
):
    bad = copy.deepcopy(graph)
    idx = next(i for i,row in enumerate(bad['source']) if row[0] == changed_name)
    bad['source'][idx] = replacement
    try: validate(bad)
    except AssertionError: pass
    else: raise AssertionError(('mutation not detected',changed_name))

print('PASS_BOUNDED_SHEAR_DEGREE',json.dumps({
    'graph_sha256':PIN, 'residual_degrees':degrees,
    'multiplier_witness_degree_bounds':{'A0':3,'A1':5,'g72':8},
    'retained_monomial':{'J':8,'f':6,'X':2,'Y':2},
    'retained_coefficient':'beta^8', 'beta_bits':beta.bit_length(),
    'actual_fixed_port_nonzero':True, 'sheared_residual_degree':18,
    'four_square_degree':36, 'mutation_controls':3,
    'scope':'ordinary integer polynomial reasoning; no Lean theorem or global minimum',
},sort_keys=True))
