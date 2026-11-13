#!/usr/bin/env python3
"""Independently check the AQ17-to-AQ16 finite reduction; no Lean replay."""
import gzip
import hashlib
import json
import sys
from collections import Counter
from functools import lru_cache
from pathlib import Path

if not __debug__:
    raise RuntimeError('optimized Python is unsupported')

ROOT = Path(__file__).resolve().parents[2]
parent_path = ROOT / 'research/aq22-positive-binding-survey/candidate17.json'
child_path = ROOT / 'research/aq17-positive-signed-binding/candidate16.json'
ports_path = ROOT / 'candidates/one-page-padding-staircase-carrier65-2011/polynomial.json'
binding_path = ROOT / 'reviews/aq22-pdf-historical-lean-binding-independent/receipt.json'
sha = lambda b: hashlib.sha256(b).hexdigest()
parent_bytes, child_bytes = parent_path.read_bytes(), child_path.read_bytes()
assert sha(parent_bytes) == '760b9e7babbb559b7175344915456fdc3d9bd8ce85382873d4915faf2cd76d81'
assert sha(child_bytes) == 'a7d6f8a618a810b37eb7a9de6bd92ceb73bd6351971fdd39045bf95f8bf9edac'
parent, child = json.loads(parent_bytes), json.loads(child_bytes)
assert child['parent_sha256'] == sha(parent_bytes)
assert child['eliminated_bindings'] == {'dValueVariable': 'DstarComputed'}
assert child['port_hypotheses'] == {'beta_lower_bound': 2}
assert child['witnesses'] == [x for x in parent['witnesses'] if x != 'dValueVariable']
assert len(child['witnesses']) == len(set(child['witnesses'])) == 16
assert child['fixed_numerals'] == parent['fixed_numerals'] == ['beta', 'K0', 'MC', 'MF']
assert not set(child['witnesses']) & set(child['fixed_numerals'])

def graph(g, count):
    nodes = set(g['witnesses'] + g['fixed_numerals'])
    rows = {}
    assert len(g['source']) == count
    for name, op, left, right in g['source']:
        assert name not in nodes and op in ('+', '-', '*')
        assert all(isinstance(x, int) or x in nodes for x in (left, right))
        rows[name] = op, left, right
        nodes.add(name)
    return rows

pr, cr = graph(parent, 99), graph(child, 96)
assert pr['dDifference'] == ('-', 'dValueVariable', 'DstarComputed')
assert child['residuals'] == [x for x in parent['residuals'] if x != 'dDifference']
assert len(child['residuals']) == 7
live, todo = set(), [child['output']]
while todo:
    x = todo.pop()
    if not isinstance(x, str) or x in live:
        continue
    live.add(x)
    if x in cr:
        todo.extend(cr[x][1:])
assert set(cr) <= live and set(child['witnesses'] + child['fixed_numerals']) <= live

def tree(rows, replacements):
    @lru_cache(None)
    def go(x):
        if isinstance(x, int):
            return ('constant', x)
        if x in replacements:
            return go(replacements[x])
        if x not in rows:
            return ('input', x)
        op, a, b = rows[x]
        return (op, go(a), go(b))
    return go

old = tree(pr, {'dValueVariable': 'DstarComputed'})
new = tree(cr, {})
for name in child['residuals']:
    assert old(name) == new(name), name
deleted = old('dDifference')
assert deleted[0] == '-' and deleted[1] == deleted[2]

def square_terms(rows, name):
    op, a, b = rows[name]
    if op == '+':
        return square_terms(rows, a) + square_terms(rows, b)
    assert op == '*' and a == b
    return [a]

assert Counter(square_terms(pr, parent['output'])) == Counter(parent['residuals'])
assert Counter(square_terms(cr, child['output'])) == Counter(child['residuals'])
assert 'dValueVariable' not in str(old('DstarComputed'))

# Independently bind the positivity proof to the graph's actual operations.
required = {
    'qm': ('*', 'J', 'beta'), 'q': ('+', 1, 'qm'), 'q2': ('*', 'q', 'q'),
    'U': ('*', 'Y', 'q2'), 'E': ('*', 'X', 'Y'), 'a': ('+', 'E', 'Y'),
    'k': ('+', 'eta', 'zeta'), 'kY': ('*', 'Y', 'k'), 'c': ('+', 'eta', 'kY'),
    'g15': ('*', 4, 'a'), 'H': ('+', 3, 'g15'),
}
for name, row in required.items():
    assert pr[name] == row, (name, pr[name])

# Sparse monomials use sorted tuples of indices, independently of the author's
# fixed-length exponent vectors. Include ports as variables until specialization.
variables = child['witnesses'] + child['fixed_numerals']
def add(a, b, factor=1):
    result = dict(a)
    for k, v in b.items():
        result[k] = result.get(k, 0) + factor*v
    return {k: v for k, v in result.items() if v}
def mul(a, b):
    result = {}
    for x, v in a.items():
        for y, w in b.items():
            k = tuple(sorted(x+y))
            result[k] = result.get(k, 0) + v*w
    return {k: v for k, v in result.items() if v}
def atom(name):
    return {(variables.index(name),): 1}
def evaluate(rows):
    @lru_cache(None)
    def go(name):
        if isinstance(name, int):
            return {(): name} if name else {}
        if name in variables:
            return atom(name)
        op, a, b = rows[name]
        x, y = go(a), go(b)
        return mul(x, y) if op == '*' else add(x, y, -1 if op == '-' else 1)
    return go

p = evaluate(cr)
one = {(): 1}
first = mul(p('U'), add(atom('X'), mul(p('a'), atom('eta'))))
coefficient = add(mul(mul(p('U'), p('a')), atom('Y')), p('H'), -1)
last = mul(p('H'), add(add(add(mul(p('U'), atom('gamma')), mul(p('E'), p('q'))), atom('rankVariable')), one))
rhs = add(add(first, mul(coefficient, p('k'))), last)
assert p('DstarComputed') == rhs
# q>=3, a>=2, U*a*Y=Y^2*q^2*a>=9a>4a+3=H, so all
# three summands are positive for positive witnesses and beta>=2.
assert p('DstarComputed') != add(add(first, mul(coefficient, p('k'))), last, -1)

degree = {n: max(sum(i < 16 for i in m) for m in p(n)) for n in child['residuals']}
assert degree['A0'] == max(degree.values()) == 16
target = sorted([variables.index('J')]*8 + [variables.index('X')]*2 +
                [variables.index('Y')]*4 + [variables.index('eta')]*2)
terms = {tuple(i for i in m if i >= 16): v for m, v in p('A0').items()
         if [i for i in m if i < 16] == target}
assert terms == {(variables.index('beta'),)*8: -1}
carrier = json.loads(ports_path.read_text())
binding = json.loads(binding_path.read_text())
assert binding['status'] == 'PASS_INDEPENDENT_AQ22_FINITE_BINDING_REVIEW'
assert binding['ports'][0]['name'] == 'beta'
meta = carrier['coefficient_binding']['ports']['beta']
packed = (ports_path.parent / 'coefficients' / meta['file']).read_bytes()
assert sha(packed) == meta['gzip_sha256']
raw = gzip.decompress(packed)
assert sha(raw) == meta['raw_sha256'] == binding['ports'][0]['integer_sha256']
assert int.from_bytes(raw, 'big') == (1 << 94517) - 1 >= 2

# Reject changed retained-residual wiring and a changed deleted binding.
bad = dict(cr); bad['g61'] = ('+', 'DstarComputed', 'DstarComputed')
assert tree(bad, {})('A1') != old('A1')
bad = dict(pr); bad['dDifference'] = ('+', 'dValueVariable', 'DstarComputed')
mutated_deleted = tree(bad, {'dValueVariable': 'DstarComputed'})('dDifference')
assert mutated_deleted[0] != '-'
try:
    bad = dict(cr); op, a, b = bad[child['output']]; bad[child['output']] = ('-', a, b)
    square_terms(bad, child['output'])
except AssertionError:
    pass
else:
    raise AssertionError('output-sign mutation accepted')
assert sha(parent_path.read_bytes()) == sha(parent_bytes)
assert sha(child_path.read_bytes()) == sha(child_bytes)
print(json.dumps({'status': 'PASS_AQ16_INDEPENDENT_FINITE_AUDIT',
                  'parent_sha256': sha(parent_bytes), 'candidate_sha256': sha(child_bytes),
                  'variables': 16, 'gates': 96, 'squares': 7,
                  'residual_degrees': degree, 'degree': 32,
                  'scope': 'finite algebra, not a Lean replay or PDF semantics'}, sort_keys=True))
