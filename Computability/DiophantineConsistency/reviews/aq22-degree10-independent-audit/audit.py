#!/usr/bin/env python3
"""Independent finite audit of the four-coordinate AQ26 to AQ22 rewrite."""
import hashlib
import json
from pathlib import Path

if not __debug__:
    raise RuntimeError('optimized Python is not supported')

D = Path(__file__).resolve().parent
ROOT = D.parents[1]
OLD = ROOT / 'research/adaptive-square-sums26-degree8/candidate.json'
NEW = ROOT / 'research/adaptive-square-sums22-degree10/candidate.json'
H = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
inputs = (OLD, NEW, Path(__file__))
before = {str(p): H(p) for p in inputs}
assert H(OLD) == 'd8e80e15d74271ba62877e841198a85729c0c4a74a5927927591b9ec2204b1a5'
assert H(NEW) == '1266b143c5512351739ea2c71fc8e0b8b0e5cecc599392f128c0803ff78ce106'
old, new = json.loads(OLD.read_text()), json.loads(NEW.read_text())
removed = {'cVariable': ('c', 'cDifference'), 'productVariable2': ('E', 'product2Difference'),
           'qSquareVariable': ('q2', 'qSquareDifference'), 'qValueVariable': ('QComputed', 'qSignedDifference')}
assert len(old['witnesses']) == 26 and len(new['witnesses']) == 22
assert [x for x in old['witnesses'] if x not in removed] == new['witnesses']
assert old['fixed_numerals'] == new['fixed_numerals'] == ['beta', 'K0', 'MC', 'MF']
assert len(new['source']) == new['operations'] == 114

def row_table(graph):
    table = {}
    known = set(graph['witnesses'] + graph['fixed_numerals'])
    for name, op, a, b in graph['source']:
        assert name not in known and op in ('+', '-', '*')
        assert all(isinstance(v, int) or v in known for v in (a, b))
        table[name] = (op, a, b)
        known.add(name)
    assert graph['output'] in table
    live = {graph['output']}
    todo = [graph['output']]
    while todo:
        n = todo.pop()
        if n in table:
            for dep in table[n][1:]:
                if isinstance(dep, str) and dep not in live:
                    live.add(dep)
                    todo.append(dep)
    assert set(table) <= live and set(graph['witnesses'] + graph['fixed_numerals']) <= live
    return table

old_rows, new_rows = row_table(old), row_table(new)
for coordinate, (expression, difference) in removed.items():
    assert old_rows[difference] == ('-', coordinate, expression)

def factors(rows, name):
    op, a, b = rows[name]
    if op == '*':
        assert a == b and isinstance(a, str)
        return [a]
    assert op == '+' and isinstance(a, str) and isinstance(b, str)
    return factors(rows, a) + factors(rows, b)

old_factors, new_factors = factors(old_rows, old['output']), factors(new_rows, new['output'])
assert len(old_factors) == len(set(old_factors)) == 17
assert len(new_factors) == len(set(new_factors)) == 13
assert [x for x in old_factors if x not in {z[1] for z in removed.values()}] == new_factors

# Positivity-relevant wiring is checked against the child graph independently
# of the original generator's text. All inputs below are strictly positive,
# except beta which is nonnegative for the intended fixed ports.
for name, expected in {
    'k': ('+', 'eta', 'zeta'), 'kY': ('*', 'Y', 'k'), 'c': ('+', 'eta', 'kY'),
    'E': ('*', 'X', 'Y'), 'qm': ('*', 'J', 'beta'), 'q': ('+', 1, 'qm'),
    'q2': ('*', 'q', 'q'), 'f2': ('*', 'f', 'f'), 'rho': ('-', 'f2', 1),
    'QComputed': ('*', 'deltaVariable', 'rho'), 'I': ('*', 'cSquareVariable', 'i'),
    'g71': ('*', 'I', 'I'), 'g72': ('-', 'g71', 'QComputed'),
}.items():
    assert new_rows.get(name) == expected, name
assert 'g72' in new_factors

names = new['witnesses'] + new['fixed_numerals']
zero = (0,) * len(names)
def add(a, b, sign=1):
    d = a.copy()
    for mon, coeff in b.items():
        d[mon] = d.get(mon, 0) + sign * coeff
        if not d[mon]:
            del d[mon]
    return d

def mul(a, b):
    d = {}
    for x, cx in a.items():
        for y, cy in b.items():
            mon = tuple(i + j for i, j in zip(x, y))
            d[mon] = d.get(mon, 0) + cx * cy
    return {k: v for k, v in d.items() if v}

symbols = {}
for i, name in enumerate(names):
    exponent = list(zero)
    exponent[i] = 1
    symbols[name] = {tuple(exponent): 1}

def evaluator(rows, memo):
    def value(name):
        if isinstance(name, int):
            return {zero: name} if name else {}
        if name in memo:
            return memo[name]
        op, a, b = rows[name]
        x, y = value(a), value(b)
        memo[name] = add(x, y) if op == '+' else add(x, y, -1) if op == '-' else mul(x, y)
        return memo[name]
    return value

child = evaluator(new_rows, dict(symbols))
parent_inputs = dict(symbols)
for name, (expression, _) in removed.items():
    parent_inputs[name] = child(expression)
parent = evaluator(old_rows, parent_inputs)
for residual in old_factors:
    expected = {} if residual in {x[1] for x in removed.values()} else child(residual)
    assert parent(residual) == expected, residual

degrees = {r: max((sum(m[:22]) for m in child(r)), default=-1) for r in new_factors}
assert max(degrees.values()) == 5
witness = [0] * 22
for n, e in {'f': 2, 'y': 2, 'deltaVariable': 1}.items():
    witness[names.index(n)] = e
terms = {m[22:]: coefficient for m, coefficient in child('auxResidual').items()
         if m[:22] == tuple(witness)}
assert terms == {(0, 0, 0, 0): -1}
assert {str(p): H(p) for p in inputs} == before

result = {'status': 'PASS_INDEPENDENT_AQ22_FINITE_AUDIT',
          'parent_sha256': H(OLD), 'child_sha256': H(NEW), 'audit_sha256': H(Path(__file__)),
          'coordinates': 22, 'fixed_ports': 4, 'operations': 114,
          'parent_residuals': 17, 'child_residuals': 13,
          'residual_degrees': degrees, 'leading_monomial': 'f^2*y^2*deltaVariable',
          'leading_coefficient': -1,
          'scope': 'Finite graph wiring, positivity-relevant identities, exact residual substitution and degree; no Lean transport, internal iPRA derivation or minimality claim.'}
out = D / 'receipt.json'
assert not out.exists()
out.write_text(json.dumps(result, indent=2, sort_keys=True) + '\n')
print(result['status'], H(out))
