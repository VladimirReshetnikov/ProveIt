#!/usr/bin/env python3
"""Independent finite audit of all direct square-residual bindings in AQ26."""
import hashlib
import json
import re
import subprocess
from pathlib import Path

if not __debug__:
    raise RuntimeError('optimized Python is not supported')

D = Path(__file__).resolve().parent
ROOT = D.parents[1]
GRAPH = ROOT / 'research/adaptive-square-sums26-degree8/candidate.json'
SURVEY = ROOT / 'research/adaptive-aq26-substitution-survey/survey.py'
MASK = ROOT / 'Lean/DiophantineConsistency/CurrentMaskData2011.lean'
KERNEL = ROOT / 'Lean/DiophantineConsistency/CurrentKernelData2011.lean'
H = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
inputs = (GRAPH, SURVEY, MASK, KERNEL, Path(__file__))
input_hashes = {str(p): H(p) for p in inputs}
assert H(GRAPH) == 'd8e80e15d74271ba62877e841198a85729c0c4a74a5927927591b9ec2204b1a5'
mask = MASK.read_text()
assert re.search(r'def radix\s*:\s*ℕ\s*:=\s*2\s*\^\s*47', mask)
assert re.search(r'def beta\s*:\s*ℕ\s*:=\s*radix\s*\^\s*2011\s*-\s*1', mask)
assert re.search(r'def ports \(K : ℤ\) : Fin 4 → ℤ := !\[beta, K, lowPort, highPort \+ beta\]', mask)
assert 'def ports : Fin 4 → ℤ := CurrentMasks2011.ports (K : ℤ)' in KERNEL.read_text()
graph = json.loads(GRAPH.read_text())
variables = graph['witnesses']
ports = graph['fixed_numerals']
assert len(variables) == 26 and ports == ['beta', 'K0', 'MC', 'MF']
assert len(set(variables + ports)) == 30
rows = {}
known = set(variables + ports)
for row in graph['source']:
    name, op, a, b = row
    assert name not in known and op in ('+', '-', '*')
    assert all(isinstance(x, int) or x in known for x in (a, b))
    rows[name] = (op, a, b)
    known.add(name)
assert len(rows) == graph['operations'] == 126

def square_residuals(name):
    op, a, b = rows[name]
    if op == '*':
        assert a == b and isinstance(a, str)
        return [a]
    assert op == '+' and isinstance(a, str) and isinstance(b, str)
    return square_residuals(a) + square_residuals(b)

residuals = square_residuals(graph['output'])
assert len(residuals) == len(set(residuals)) == 17

def dependencies(name):
    if isinstance(name, int):
        return set()
    if name not in rows:
        return {name}
    _, a, b = rows[name]
    return dependencies(a) | dependencies(b)

bindings = []
for r in residuals:
    op, a, b = rows[r]
    if op != '-':
        continue
    for v, expression, orientation in ((a, b, 'left'), (b, a, 'right')):
        if v in variables and isinstance(expression, str) and expression in rows and v not in dependencies(expression):
            bindings.append((v, expression, r, orientation))
assert len(bindings) == 14 and len({x[0] for x in bindings}) == 13, bindings
assert ('qValueVariable', 'g71', 'g72', 'right') in bindings

zero = (0,) * 30
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
            m = tuple(i + j for i, j in zip(x, y))
            d[m] = d.get(m, 0) + cx * cy
    return {k: v for k, v in d.items() if v}

def polys_for(variable, replacement):
    # Evaluate the replacement in a fresh graph, then rebuild every residual
    # from the original DAG with the selected input interpreted by its value.
    symbols = {}
    for i, n in enumerate(variables + ports):
        e = list(zero)
        e[i] = 1
        symbols[n] = {tuple(e): 1}
    def evaluate(name, memo):
        if isinstance(name, int):
            return {zero: name} if name else {}
        if name in memo:
            return memo[name]
        op, a, b = rows[name]
        x, y = evaluate(a, memo), evaluate(b, memo)
        memo[name] = add(x, y) if op == '+' else add(x, y, -1) if op == '-' else mul(x, y)
        return memo[name]
    replacement_poly = evaluate(replacement, dict(symbols))
    assert all(not m[variables.index(variable)] for m in replacement_poly)
    symbols[variable] = replacement_poly
    return {r: evaluate(r, symbols) for r in residuals}

answers = []
for v, e, removed, orientation in bindings:
    all_polys = polys_for(v, e)
    assert not all_polys[removed], (v, e, removed)
    degrees = {n: max((sum(m[:26]) for m in p), default=-1)
               for n, p in all_polys.items() if n != removed}
    top = max(degrees.values())
    assert top > 4
    cert = None
    for name, d in degrees.items():
        if d != top:
            continue
        groups = {}
        for mon, coefficient in all_polys[name].items():
            if sum(mon[:26]) == top:
                groups.setdefault(mon[:26], []).append((mon[26:], coefficient))
        for witness, terms in sorted(groups.items()):
            if len(terms) == 1 and terms[0][1] != 0 and terms[0][0][1:] == (0, 0, 0):
                cert = {'residual': name, 'witness_exponents': list(witness),
                        'beta_exponent': terms[0][0][0], 'coefficient': terms[0][1]}
                break
        if cert:
            break
    assert cert, (v, e)
    answers.append({'variable': v, 'replacement': e, 'removed': removed,
                    'orientation': orientation, 'max_residual_degree': top,
                    'sum_of_squares_degree': 2*top, 'certificate': cert})

# Compare independently discovered graph bindings and degrees with survey output.
proc = subprocess.run(['python3', str(SURVEY)], text=True, capture_output=True, check=True)
start = proc.stdout.find('\n{\n')
assert start >= 0
reported = json.loads(proc.stdout[start + 1:])
def compare_report(report):
    if report['status'] != 'PASS_DIRECT_SUBSTITUTION_SURVEY':
        raise ValueError('status')
    lookup = {(r['variable'], r['replacement'], r['removed']): r for r in report['results']}
    if len(lookup) != len(answers) or len(report['results']) != len(answers):
        raise ValueError('binding count')
    for answer in answers:
        key = (answer['variable'], answer['replacement'], answer['removed'])
        if key not in lookup:
            raise ValueError(('missing binding', key))
        row = lookup[key]
        if (row['max_residual_degree'] != answer['max_residual_degree'] or
                row['sum_of_squares_degree'] != answer['sum_of_squares_degree']):
            raise ValueError(('degree', key))
compare_report(reported)
for label, mutate in (
        ('omitted_reverse_binding', lambda r: r['results'].pop()),
        ('forged_degree', lambda r: r['results'][0].update(sum_of_squares_degree=8)),
        ('duplicate_binding', lambda r: r['results'].append(r['results'][0]))):
    changed = json.loads(json.dumps(reported))
    mutate(changed)
    try:
        compare_report(changed)
    except ValueError:
        pass
    else:
        raise AssertionError(('undetected report mutation', label))

assert {str(p): H(p) for p in inputs} == input_hashes

receipt = {'status': 'PASS_INDEPENDENT_DIRECT_SUBSTITUTION_AUDIT',
           'graph_sha256': H(GRAPH), 'survey_sha256': H(SURVEY),
           'audit_sha256': H(Path(__file__)), 'square_residuals': residuals,
           'lean_mask_source_sha256': H(MASK), 'lean_kernel_source_sha256': H(KERNEL),
           'binding_count': len(bindings), 'distinct_witnesses': len({x[0] for x in bindings}),
           'mutation_controls': ['omitted_reverse_binding', 'forged_degree', 'duplicate_binding'],
           'results': answers,
           'scope': 'Finite symbolic graph arithmetic for direct bindings only; beta-positive leading coefficients; no Lean model theorem or global minimality.'}
out = D / 'receipt.json'
assert not out.exists()
out.write_text(json.dumps(receipt, indent=2, sort_keys=True) + '\n')
print(receipt['status'], H(out))
