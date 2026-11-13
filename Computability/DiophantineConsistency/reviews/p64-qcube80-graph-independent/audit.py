#!/usr/bin/env python3
"""Read-only structural and univariate audit of the 80-gate candidate."""
import hashlib
import json
import sys
from collections import Counter
from pathlib import Path

if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:
    raise SystemExit('use python3 -I -S -B without optimization')
HERE = Path(__file__).resolve().parent
RESEARCH = HERE.parent.parent / 'research'
FILES = {
    'parent': (RESEARCH / 'p64-qcube81-candidate/graph.json',
               '41c8602480cee0e9a21d3a4cd2a7719fa395bd6aabba821aeb7a9f5c776a3db3'),
    'graph': (RESEARCH / 'p64-qcube80-candidate/graph.json',
              '50e65396385a108eb340a7d117ce490e7ae671452acb5df3574f61b75aeb8825'),
    'binding': (RESEARCH / 'fourteen-p64-qcube80-binding-draft/P64QCube80Binding.lean',
                '53462826fc52467434d87676079262487fb31a24104ca0857562791ca281e452'),
    'binding_receipt': (RESEARCH / 'fourteen-p64-qcube80-binding-draft/lean-replay.json',
                        'c9b28764e7842b8c5342023acc41a3885b9fc4141a6bbdbcd79fa35ed417ae39'),
    'binding_log': (RESEARCH / 'fourteen-p64-qcube80-binding-draft/lean-replay.log',
                    '217a257b8a87ae15b76802a957bacca7f0a87e76a6793fe8df31c3fbc53473d6'),
}
data = {}
for key, (path, expected) in FILES.items():
    b = path.read_bytes()
    if hashlib.sha256(b).hexdigest() != expected:
        raise RuntimeError('hash mismatch for ' + key)
    data[key] = b
parent, graph = (json.loads(data[n]) for n in ('parent', 'graph'))
old, new = parent['source'], graph['source']
assert len(old) == 81 and len(new) == 80
assert parent['witnesses'][7] == 's' and parent['witnesses'][9] == 'rho'
assert graph['witnesses'] == parent['witnesses'][:9] + ['r0'] + parent['witnesses'][10:]
assert graph['fixed_numerals'] == parent['fixed_numerals'] and graph['output'] == parent['output']
assert [r for r in old if 'rho' in r] == [['ell_plus_rho', '+', 'ell', 'rho']]
assert [r for r in old if 'ell_plus_rho' in r] == [
    ['ell_plus_rho', '+', 'ell', 'rho'], ['first_unscaled', '+', 'ell_plus_rho', 's']]
assert [r for r in new if 'r0' in r] == [['first_unscaled', '+', 'ell', 'r0']]
assert [r for r in old if r[0] not in ('ell_plus_rho', 'first_unscaled')] == [
    r for r in new if r[0] != 'first_unscaled']
counts = dict(Counter(r[1] for r in new))
assert counts == {'*': 42, '+': 22, '-': 16}

# Independent full univariate arithmetic over F_p: witness j is (j+1)t,
# while the four fixed numerals have the values 5,6,7,8. This gives a lower
# bound for that specialization, not a general symbolic degree certificate.
prime = 1000003
def trim(a):
    while len(a) > 1 and a[-1] % prime == 0:
        a.pop()
    return [x % prime for x in a]
def add(a, b, sign):
    return trim([(a[i] if i < len(a) else 0) + sign * (b[i] if i < len(b) else 0)
                 for i in range(max(len(a), len(b)))])
def mul(a, b):
    c = [0] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            c[i+j] = (c[i+j] + x*y) % prime
    return trim(c)
v = {n: [0, i+1] for i, n in enumerate(graph['witnesses'])}
v.update({n: [i+5] for i, n in enumerate(graph['fixed_numerals'])})
for n, op, left, right in new:
    a = v[left] if isinstance(left, str) else [left]
    b = v[right] if isinstance(right, str) else [right]
    v[n] = add(a, b, 1) if op == '+' else add(a, b, -1) if op == '-' else mul(a, b)
degree = {n: len(v[n])-1 for n in ('A0', 'M', 'W', 'Na', 'Lt', 'polynomial')}
assert degree == {'A0': 12, 'M': 34, 'W': 22, 'Na': 23, 'Lt': 2, 'polynomial': 68}
coef = lambda n: v[n][1] if n in graph['witnesses'] else v[n][0]
expected = (64 * pow(coef('beta'),46,prime) * pow(coef('J'),46,prime) *
            pow(coef('w'),4,prime) * pow(coef('s'),14,prime) *
            pow(coef('eta')+coef('zeta'),2,prime) * pow(coef('gamma'),2,prime)) % prime
assert expected == v['polynomial'][-1] == 193218 and expected != 0

receipt = json.loads(data['binding_receipt'])
assert receipt['returncode'] == 0 and receipt['exact_expected_output'] is True
assert receipt['log_sha256'] == FILES['binding_log'][1]
expected_log = ''.join("'P64QCube80Binding." + n + "' depends on axioms: [propext]\n"
                       for n in ('first', 'main', 'strong', 'auxiliary', 'transport', 'output'))
assert data['binding_log'].decode() == expected_log
print(json.dumps({'status': 'PASS', 'input_hashes': {k: x[1] for k, x in FILES.items()},
                  'operation_counts': counts, 'unchanged_parent_rows': 79,
                  'ray_prime': prime, 'ray_degrees': degree, 'ray_output_leading_coefficient': expected,
                  'binding_replay_exit': receipt['returncode'],
                  'scope': 'Structural substitution; one exact finite-field ray; retained ring-binding receipt. No converse, iPRA, general degree, or ancestry proof.'},
                 indent=2, sort_keys=True))
