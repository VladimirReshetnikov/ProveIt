#!/usr/bin/env python3
"""Read-only structural and univariate audit of the 79-gate candidate."""
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
    'parent': (RESEARCH / 'p64-qcube80-candidate/graph.json',
               '50e65396385a108eb340a7d117ce490e7ae671452acb5df3574f61b75aeb8825'),
    'graph': (RESEARCH / 'p64-qcube79-candidate/graph.json',
              'd70bbed8b36895ffcf144f51bf78287e03fb2942d62c016ac9c845e691820b9b'),
    'binding': (RESEARCH / 'fourteen-p64-qcube79-binding-draft/P64QCube79Binding.lean',
                '6699312618be0598dc0cc49473533928a46fd91a54871eef444d4f600a04e6a1'),
    'binding_receipt': (RESEARCH / 'fourteen-p64-qcube79-binding-draft/lean-replay.json',
                        'a9b7bee9e42473649c340d4ce049854ac1f0d5d00722cdb5aca48954165c3dd6'),
    'binding_log': (RESEARCH / 'fourteen-p64-qcube79-binding-draft/lean-replay.log',
                    '1f5780ef73fc2bfaa3968a599a43b681ff7a366b105507becf3eb10fa459eed8'),
}
data = {}
for key, (path, expected) in FILES.items():
    b = path.read_bytes()
    if hashlib.sha256(b).hexdigest() != expected:
        raise RuntimeError('hash mismatch for ' + key)
    data[key] = b
parent, graph = (json.loads(data[n]) for n in ('parent', 'graph'))
old, new = parent['source'], graph['source']
assert len(old) == 80 and len(new) == 79
assert parent['witnesses'][9] == 'r0'
assert graph['witnesses'] == parent['witnesses'][:9] + ['t'] + parent['witnesses'][10:]
assert graph['fixed_numerals'] == parent['fixed_numerals'] and graph['output'] == parent['output']
assert [r for r in old if 'r0' in r] == [['first_unscaled', '+', 'ell', 'r0']]
assert [r for r in old if 'first_unscaled' in r] == [
    ['first_unscaled', '+', 'ell', 'r0'],
    ['first_unscaled_square', '*', 'first_unscaled', 'first_unscaled']]
assert [r for r in new if 't' in r] == [['first_unscaled_square', '*', 't', 't']]
assert [r for r in old if r[0] not in ('first_unscaled', 'first_unscaled_square')] == [
    r for r in new if r[0] != 'first_unscaled_square']
counts = dict(Counter(r[1] for r in new))
assert counts == {'*': 42, '+': 21, '-': 16}

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
assert degree == {'A0': 22, 'M': 34, 'W': 22, 'Na': 23, 'Lt': 2, 'polynomial': 68}
coef = lambda n: v[n][1] if n in graph['witnesses'] else v[n][0]
expected = (64 * pow(coef('beta'),46,prime) * pow(coef('J'),46,prime) *
            pow(coef('w'),4,prime) * pow(coef('s'),14,prime) *
            pow(coef('eta')+coef('zeta'),2,prime) * pow(coef('gamma'),2,prime)) % prime
assert expected == v['polynomial'][-1] == 193218 and expected != 0

receipt = json.loads(data['binding_receipt'])
assert receipt['returncode'] == 0 and receipt['exact_expected_output'] is True
assert receipt['log_sha256'] == FILES['binding_log'][1]
expected_log = ''.join("'P64QCube79Binding." + n + "' depends on axioms: [propext]\n"
                       for n in ('first', 'main', 'strong', 'auxiliary', 'transport', 'output'))
assert data['binding_log'].decode() == expected_log
print(json.dumps({'status': 'PASS', 'input_hashes': {k: x[1] for k, x in FILES.items()},
                  'operation_counts': counts, 'unchanged_parent_rows': 78,
                  'ray_prime': prime, 'ray_degrees': degree, 'ray_output_leading_coefficient': expected,
                  'binding_replay_exit': receipt['returncode'],
                  'scope': 'Structural substitution; one exact finite-field ray; retained ring-binding receipt. No converse, iPRA, general degree, or ancestry proof.'},
                 indent=2, sort_keys=True))
