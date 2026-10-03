#!/usr/bin/env python3
"""Independent homogeneous-specialization audit; consumes JSON data only."""
import hashlib
import json
from pathlib import Path

if not __debug__:
    raise RuntimeError('Degree-certificate audit requires assertions enabled')

ROOT = Path(__file__).resolve().parents[1]


def check(path):
    raw = path.read_bytes()
    packet = json.loads(raw)
    claim = packet['exact_degree_certificate']
    modulus = claim['modulus']
    assert type(modulus) is int and modulus > 1
    variables = packet['parameters'] + packet['auxiliaries']
    weights = claim['substitution_weights']
    assert set(weights) == set(variables) and len(variables) == len(set(variables))
    bounds = {name: 1 for name in variables}
    coefficients = {name: weights[name] % modulus for name in variables}
    trace = []
    def node(item):
        if type(item) is int:
            return 0, item % modulus
        assert type(item) is str and item in bounds
        return bounds[item], coefficients[item]
    for name, operation, left, right in packet['source']:
        assert name not in bounds
        dl, cl = node(left)
        dr, cr = node(right)
        if operation == '*':
            bound, top = dl + dr, cl * cr
        else:
            assert operation in ('+', '-')
            bound = max(dl, dr)
            top = (cl if dl == bound else 0)
            top += (1 if operation == '+' else -1) * (cr if dr == bound else 0)
        bounds[name] = bound
        coefficients[name] = top % modulus
        trace.append([name, bound, top % modulus])
    degree, coefficient = node(packet['output'])
    assert trace == claim['gate_degree_top_trace']
    assert degree == claim['formal_degree'] == packet['ledger']['exact_degree']
    assert coefficient == claim['nonzero_top_coefficient'] != 0
    return dict(file=path.name, sha256=hashlib.sha256(raw).hexdigest(),
                degree=degree, coefficient_modulus=modulus,
                nonzero_top_coefficient=coefficient,
                checked_gates=len(packet['source']),
                justification='Nonzero specialized formal-top coefficient certifies exact total degree')


if __name__ == '__main__':
    results = [check(path) for path in sorted((ROOT/'circuits').glob('*.json'))]
    receipt = dict(status='PASS', method='Independent formal-degree homogeneous specialization',
                   third_party_python_executed=False, cases=results)
    (ROOT/'audit'/'degree_crosscheck.json').write_text(json.dumps(receipt, indent=2, sort_keys=True)+'\n')
    print(json.dumps(receipt, sort_keys=True))
