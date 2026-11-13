#!/usr/bin/env python3
"""Counterexample to dropping the strong residual at arbitrary integer ports."""
import hashlib
import json
import operator
from pathlib import Path

if not __debug__:
    raise RuntimeError('this check requires Python assertions enabled')

HERE = Path(__file__).resolve().parent
candidate_path = HERE.parent / 'adaptive-square-sums/candidate.json'
raw = candidate_path.read_bytes()
assert hashlib.sha256(raw).hexdigest() == '11fb3c192fb3a8ab9204ef0a5401198d986e002242e4f48442147aa356263828'
candidate = json.loads(raw)
values = {'beta': 0, 'K0': -2, 'MC': -326, 'MF': 0,
          'J': 1, 'F': 1, 'alpha': 1, 'f': 1, 'i': 1, 'T': 1,
          'X': 1, 'Y': 3, 'r': 1, 'eta': 27, 'zeta': 49,
          'y': 1, 'gamma': 1}
assert all(values[n] > 0 for n in candidate['witnesses'])
assert set(values) == set(candidate['witnesses']) | set(candidate['fixed_numerals'])
ops = {'+': operator.add, '-': operator.sub, '*': operator.mul}
def operand(value):
    return value if isinstance(value, int) else values[value]
for name, op, left, right in candidate['source']:
    assert name not in values
    values[name] = ops[op](operand(left), operand(right))
expected = {'q': 1, 'k': 76, 'c': 255, 'a': 6, 'Delta': 63,
            'U': 3, 'M': 0, 'Bt': 0, 'R': -326, 'Z': 0,
            'Dstar': -6072, 'Q': 0, 'I': 65025, 'A0': 0,
            'A1': 0, 'auxResidual': 0, 'g72': 4228250625}
assert all(values[name] == result for name, result in expected.items())
assert 1 + values['Delta'] * values['c2'] == 2024**2
assert values['Dstar'] == -values['U'] * 2024
assert values['sumSquares'] == values['g72']**2 > 0
print('PASS_UNIVERSAL_PORT_STRONG_FACTOR_OBSTRUCTION', json.dumps(expected, sort_keys=True))
