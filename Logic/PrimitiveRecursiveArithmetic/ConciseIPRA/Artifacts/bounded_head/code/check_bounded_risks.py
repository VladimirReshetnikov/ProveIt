"""Independent targeted audit of scope and local-conversion boundaries."""
import importlib.util
import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
source = ROOT / 'code/bounded_checker.py'
spec = importlib.util.spec_from_file_location('bounded_risk_target', source)
checker = importlib.util.module_from_spec(spec)
spec.loader.exec_module(checker)
z = ['z']
v = lambda i: ['v', i]
s = lambda t: ['s', t]
it = lambda c, a, h: ['i', c, a, h]
eq = lambda a, b: ['=', a, b]
tests = []

def run(name, data, expected):
    try:
        checker.check(data)
        accepted = True
    except Exception:
        accepted = False
    tests.append({'name': name, 'expected': expected, 'accepted': accepted})
    if accepted != expected:
        raise RuntimeError(tests[-1])

for depth in range(5):
    previous, current = it(z, v(0), z), v(0)
    for _ in range(depth):
        previous, current = it(previous, z, v(0)), it(current, z, v(0))
    for reverse in [False, True]:
        a, b = (previous, current) if not reverse else (current, previous)
        data = {'variables': 1, 'context': [eq(a, z)], 'goal': eq(b, z),
                'proof': ['hc', depth, a, None]}
        run(f'hc_depth_{depth}_{reverse}', data, depth <= 3)

for depth in [-1, True, 0.0, '0', 4]:
    a = it(z, v(0), z)
    run(f'invalid_depth_{depth!r}',
        {'variables': 1, 'context': [eq(a, z)], 'goal': eq(v(0), z),
         'proof': ['hc', depth, a, None]}, False)

# A source field that would be erased by the zero contraction must still be
# checked before that contraction. Put the bad term only in proof metadata.
bad_previous = it(z, v(0), v(999))
run('erased_out_of_scope_body',
    {'variables': 1, 'context': [eq(it(z, v(0), z), z)],
     'goal': eq(v(0), z), 'proof': ['hc', 0, bad_previous, None]}, False)

# Substitution for an outer variable under an iterator body must shift the
# replacement. The two proposed target formulas differ only at that capture.
t = s(v(0))
u = it(v(0), z, s(v(1)))
correct = it(s(v(0)), z, s(s(v(1))))
captured = it(s(v(0)), z, s(s(v(0))))
for label, target, expected in [('correct', correct, True),
                                 ('capture', captured, False)]:
    run('variable_substitution_' + label,
        {'variables': 1, 'context': [eq(v(0), t), eq(u, z)],
         'goal': eq(z, target), 'proof': ['vs', 0, t, u, None, None]}, expected)

result = {'source': 'code/bounded_checker.py', 'source_sha256': hashlib.sha256(source.read_bytes()).hexdigest(),
          'tests': tests, 'count': len(tests), 'failures': 0,
          'scope': 'Targeted finite checks; not a formal verification or universal proof.'}
(ROOT / 'evidence/bounded_risk_results.json').write_text(json.dumps(result, indent=2) + '\n')
print(json.dumps({'count': len(tests), 'failures': 0, 'source_sha256': result['source_sha256']}))
