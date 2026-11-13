"""Run finite derived-rule certificates and targeted rejection controls."""
from copy import deepcopy
from pathlib import Path
import json
import subprocess
import sys
import platform
from build_certificates import build

ROOT = Path(__file__).resolve().parent
positive = build()
controls = []
for name, data in positive.items():
    controls.append((name, data, True))
base = positive['schematic_formula_transport']

def bad(name, modify):
    data = deepcopy(base)
    modify(data)
    controls.append((name, data, False))

bad('alias_reuses_old_parameter', lambda d: d['proof'].__setitem__('parameter', 'x'))
bad('alias_replacement_mentions_new_parameter',
    lambda d: d['proof'].__setitem__('term', ['v', d['proof']['parameter']]))
bad('alias_replacement_has_free_bound_index',
    lambda d: d['proof'].__setitem__('term', ['b', 0]))
bad('back_source_unavailable',
    lambda d: d['proof']['body'].__setitem__('parameter', 'undeclared'))
bad('wrong_major_orientation',
    lambda d: d['assumptions'].__setitem__(0, ['eq', ['v', 'y'], ['v', 'x']]))
bad('wrong_source_instance',
    lambda d: d['assumptions'].__setitem__(1, ['pred', 'F', ['v', 'y']]))
bad('incorrect_goal', lambda d: d.__setitem__('goal', ['pred', 'G', ['v', 'y']]))
bad('unknown_inference', lambda d: d['proof'].__setitem__('rule', 'refl'))
bad('unexpected_trusted_field', lambda d: d['proof'].__setitem__('trusted', True))
bad('undeclared_parameter_in_goal',
    lambda d: d.__setitem__('goal', ['pred', 'F', ['v', 'z']]))
bad('boolean_hyp_index',
    lambda d: d['proof']['body']['instance'].__setitem__('index', True))
bad('scope_escape_under_D',
    lambda d: d.__setitem__('goal', ['d', ['eq', ['b', 2], ['0']]]))

rows = []
for name, data, expected in controls:
    for optimized in (False, True):
        args = [sys.executable, '-I', '-S', '-B']
        if optimized:
            args.append('-O')
        result = subprocess.run(args + [str(ROOT / 'checker.py')],
            input=json.dumps(data).encode(), capture_output=True, timeout=10)
        accepted = result.returncode == 0 and result.stdout == b'ACCEPT\n'
        rows.append({'case': name, 'optimized': optimized,
                     'expected': expected, 'accepted': accepted})
failures = [r for r in rows if r['expected'] != r['accepted']]
report = {'python': platform.python_version(), 'positive_certificates': len(positive),
          'negative_controls': len(controls) - len(positive),
          'process_executions': len(rows), 'failures': failures, 'results': rows,
          'assurance': 'Finite independent fragment checks; not Lean/Rocq verification or a proof of full iPRA equivalence.'}
(ROOT / 'evidence.json').write_text(json.dumps(report, indent=2) + '\n')
print(json.dumps({k:v for k,v in report.items() if k!='results'}, indent=2))
if failures:
    raise SystemExit(1)
