"""Reproduce the 300 complete-process readable/compact comparisons."""
from pathlib import Path
import json
import subprocess
import sys

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
positive = json.loads((HERE / 'fixtures/native_positives.json').read_text())['cases']
cases = []
for case in positive:
    cases.append(case)
    for tag, goal in [('false_zero_one', [1, [1]]),
                      ('false_one_zero', [[1], 1])]:
        cases.append({'name': case['name'] + '_' + tag,
                      'certificate': case['certificate'][:-1] + [goal]})
base = positive[0]['certificate']
for j, goal in enumerate([0, 1, [], [0, 1], [2, 1], [3, 1], [-1, 1],
                         [[3], [1]], [[5], [1]], [[1, 3, 1], 1],
                         [[1, 1, 5], 1], [1, 1, 1], [[], 1],
                         True, 1.5, None, 'x', {}]):
    cases.append({'name': 'invalid_public_' + str(j),
                  'certificate': base[:-1] + [goal]})
for j, value in enumerate([None, True, False, 1.5, '', {}, 'unused']):
    cases.append({'name': 'invalid_unused_' + str(j),
                  'certificate': [value] + base})
for j, packet in enumerate([[], [0], [0, 1], [0, 1, 2, 3, 4], 0, None]):
    cases.append({'name': 'malformed_root_packet_' + str(j),
                  'certificate': base[:-2] + [packet] + base[-1:]})
cases.append({'name': 'missing_root_packet', 'certificate': [base[-1]]})
cases.append({'name': 'future_witness_capture', 'certificate':
              json.loads((HERE / 'fixtures/capture_four.json').read_text())})
programs = [ROOT / 'code/checker.py', ROOT / 'code/checker_readable.py']
rows = []
for case in cases:
    data = json.dumps(case['certificate']).encode()
    for optimized in (False, True):
        outcomes = []
        for program in programs:
            result = subprocess.run([sys.executable, *(['-O'] if optimized else []),
                                     str(program)], input=data, capture_output=True,
                                    timeout=30)
            outcomes.append(result.returncode == 0 and result.stdout == b'ACCEPT\n')
        rows.append({'case': case['name'], 'optimized': optimized,
                     'compact': outcomes[0], 'readable': outcomes[1]})
bad = [row for row in rows if row['compact'] != row['readable']]
print(json.dumps({'cases': len(cases), 'process_runs': 2 * len(rows),
                  'mismatches': bad}, indent=2))
if bad:
    raise SystemExit(1)
