"""Independent phase-boundary and parser differential audit."""
import copy
import json
from pathlib import Path
import subprocess
import sys

BASE = Path(__file__).resolve().parent / 'validated'
PAIRS = {
    'strict': (BASE/'controls/checker_strict606.py',
               BASE/'code/checker_strict_procedure.py'),
    'native': (BASE/'controls/checker_native579.py',
               BASE/'code/checker_native_procedure.py'),
}
good = [[0, 0, 1, 1], [[1, 1, 1], 1]]
cases = [('direct_zero', json.dumps(good), True)]
for name, goal in [
    ('scalar_zero', 0), ('scalar_one', 1), ('scalar_negative', -1),
    ('empty_formula', []), ('old_zero', [0, 0]),
    ('even_alias', [2, 2]), ('free_slot', [3, 3]),
    ('later_slot', [5, 5]), ('free_rigid', [-1, -1]),
    ('bool_term', [True, True]), ('false_term', [False, False]),
    ('float_term', [1.0, 1.0]), ('null_term', [None, None]),
    ('string_term', ['1', '1']), ('object_term', [{}, {}]),
    ('empty_term', [[], []]), ('iterator_wrong_arity', [[1, 1], [1, 1]]),
    ('Q_root', [[1, 1], [1, 1], [1, 1]]),
    ('false_equation', [1, [1]]),
]:
    data = copy.deepcopy(good)
    data[-1] = goal
    cases.append((name, json.dumps(data), False))
for name, text in [
    ('bad_json', '[1,'), ('two_values', '[] []'),
    ('top_number', '1'), ('top_string', '"1"'),
    ('top_object', '{}'), ('empty_certificate', '[]'),
    ('infinite_float', '[1e999]'),
]:
    cases.append((name, text, False))
prefixes = [('bool', True), ('float', 1.0), ('null', None),
            ('string', 'unused'), ('object', {'x': 1})]
results = []
for kind, pair in PAIRS.items():
    specific = cases + [('unused_prefix_' + name,
                         json.dumps([value] + good), kind == 'native')
                        for name, value in prefixes]
    for optimized in (False, True):
        for name, text, expected in specific:
            row = {'profile': kind, 'optimized': optimized,
                   'case': name, 'expected': expected}
            for key, file in zip(('control', 'candidate'), pair):
                proc = subprocess.run(
                    [sys.executable] + (['-O'] if optimized else []) + [str(file)],
                    input=text, text=True, capture_output=True, timeout=5)
                row[key] = proc.returncode == 0 and proc.stdout == 'ACCEPT\n'
            results.append(row)
bad = [r for r in results if r['control'] != r['candidate']
       or r['candidate'] != r['expected']]
report = {'python': sys.version, 'paired_cases': len(results),
          'executions': 2 * len(results), 'unexpected': bad, 'results': results}
Path(__file__).with_suffix('.json').write_text(json.dumps(report, indent=2) + '\n')
print(json.dumps({k: v for k, v in report.items() if k != 'results'}, indent=2))
if bad:
    raise SystemExit(1)
