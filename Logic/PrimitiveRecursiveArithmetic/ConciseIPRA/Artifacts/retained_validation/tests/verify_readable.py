"""Compare the explanatory expansion with the counted module on fixed risks."""
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path
import hashlib
import json
import subprocess
import sys

ROOT = Path(__file__).resolve().parent.parent
cases = []
for c in json.loads((ROOT/'tests/fixtures/native_positives.json').read_text())['cases']:
    cases.append(c)
    for suffix, goal in [('zero_one', [1, [1]]), ('one_zero', [[1], 1])]:
        cases.append({'name': c['name']+'_'+suffix,
                      'certificate': c['certificate'][:-1]+[goal], 'expected': False})
for name in ('lazy_ignored_source', 'float_hole_unused_witness'):
    cases.append({'name': name,
                  'certificate': json.loads((ROOT/'examples'/(name+'.json')).read_text()),
                  'expected': True})
cases.append({'name': 'future_capture',
              'certificate': json.loads((ROOT/'tests/fixtures/capture_four.json').read_text()),
              'expected': False})
profiles = [ROOT/'code/checker.py', ROOT/'code/checker_readable.py']


def run(job):
    path, case, optimized = job
    result = subprocess.run([sys.executable, *(['-O'] if optimized else []), str(path)],
                            input=json.dumps(case['certificate'])+'\n',
                            text=True, capture_output=True, timeout=15)
    accepted = result.returncode == 0 and result.stdout == 'ACCEPT\n'
    return {'profile': path.name, 'case': case['name'], 'optimized': optimized,
            'expected': case['expected'], 'accepted': accepted}


with ThreadPoolExecutor(max_workers=6) as pool:
    rows = list(pool.map(run, [(p,c,o) for p in profiles for c in cases for o in (False,True)]))
failures = [r for r in rows if r['expected'] != r['accepted']]
receipt = {'source_hashes': {p.name: hashlib.sha256(p.read_bytes()).hexdigest() for p in profiles},
           'process_runs': len(rows), 'unexpected_outcomes': len(failures),
           'failures': failures, 'results': rows}
(ROOT/'evidence/readable_receipt.json').write_text(json.dumps(receipt, indent=2)+'\n')
print(json.dumps({k:v for k,v in receipt.items() if k!='results'}, indent=2))
if failures:
    raise SystemExit(1)
