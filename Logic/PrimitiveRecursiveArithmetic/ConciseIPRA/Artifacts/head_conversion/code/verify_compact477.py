"""Check the byte refinement against the exact 478-byte control.

The input framing for both programs is the same final [goal,0] record.
Only the candidate's administrative majors change from 0 to [].
The three surplus truth aliases have separate documented expectations.
"""
import concurrent.futures
import json
from pathlib import Path
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
FIX = ROOT / 'tests/compact477'
cases = json.loads((FIX / 'cases.json').read_text())


def run(case):
    results = []
    for family, program in [('control', 'reference/incumbent_bytes478.py'),
                            ('candidate', 'code/compact477.py')]:
        for optimized in (False, True):
            command = [sys.executable, '-I', '-S', '-B']
            if optimized:
                command.append('-O')
            command.append(str(ROOT / program))
            process = subprocess.run(command,
                input=(FIX / family / case['file']).read_bytes(),
                capture_output=True, timeout=10)
            accepted = process.returncode == 0 and process.stdout == b'ACCEPT\n'
            results.append({'program': program, 'optimized': optimized,
                            'accepted': accepted,
                            'passed': accepted == case[family + '_expected']})
    return {'fixture': case['file'],
            'control_expected': case['control_expected'],
            'candidate_expected': case['candidate_expected'],
            'noncanonical_surplus_alias': case['noncanonical_surplus_alias'],
            'results': results}


with concurrent.futures.ThreadPoolExecutor(max_workers=8) as pool:
    results = list(pool.map(run, cases))
failures = [r for r in results if any(not x['passed'] for x in r['results'])]
report = {'python': sys.version, 'fixture_count': len(cases),
          'process_executions': 4 * len(cases), 'failures': failures,
          'changed_noncanonical_public_aliases':
              [r['fixture'] for r in results if r['noncanonical_surplus_alias']],
          'results': results}
(ROOT / 'evidence/compact477_inherited.json').write_text(
    json.dumps(report, indent=2) + '\n')
print(json.dumps({k: v for k, v in report.items() if k != 'results'}, indent=2))
if failures:
    raise SystemExit(1)
subprocess.run([sys.executable, str(ROOT / 'code/verify_compact477_extended.py')],
               cwd=ROOT, check=True)
