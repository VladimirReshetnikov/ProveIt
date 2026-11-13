"""Run concrete target certificates with and without Python optimization."""
import json
from pathlib import Path
import subprocess
import sys

ROOT = Path(__file__).resolve().parent
records = []
for optimized in (False, True):
    command = [sys.executable] + (['-O'] if optimized else []) + [str(ROOT / 'checker.py')]
    for filename in ('reflexivity_two.json', 'exists_one.json',
                     'identity_iteration_induction.json'):
        run = subprocess.run(command, input=(ROOT / 'fixtures' / filename).read_text(),
                             text=True, capture_output=True)
        assert run.returncode == 0 and run.stdout.strip() == 'ACCEPT', run.stderr
        records.append({'fixture': filename, 'optimized': optimized,
                        'expected': 'accept', 'exit_code': run.returncode})
    run = subprocess.run(command, input=json.dumps([[0, [0, 0, 0]], [0, None]]),
                         text=True, capture_output=True)
    assert run.returncode != 0 and 'ACCEPT' not in run.stdout
    records.append({'fixture': 'unproved_contradiction', 'optimized': optimized,
                    'expected': 'reject', 'exit_code': run.returncode})
evidence = {'checks': len(records), 'passed': len(records), 'results': records}
(ROOT / 'cli_evidence.json').write_text(json.dumps(evidence, indent=2) + '\n')
print(json.dumps(evidence, indent=2))
