#!/usr/bin/env python3
"""Replay positive and deliberate-negative cases with assertions disabled too."""
from pathlib import Path
import json
import subprocess
import sys
import tempfile

root = Path(__file__).resolve().parent
checks = []
temporary = tempfile.TemporaryDirectory(prefix='eth-certificates-')
for name in ('verify_schedule.py', 'verify_degree_51_schedule.py', 'verify_lowdegree_schedule.py', 'verify_streamed_composition.py'):
    for optimized in (False, True):
        for control in (None, 'constant', 'guard'):
            command = [sys.executable] + (['-O'] if optimized else []) + [str(root / name)]
            command.append('--output=' + str(Path(temporary.name) / (name + '.json')))
            if control:
                command.append('--negative-control=' + control)
            result = subprocess.run(command, text=True, capture_output=True, check=False)
            if control is None:
                if result.returncode != 0 or json.loads(result.stdout).get('status') != 'PASS':
                    raise ArithmeticError('positive certificate failed: ' + repr(command))
            elif result.returncode == 0 or 'ArithmeticError: deliberate wrong' not in result.stderr:
                raise ArithmeticError('negative certificate did not fail closed: ' + repr(command))
            checks.append({'script': name, 'optimized': optimized,
                           'negative_control': control, 'exit_code': result.returncode,
                           'expected': True,
                           'error_tail': result.stderr.splitlines()[-1] if control else None})
output = {'status': 'PASS', 'checks': checks}
destination = Path(sys.argv[1]) if len(sys.argv)>1 else root / 'certificate_replay_checks.json'
destination.write_text(json.dumps(output, indent=2) + '\n')
temporary.cleanup()
print(json.dumps(output, indent=2))
