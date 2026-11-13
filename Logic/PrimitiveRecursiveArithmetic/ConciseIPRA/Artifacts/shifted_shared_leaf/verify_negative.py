"""Replay the concrete false-goal attack against the rejected no-parity mutant."""
import json
from pathlib import Path
import subprocess
import sys

ROOT = Path(__file__).resolve().parent
payload = (ROOT / 'negative/false_guarded_goal_shifted_shared.json').read_bytes()
rows = []
for program, expected in [('code/checker.py', False),
                          ('negative/REJECTED_UNSOUND_shared_no_parity.py', True)]:
    for optimized in (False, True):
        args = [sys.executable, '-I', '-S', '-B']
        if optimized:
            args.append('-O')
        args.append(str(ROOT / program))
        result = subprocess.run(args, input=payload, capture_output=True, timeout=25)
        accepted = result.returncode == 0 and result.stdout == b'ACCEPT\n'
        rows.append({'program': program, 'optimized': optimized,
                     'expected_acceptance': expected, 'accepted': accepted,
                     'exit_code': result.returncode})
        if accepted != expected:
            raise AssertionError(rows[-1])
report = {'executions': len(rows), 'unexpected_outcomes': 0, 'results': rows,
          'purpose': 'The mutant is deliberately unsound and excluded from every size record.'}
(ROOT / 'evidence/parity_attack.json').write_text(json.dumps(report, indent=2) + '\n')
print('Parity attack: correct checker rejects; deliberately unsound mutant accepts (normal and -O).')
