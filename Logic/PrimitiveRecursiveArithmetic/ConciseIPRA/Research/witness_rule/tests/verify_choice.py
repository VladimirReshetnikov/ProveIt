"""Replay the supplied raw tests for the unchanged Choice-DI theory."""
import copy
import json
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def main():
    saved = json.loads((ROOT / 'reference/certified_zero_cases.json').read_text())
    cases = saved['cases'] if isinstance(saved, dict) else saved
    rows = []
    for case in cases:
        packet = copy.deepcopy(case['packet'])
        for instruction in packet[:-1]:
            if isinstance(instruction, list) and len(instruction) == 4 and instruction[0] is None:
                instruction[0] = []
        for optimized in (False, True):
            command = [sys.executable] + (['-O'] if optimized else [])
            result = subprocess.run(command + [str(ROOT / 'code/checker_choice.py')],
                                    input=json.dumps(packet), text=True,
                                    capture_output=True, timeout=20)
            accepted = result.returncode == 0 and result.stdout == 'ACCEPT\n'
            rows.append({'case': case['name'], 'optimized': optimized,
                         'expected': case['accept'], 'accepted': accepted,
                         'match': accepted == case['accept']})
    receipt = {'executions': len(rows), 'results': rows}
    if '--write' in sys.argv:
        (ROOT / 'evidence/choice_verification.json').write_text(json.dumps(receipt, indent=2) + '\n')
    failures = [r for r in rows if not r['match']]
    print(json.dumps({'executions': len(rows), 'mismatches': failures}))
    return int(bool(failures))


if __name__ == '__main__':
    raise SystemExit(main())
