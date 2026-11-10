"""Replay one theorem and rejection controls against two complete checkers.

The original is a byte-identical pinned corpus member. The second changes
only recursive major checking into retained-hypothesis membership.
No input source code, plugins, theorem oracle, or external prover is loaded.
"""
from pathlib import Path
import hashlib
import json
import subprocess
import sys

ROOT = Path(__file__).resolve().parent
PROGRAMS = ('original_flat_checker.py', 'hypothesis_major_checker.py')
EXPECTED = {
    'q_reflexivity': (True, False),
    'paired_constant_identity': (True, True),
    'arithmetic_supply': (True, True),
    'false_varying_closure': (False, False),
    'wrong_outer_goal': (False, False),
    'unallocated_goal_parameter': (False, False),
    'unproved_paired_major': (False, False),
}


def main():
    provenance = json.loads((ROOT/'provenance.json').read_text())
    original = (ROOT/PROGRAMS[0]).read_text()
    assert hashlib.sha256(original.encode()).hexdigest() == provenance['checker_sha256']
    mutation = provenance['mutation']
    assert original.count(mutation['old']) == 1
    assert (ROOT/PROGRAMS[1]).read_text() == original.replace(mutation['old'], mutation['new'])
    certificate = [[[], 0, 0, 0], [[0, 0, [0, 0]], 0, 0, 0], [[0, 0]]]
    assert json.loads((ROOT/'q_reflexivity.json').read_text()) == certificate
    records = []
    for optimized in (False, True):
        for case, expected in EXPECTED.items():
            payload = (ROOT/(case+'.json')).read_text()
            for program, want in zip(PROGRAMS, expected):
                command = [sys.executable] + (['-O'] if optimized else []) + [str(ROOT/program)]
                result = subprocess.run(command, input=payload, text=True,
                                        capture_output=True, timeout=5)
                accepted = result.returncode == 0 and result.stdout.strip() == 'ACCEPT'
                protocol = accepted or (result.returncode != 0 and result.stdout.strip() == 'REJECT')
                row = {'case': case, 'checker': program, 'optimized': optimized,
                       'expected': want, 'accepted': accepted,
                       'stdout': result.stdout, 'stderr': result.stderr,
                       'exit_code': result.returncode,
                       'pass': accepted == want and protocol}
                records.append(row)
    report = {'scope': 'One exact theorem loss under the stated rule deletion, with finite controls; '
                        'not a universal incompleteness claim for every Eq/D redesign.',
              'python': sys.version, 'run_count': len(records),
              'all_passed': all(row['pass'] for row in records), 'records': records}
    (ROOT/'results.json').write_text(json.dumps(report, indent=2)+'\n')
    summary = {k: v for k, v in report.items() if k != 'records'}
    print(json.dumps(summary, indent=2))
    if not report['all_passed']:
        print(json.dumps([row for row in records if not row['pass']], indent=2))
        raise SystemExit(1)


if __name__ == '__main__':
    main()
