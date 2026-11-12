"""Measure every delivered checker and run the frozen CLI regression suite.

No checker imports this harness. The compact and strict input contracts are
tested separately; accepted administrative aliases are not counted as strict
public-language theorems. Finite tests do not replace the report's proofs.
"""
from pathlib import Path
import concurrent.futures
import hashlib
import json
import subprocess
import sys

import measure

ROOT = Path(__file__).resolve().parent
FOUR_FIELD = {
    'code/checker_compact.py': 'compact',
    'code/checker_readable.py': 'compact',
    'baseline/checker_495.py': 'compact',
    'code/checker_strict.py': 'strict',
    'baseline/checker_strict_862.py': 'strict',
    'baseline/checker_strict_869.py': 'strict',
}
THREE_FIELD = {
    'global': 'baseline/checker_tokens_249.py',
    'local': 'baseline/checker_ast_271.py',
}


def jobs(case):
    protocol = case['protocol']
    if protocol == 'four_field':
        targets = [(program, case['expected'][contract], contract)
                   for program, contract in FOUR_FIELD.items()]
    elif protocol.startswith('three_field_'):
        mode = protocol.removeprefix('three_field_')
        programs = THREE_FIELD.values() if mode == 'adversarial' else [THREE_FIELD[mode]]
        targets = [(program, case['expected'], 'compact_three_field') for program in programs]
    else:
        targets = [('code/two_field_reference.py', case['expected'], 'compact_two_field')]
    for program, expected, contract in targets:
        for optimized in [False, True]:
            yield case, program, expected, contract, optimized


def run(job):
    case, program, expected, contract, optimized = job
    data = (ROOT / case['path']).read_bytes()
    if hashlib.sha256(data).hexdigest() != case['sha256']:
        raise ValueError('Fixture hash mismatch: ' + case['path'])
    command = [sys.executable, '-I', '-S', '-B']
    if optimized:
        command.append('-O')
    command.append(str(ROOT / program))
    try:
        process = subprocess.run(command, input=data, capture_output=True, timeout=20)
        accepted = process.returncode == 0 and process.stdout == b'ACCEPT\n'
        valid_signal = process.returncode != 0 or accepted
        stderr_tail = process.stderr.decode(errors='replace')[-200:]
        returncode = process.returncode
        timed_out = False
    except subprocess.TimeoutExpired:
        accepted = False
        valid_signal = False
        stderr_tail = 'Timed out after 20 seconds; classified as a test failure.'
        returncode = None
        timed_out = True
    return {'fixture': case['path'], 'program': program, 'contract': contract,
            'optimized': optimized, 'expected': expected, 'accepted': accepted,
            'returncode': returncode, 'timed_out': timed_out,
            'passed': valid_signal and accepted == expected,
            'stderr_tail': stderr_tail}


def main():
    metrics = measure.main()
    manifest = json.loads((ROOT / 'tests/fixtures.json').read_text())
    work = [job for case in manifest['cases'] for job in jobs(case)]
    with concurrent.futures.ThreadPoolExecutor(max_workers=8) as pool:
        rows = list(pool.map(run, work))
    failures = [row for row in rows if not row['passed']]
    counts = {}
    for row in rows:
        counts[row['program']] = counts.get(row['program'], 0) + 1
    result = {
        'python': sys.version,
        'pinned_commit': manifest['pinned_commit'],
        'fixture_count': len(manifest['cases']),
        'standalone_cli_executions': len(rows),
        'executions_per_program': counts,
        'failed_cli_checks': len(failures),
        'expected_metrics_match': metrics['expected_metrics_match'],
        'program_sha256': {r['path']: r['source_sha256'] for r in metrics['measurements']},
        'failures': failures,
        'results': rows,
        'limits': [
            'Finite regression evidence is not a proof of universal soundness.',
            'Compact acceptance and strict public-goal validation have distinct contracts.',
            'The two-field reference has a different packet protocol and is tested on its own certificates.',
            'The native 643-byte baseline is measured for context; this suite does not re-audit its distinct contract.',
            'No overall simplicity target or new arithmetic axiom deletion is claimed.',
        ],
    }
    (ROOT / 'evidence/validation.json').write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps({key: result[key] for key in [
        'fixture_count', 'standalone_cli_executions', 'executions_per_program',
        'failed_cli_checks', 'expected_metrics_match']}, indent=2))
    if failures or not metrics['expected_metrics_match']:
        print(json.dumps(failures, indent=2))
        raise SystemExit(1)


if __name__ == '__main__':
    main()
