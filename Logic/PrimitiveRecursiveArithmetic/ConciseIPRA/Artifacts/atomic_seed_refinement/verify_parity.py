#!/usr/bin/env python3
"""Replay frozen certificates against each exact predecessor/candidate pair."""
import concurrent.futures
import json
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent
PAIRS = [('reference/native_goal_643.py', 'code/native_goal_checker.py'),
         ('reference/native_strict_637.py', 'code/native_strict_checker.py')]

def run(task):
    group, case, optimized, predecessor, candidate = task
    payload = (ROOT / 'tests/native' / group / case['file']).read_text()
    command = [sys.executable, '-I', '-S', '-B'] + (['-O'] if optimized else [])
    results = []
    for program in (predecessor, candidate):
        process = subprocess.run(command + [str(ROOT / program)],
                                 input=payload, text=True, capture_output=True,
                                 timeout=30)
        results.append(process.returncode == 0 and process.stdout == 'ACCEPT\n')
    return {'group': group, 'fixture': case['file'], 'optimized': optimized,
            'predecessor': predecessor, 'candidate': candidate,
            'predecessor_accepts': results[0], 'candidate_accepts': results[1],
            'agrees': results[0] == results[1]}

def main():
    tasks = []
    for group in ('proofs', 'boundary'):
        cases = json.loads((ROOT / 'tests/native' / group / 'cases.json').read_text())
        for case in cases:
            for optimized in (False, True):
                for predecessor, candidate in PAIRS:
                    tasks.append((group, case, optimized, predecessor, candidate))
    with concurrent.futures.ThreadPoolExecutor(max_workers=8) as pool:
        rows = list(pool.map(run, tasks))
    failures = [r for r in rows if not r['agrees']]
    result = {'python': sys.version, 'distinct_cases': len(tasks) // 4,
              'process_executions': 2 * len(rows), 'mismatches': len(failures),
              'results': rows}
    (ROOT / 'evidence/parity_verification.json').write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps({k: v for k, v in result.items() if k != 'results'}, indent=2))
    if failures:
        raise SystemExit(1)

if __name__ == '__main__':
    main()
