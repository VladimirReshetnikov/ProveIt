#!/usr/bin/env python3
"""Run the finite research audits; no consistency claim follows from a pass."""
import json
import os
from pathlib import Path
import subprocess
import sys


def main():
    if sys.flags.optimize:
        raise RuntimeError('Run the audits with assertions enabled, without -O')
    root = Path(__file__).resolve().parents[1]
    result_dir = root / 'results'
    result_dir.mkdir(exist_ok=True)
    commands = [
        ['code/test_tableau.py'],
        ['code/test_search.py'],
        ['code/audit_calculus.py', '--output', 'results/calculus_audit.json'],
        ['code/audit_monochromatic_decoder.py', '--output', 'results/monochromatic_decoder_audit.json'],
        ['code/check_exceptional_psc.py', '--output', 'results/exceptional_psc.json'],
        ['code/verify_benchmarks.py', '--out', 'results/benchmark_audit.json'],
    ]
    results, logs = [], []
    env = dict(os.environ, PYTHONDONTWRITEBYTECODE='1')
    for args in commands:
        completed = subprocess.run([sys.executable, *args], cwd=root, env=env,
                                   capture_output=True, text=True)
        results.append({'script': args[0], 'returncode': completed.returncode})
        logs.append('COMMAND: ' + ' '.join(args) + '\n' + completed.stdout + completed.stderr)
        print(('PASS ' if completed.returncode == 0 else 'FAIL ') + args[0], flush=True)
        if completed.returncode != 0:
            break
    passed = len(results) == len(commands) and all(x['returncode'] == 0 for x in results)
    evidence = {'passed': passed, 'commands': results, 'python': sys.version.split()[0],
                'scope': 'Finite regression and table audits only; no Lean/Rocq rerun or compiled-machine equivalence'}
    (result_dir/'run_checks.json').write_text(json.dumps(evidence, indent=2)+'\n')
    (result_dir/'run_checks.log').write_text('\n\n'.join(logs))
    raise SystemExit(0 if passed else 1)


if __name__ == '__main__':
    main()
