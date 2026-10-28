#!/usr/bin/env python3
"""Replay all main exact checks; no third-party packages or network needed."""
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path
import hashlib
import json
import subprocess
import sys

ROOT = Path(__file__).resolve().parent
SCRIPTS = [
    ('verify_quartet.py', 'quartet_checks.json'),
    ('check_joint_objective.py', 'joint_objective_checks.json'),
    ('joint_partition_prototype.py', 'joint_prototype_checks.json'),
    ('check_degree_flow.py', 'degree_flow_checks.json'),
    ('audit_joint_objective.py', 'joint_objective_audit.json'),
]


def run(item):
    script, output = item
    command = [sys.executable]
    if sys.flags.optimize:
        command += ['-O']
    command += [str(ROOT / 'code' / script)]
    result = subprocess.run(command, cwd=ROOT, capture_output=True, text=True)
    if result.returncode:
        raise RuntimeError(script + ' failed:\n' + result.stderr[-6000:] + result.stdout[-2000:])
    target = ROOT / 'results' / output
    data = target.read_bytes()
    json.loads(data)
    return {'script': script, 'status': 'PASS', 'result': 'results/' + output,
            'sha256': hashlib.sha256(data).hexdigest()}


def main():
    (ROOT / 'results').mkdir(exist_ok=True)
    with ThreadPoolExecutor(max_workers=3) as pool:
        results = list(pool.map(run, SCRIPTS))
    summary = {'status': 'PASS', 'optimized_python': bool(sys.flags.optimize),
               'scope': 'Exact finite checks and rational certificates; no complete SAT engine.',
               'checks': results}
    name = 'verification_optimized.json' if sys.flags.optimize else 'verification_summary.json'
    (ROOT / 'results' / name).write_text(json.dumps(summary, indent=2) + '\n')
    print(json.dumps(summary, indent=2))


if __name__ == '__main__':
    main()
