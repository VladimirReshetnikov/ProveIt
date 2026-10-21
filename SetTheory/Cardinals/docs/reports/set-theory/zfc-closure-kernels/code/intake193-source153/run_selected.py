#!/usr/bin/env python3
"""Portable path adapter for root's exact six selected Source153 commands.

This adapter has been source-reviewed but was not used for the original run.
It performs no delivery-manifest, ancestor, optional, or full-runtime job.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import time


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--packet', required=True, type=Path)
    ap.add_argument('--plan', required=True, type=Path)
    ap.add_argument('--reviewed-inputs', required=True, type=Path)
    ap.add_argument('--baseline-table', required=True, type=Path)
    ap.add_argument('--baseline-source', required=True, type=Path)
    ap.add_argument('--output', required=True, type=Path)
    a = ap.parse_args()
    if not __debug__ or sys.flags.optimize:
        raise SystemExit('Assertions must remain enabled.')
    sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
    plan = json.loads(a.plan.read_text())
    pins = json.loads(a.reviewed_inputs.read_text())
    packet, out = a.packet.resolve(), a.output.resolve()
    if out.exists() or packet == out or packet in out.parents:
        raise SystemExit('Use a nonexistent output directory outside the packet.')
    expected = ['peirce-models', 'residual-blocks', 'residual-source',
                'two-adic-source', 'literal-deltas', 'weak-caller-counterexamples']
    assert [j['name'] for j in plan['jobs']] == expected
    by_path = {x['path']: x['sha256'] for x in pins['fully_read_code']}
    for job in plan['jobs']:
        for name in job['reviewed_closure']:
            assert sha(packet / name) == by_path[name], name
    baseline = [a.baseline_table.resolve(), a.baseline_source.resolve()]
    assert [sha(p) for p in baseline] == [x['sha256'] for x in plan['baseline_inputs']]
    out.mkdir(parents=True)
    shutil.copyfile(Path(__file__), out/'run.py')
    copy, outputs, base = out/'packet', out/'outputs', out/'baseline219'
    shutil.copytree(packet, copy)
    outputs.mkdir()
    (out/'logs').mkdir()
    for src, desc in zip(baseline, plan['baseline_inputs']):
        target = base/desc['relative_target']
        target.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(src, target)
    def expand(s):
        return s.replace('{COPY}', str(copy)).replace('{OUT}', str(outputs)).replace('{BASE219}', str(base))
    env = dict(os.environ)
    env.pop('PYTHONOPTIMIZE', None)
    env['PYTHONDONTWRITEBYTECODE'] = '1'
    result = {'status': 'RUNNING', 'selected_names': expected,
              'scope': 'Six reviewed cheap selected leaves, no optional jobs, runtime, manifest or ancestor wrapper.',
              'jobs': [], 'portable_adapter_sha256': sha(Path(__file__)),
              'plan_sha256': sha(a.plan), 'reviewed_inputs_sha256': sha(a.reviewed_inputs)}
    for job in plan['jobs']:
        name = job['name']
        command = [expand(s) for s in job['argv']]
        command[0] = sys.executable
        start = time.monotonic()
        with (out/'logs'/(name+'.stdout')).open('w') as stdout, (out/'logs'/(name+'.stderr')).open('w') as stderr:
            try:
                process = subprocess.run(command, cwd=expand(job['cwd']), stdout=stdout,
                                         stderr=stderr, env=env, timeout=job['timeout'])
                code, limit = process.returncode, False
            except subprocess.TimeoutExpired:
                code, limit = None, True
        result['jobs'].append({'name': name, 'argv': command, 'cwd': expand(job['cwd']),
                               'exit_code': code, 'timeout': limit, 'timeout_seconds': job['timeout'],
                               'seconds': time.monotonic()-start, 'expected': job['expected']})
        result['status'] = 'RUNNING' if code == 0 else 'FAIL'
        (out/'actual.json').write_text(json.dumps(result, indent=2)+'\n')
        print(name, code, flush=True)
        if code != 0:
            return 1
    result['status'] = 'SIX_SELECTED_PROCESSES_EXIT_ZERO_PENDING_RESULT_AUDIT'
    (out/'actual.json').write_text(json.dumps(result, indent=2)+'\n')
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
