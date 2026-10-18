#!/usr/bin/env python3
"""Verify the delivered files and replay mathematical certificates portably.

All result-generating commands run in a temporary copy. The baseline and the
research record are never rewritten. Solver and exhaustive-search reruns are
documented separately and are not required to replay the proved results.
"""
from pathlib import Path
import argparse
import hashlib
import json
import os
import shutil
import subprocess
import sys
import tempfile
import time

ROOT = Path(__file__).resolve().parent


def integrity(root):
    manifest = root / 'SHA256SUMS'
    if not manifest.is_file():
        raise SystemExit('Missing delivery SHA256SUMS.')
    count = 0
    for row in manifest.read_text().splitlines():
        wanted, name = row.split('  ', 1)
        p = root / name
        assert p.is_file(), name
        assert hashlib.sha256(p.read_bytes()).hexdigest() == wanted, name
        count += 1
    return count


def main():
    if not __debug__:
        raise SystemExit('Assertions are required; run without -O.')
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--full', action='store_true', help='Also replay the full supplied nine-stage baseline suite.')
    ap.add_argument('--output', type=Path, help='Optionally write this run summary to a specified path.')
    args = ap.parse_args()
    count = integrity(ROOT)
    print(f'DELIVERY INTEGRITY PASS: {count} hashes', flush=True)
    records = []
    began = time.monotonic()
    with tempfile.TemporaryDirectory(prefix='zfc-below246-replay-') as tmp:
        work = Path(tmp)
        for name in ['baseline', 'experiments']:
            shutil.copytree(ROOT/name, work/name, ignore=shutil.ignore_patterns('__pycache__', '*.pyc'))
        env = os.environ.copy()
        env['ZFC246_BASE'] = str(work/'baseline/context246')
        env.pop('ZFC246_TABLE', None)
        env['PYTHONDONTWRITEBYTECODE'] = '1'
        base = work/'baseline/context246'

        def run(label, argv, cwd=work):
            start = time.monotonic()
            result = subprocess.run([sys.executable, '-B', *map(str, argv)],
                cwd=cwd, env=env, text=True, capture_output=True)
            row = {'label': label, 'command': list(map(str, argv)),
                   'returncode': result.returncode, 'seconds': time.monotonic()-start,
                   'stdout': result.stdout, 'stderr': result.stderr}
            records.append(row)
            print(label, 'PASS' if result.returncode == 0 else 'FAIL', flush=True)
            if result.returncode:
                print(result.stdout)
                print(result.stderr, file=sys.stderr)
                raise SystemExit(result.returncode)

        run('Pristine baseline integrity', ['code/check_hashes.py'], base)
        if args.full:
            run('Full nine-stage baseline suite', ['code/verify_all.py'], base)
        else:
            run('Baseline universal macro inductions', ['code/check_macro_inductions.py'], base)
        run('Partial245 universal decrements and increment counterexample',
            ['experiments/tail/verify_decrement245.py', '--base', base,
             '--output-dir', work/'experiments/tail'])
        run('Partial244 universal arithmetic contracts',
            ['experiments/forward/prove_forward_carry.py'])
        run('Partial244 exact configuration collisions',
            ['experiments/forward/check_collision.py'])
        run('Return-context counterexample',
            ['experiments/runtime/verify_return_counterexample.py'])
        run('Universal detector caller partition',
            ['experiments/tail/audit_detector_entry.py', '--base', base,
             '--output', work/'experiments/tail/detector-entry-audit.json'])
        models = sorted((work/'experiments/counter').glob('*.json'))
        sat_count = 0
        for model in models:
            data = json.loads(model.read_text())
            if data.get('status') == 'sat' and 'table' in data:
                sat_count += 1
                run('Independent detector replay: '+model.name,
                    ['experiments/decoder/verify_detector.py', model])
        assert sat_count == 2, sat_count
        run('Alternate246 inherited induction support',
            ['experiments/decoder/audit_detector_support.py'])
        run('Alternate246 all instruction contracts and exact blank prefix',
            ['experiments/decoder/verify_alternate.py'])
        collision = json.loads((work/'experiments/forward/collision.json').read_text())
        assert len(collision['examples']) == 3
        assert [len(e['zero_trace'])-1 for e in collision['examples']] == [14, 46, 48]
    output = {'status': 'PASS', 'delivery_hashes_checked': count,
              'full_baseline_replay': args.full, 'python': sys.version,
              'seconds': time.monotonic()-began, 'commands': records,
              'result': 'No complete sub-246 machine obtained. Partial local results and alternate246 reverified.',
              'proof_status': 'Ordinary symbolic-induction and literal checks; no fresh Lean/Rocq kernel build.'}
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(json.dumps(output, indent=2)+'\n')
    print(f'ALL REQUESTED REPLAY CHECKS PASS ({len(records)} commands)', flush=True)


if __name__ == '__main__':
    main()
