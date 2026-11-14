#!/usr/bin/env python3
"""Offline reconstruction, local proofs, comparison and universal replay."""
from pathlib import Path
import argparse
import hashlib
import json
import os
import subprocess
import sys
import tempfile
import time

ROOT = Path(__file__).resolve().parent


def require(ok, message):
    if not ok:
        raise ValueError(message)


def verify_manifest():
    manifest = json.loads((ROOT / 'MANIFEST.json').read_text())
    for name, info in manifest['files'].items():
        data = (ROOT / name).read_bytes()
        require(len(data) == info['bytes'] and
                hashlib.sha256(data).hexdigest() == info['sha256'],
                'Manifest mismatch: ' + name)
    return len(manifest['files'])


def run(args, output):
    started = time.monotonic()
    count = verify_manifest()
    output.mkdir(parents=True, exist_ok=True)
    records = []

    def command(label, program, options=(), optimized=False):
        cmd = [sys.executable, '-B']
        if optimized:
            cmd.append('-O')
        cmd += [str(ROOT / program), *map(str, options)]
        result = subprocess.run(cmd, cwd=ROOT, text=True, capture_output=True)
        (output / (label + '.log')).write_text(result.stdout + result.stderr)
        require(result.returncode == 0, label + ' failed: see ' + str(output))
        records.append({'check': label, 'returncode': 0})
        print(label + ': PASS', flush=True)

    for optimized in (False, True):
        tag = '_optimized' if optimized else ''
        command('local' + tag, 'checks/check_local.py',
                ['--output', output / ('local' + tag + '.json')], optimized)
        command('independent' + tag, 'checks/check_local_independent.py',
                ['--output', output / ('independent' + tag + '.json')], optimized)
    command('comparison', 'checks/compare.py',
            ['--output', output / 'comparison.json'])
    command('source_startup', 'checks/check_source_startup.py',
            ['--output', output / 'source_startup.json'])
    command('variants', 'checks/check_variants.py',
            ['--output', output / 'variants.json'])
    for source in sorted((ROOT / 'comparison').glob('*/u209.native.tm')):
        tag = source.parent.name
        command('portable_' + tag, 'checks/portable_fold.py',
                [source, '--output', output / ('portable_' + tag + '.json')])
    command('rejected_source_fold', 'research/rejected_source_fold/replay_rejected.py',
            ['--output', output / 'rejected_source_fold'])
    if args.quick:
        print('Fresh universal runtime replay: SKIPPED (--quick)', flush=True)
    else:
        command('runtime', 'checks/check_runtime.py', ['--output', output / 'runtime'])
    require(verify_manifest() == count, 'Payload changed during replay')
    receipt = {
        'status': 'U208_RELEASE_REPLAY_PASS', 'quick': args.quick,
        'manifest_files_checked': count, 'checks': records,
        'fresh_universal_runtime_derived': not args.quick,
        'seconds': time.monotonic() - started,
        'scope': 'Mathematical and executable certificate replay, not a new '
                 'kernel-checked PA/Lean/Rocq/MM0 endpoint.',
    }
    (output / 'release_replay.json').write_text(json.dumps(receipt, indent=2) + '\n')
    print(json.dumps(receipt, indent=2))


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--quick', action='store_true')
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    require(__debug__ and not sys.flags.optimize and not os.environ.get('PYTHONOPTIMIZE'),
            'Use ordinary Python with assertions enabled.')
    if args.output:
        run(args, args.output.resolve())
    else:
        with tempfile.TemporaryDirectory(prefix='u208-replay-') as directory:
            run(args, Path(directory))
