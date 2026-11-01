#!/usr/bin/env python3
"""Build the named Foundation targets in an isolated, pre-snapshotted Lake root.

The input manifest authenticates the archived Foundation tree and build config.
The existing external package objects and dynamic dependencies remain inherited.
"""
import hashlib
import json
import os
from pathlib import Path
import shutil
import signal
import subprocess
import sys
import time

HERE = Path(__file__).resolve().parent
MANIFEST = HERE / 'input-manifest.json'
OLD = Path('/tmp/pra14-full-transitive-2x6o__to/package-lib')
LEAN = Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean')
MIN_FREE = 4 * 1024**3

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def check_inputs(root, manifest):
    source = root / 'lib/FormalizedFormalLogic-Foundation'
    actual = {str(p.relative_to(source)): sha(p) for p in sorted(source.rglob('*')) if p.is_file()}
    if actual != manifest['foundation_archive_files_sha256']:
        raise RuntimeError('Foundation archive snapshot changed')
    for name, expected in manifest['configs_sha256'].items():
        if sha(root / name) != expected:
            raise RuntimeError(f'configuration changed: {name}')
    if sha(LEAN) != manifest['lean_sha256']:
        raise RuntimeError('Lean executable changed')
    rev = subprocess.check_output(['git', '-C', '/home/codex/src/Proofs/.lake/packages/mathlib',
                                   'rev-parse', 'HEAD'], text=True).strip()
    if rev != manifest['mathlib_checkout_commit']:
        raise RuntimeError('mathlib checkout changed')

def main():
    if len(sys.argv) != 2:
        raise SystemExit('usage: build_all.py /absolute/isolation/root')
    root = Path(sys.argv[1]).resolve(strict=True)
    manifest = json.loads(MANIFEST.read_text())
    check_inputs(root, manifest)
    log = root / 'build-all.log'
    receipt = root / 'build-all-receipt.json'
    overlay = root / 'package-lib'
    if any(p.exists() for p in (log, receipt, overlay)):
        raise RuntimeError('refusing to overwrite an earlier build or overlay')
    if shutil.disk_usage(root).free < MIN_FREE:
        raise RuntimeError('insufficient free space')
    targets = ['+' + n + ':olean' for n in manifest['historical_module_names']]
    cmd = ['lake', 'build', *targets]
    env = dict(os.environ, LEAN_NUM_THREADS='1')
    start = time.time()
    stopped = False
    with log.open('x') as f:
        p = subprocess.Popen(cmd, cwd=root, env=env, stdout=f, stderr=subprocess.STDOUT,
                             start_new_session=True)
        while p.poll() is None:
            if shutil.disk_usage(root).free < MIN_FREE:
                stopped = True
                os.killpg(p.pid, signal.SIGTERM)
                break
            time.sleep(5)
        exit_code = p.wait()
    record = {'status': 'FAILED', 'exit_code': exit_code, 'space_stop': stopped,
              'elapsed_seconds': round(time.time() - start, 2), 'command': cmd,
              'manifest_sha256': sha(MANIFEST), 'driver_sha256': sha(Path(__file__)),
              'log_sha256': sha(log), 'root': str(root),
              'scope': 'Fresh Foundation build on inherited external package and dynamic ancestry; '
                       'no identity with vanished historical objects is asserted.'}
    try:
        if exit_code != 0:
            raise RuntimeError('Lake build did not exit successfully')
        check_inputs(root, manifest)
        lib = root / '.lake/build/lib/lean'
        objects = {}
        for name in manifest['historical_module_names']:
            obj = lib.joinpath(*name.split('.')).with_suffix('.olean')
            if not obj.is_file():
                raise RuntimeError(f'missing target object: {name}')
            objects[name] = sha(obj)
        overlay.mkdir()
        for p in sorted(OLD.iterdir()):
            if p.name != 'Foundation':
                (overlay / p.name).symlink_to(p)
        (overlay / 'Foundation').symlink_to(lib / 'Foundation', target_is_directory=True)
        broken = [str(p) for p in overlay.iterdir() if not p.exists()]
        if broken:
            raise RuntimeError(f'broken top-level overlay entries: {broken}')
        record.update(status='BUILT', objects=objects, overlay=str(overlay))
    except BaseException as exc:
        record['error'] = repr(exc)
        raise
    finally:
        receipt.write_text(json.dumps(record, indent=2, sort_keys=True) + '\n')
    print('BUILT', len(objects), 'Foundation targets;', overlay, flush=True)

if __name__ == '__main__':
    main()
