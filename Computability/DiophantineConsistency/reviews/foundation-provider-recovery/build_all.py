#!/usr/bin/env python3
"""Build the named Foundation targets in an isolated, pre-snapshotted Lake root.

The input manifest authenticates the archived Foundation tree and build config.
The existing external package objects and dynamic dependencies remain inherited.
"""
import hashlib
import json
import os
from pathlib import Path
import re
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
MANIFEST_SHA256 = '491075df9eac57799d21b475527b3b1af3dc81ded58e97a87e1cf6c453dcb13d'

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

def uncomment(text):
    result, i, depth = [], 0, 0
    while i < len(text):
        if depth:
            if text.startswith('/-', i): depth += 1; i += 2
            elif text.startswith('-/', i): depth -= 1; i += 2
            else:
                if text[i] == '\n': result.append('\n')
                i += 1
        elif text.startswith('/-', i): depth = 1; i += 2
        elif text.startswith('--', i):
            while i < len(text) and text[i] != '\n': i += 1
        else: result.append(text[i]); i += 1
    if depth:
        raise RuntimeError('unterminated block comment in source')
    return ''.join(result)

def direct_external_inputs(root, targets):
    """Guard declared external imports of the Foundation source closure."""
    source = root / 'lib/FormalizedFormalLogic-Foundation'
    todo, visited, external = list(targets), set(), set()
    while todo:
        name = todo.pop()
        if name in visited:
            continue
        if not name.startswith('Foundation.'):
            external.add(name)
            continue
        visited.add(name)
        path = source.joinpath(*name.split('.')).with_suffix('.lean')
        if not path.is_file():
            raise RuntimeError(f'Foundation source missing: {name}')
        for line in uncomment(path.read_text()).splitlines():
            match = re.match(r'\s*(?:(?:public|meta)\s+)*import\s+(.+)', line)
            if match:
                todo.extend(match.group(1).split())
    path_text = subprocess.check_output(['lake', 'env', 'printenv', 'LEAN_PATH'],
                                        cwd=root, text=True).strip()
    search = [Path(p) for p in path_text.split(':') if p]
    guard = {}
    for name in sorted(external):
        rel = Path(*name.split('.'))
        candidates = [base / rel.with_suffix('.olean') for base in search]
        obj = next((p for p in candidates if p.is_file()), None)
        if obj is None:
            raise RuntimeError(f'external imported object missing: {name}')
        stem = Path(str(obj)[:-len('.olean')])
        for suffix in ('.olean', '.olean.private', '.olean.server', '.ir', '.ilean',
                       '.olean.hash', '.olean.private.hash', '.olean.server.hash',
                       '.ir.hash', '.ilean.hash'):
            path = Path(str(stem) + suffix)
            if os.path.lexists(path):
                if not path.is_file():
                    raise RuntimeError(f'bad external input companion: {path}')
                guard[str(path)] = {'realpath': str(path.resolve()), 'sha256': sha(path)}
            else:
                guard[str(path)] = None
    return sorted(visited), sorted(external), guard

def check_guard(guard):
    for name, expected in guard.items():
        path = Path(name)
        if expected is None:
            if os.path.lexists(path): raise RuntimeError(f'new external companion: {path}')
        elif not path.is_file() or str(path.resolve()) != expected['realpath'] or sha(path) != expected['sha256']:
            raise RuntimeError(f'external input changed: {path}')

def main():
    if len(sys.argv) != 2:
        raise SystemExit('usage: build_all.py /absolute/isolation/root')
    root = Path(sys.argv[1]).resolve(strict=True)
    if sha(MANIFEST) != MANIFEST_SHA256:
        raise RuntimeError('input manifest identity mismatch')
    manifest = json.loads(MANIFEST.read_text())
    driver_hash = sha(Path(__file__))
    check_inputs(root, manifest)
    log = root / 'build-all.log'
    receipt = root / 'build-all-receipt.json'
    overlay = root / 'package-lib'
    if any(p.exists() for p in (log, receipt, overlay)):
        raise RuntimeError('refusing to overwrite an earlier build or overlay')
    if (root / '.lake/build').exists():
        raise RuntimeError('requires a fresh root with no prior Foundation build')
    if shutil.disk_usage(root).free < MIN_FREE:
        raise RuntimeError('insufficient free space')
    targets = ['+' + n + ':olean' for n in manifest['historical_module_names']]
    foundation_sources, external_modules, package_guard = direct_external_inputs(
        root, manifest['historical_module_names'])
    check_guard(package_guard)
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
              'manifest_sha256': MANIFEST_SHA256, 'driver_sha256': driver_hash,
              'log_sha256': sha(log), 'root': str(root),
              'foundation_source_closure': foundation_sources,
              'declared_external_modules': external_modules,
              'declared_external_guard': package_guard,
              'scope': 'Fresh Foundation build on inherited external package and dynamic ancestry; '
                       'no identity with vanished historical objects is asserted.'}
    try:
        if exit_code != 0:
            raise RuntimeError('Lake build did not exit successfully')
        if sha(MANIFEST) != MANIFEST_SHA256 or sha(Path(__file__)) != driver_hash:
            raise RuntimeError('manifest or driver changed during build')
        check_inputs(root, manifest)
        check_guard(package_guard)
        lib = root / '.lake/build/lib/lean'
        objects = {}
        for name in manifest['historical_module_names']:
            obj = lib.joinpath(*name.split('.')).with_suffix('.olean')
            if not obj.is_file():
                raise RuntimeError(f'missing target object: {name}')
            objects[name] = sha(obj)
        foundation = lib / 'Foundation'
        artifacts = {}
        for path in sorted(foundation.rglob('*')):
            if path.is_symlink():
                raise RuntimeError(f'unexpected symlink inside fresh provider: {path}')
            if path.is_file():
                artifacts[str(path.relative_to(foundation))] = sha(path)
        overlay.mkdir()
        for p in sorted(OLD.iterdir()):
            if p.name != 'Foundation':
                (overlay / p.name).symlink_to(p)
        (overlay / 'Foundation').symlink_to(lib / 'Foundation', target_is_directory=True)
        broken = [str(p) for p in overlay.iterdir() if not p.exists()]
        if broken:
            raise RuntimeError(f'broken top-level overlay entries: {broken}')
        record.update(status='BUILT', objects=objects, foundation_artifacts=artifacts,
                      overlay=str(overlay))
    except BaseException as exc:
        record['error'] = repr(exc)
        raise
    finally:
        receipt.write_text(json.dumps(record, indent=2, sort_keys=True) + '\n')
    print('BUILT', len(objects), 'Foundation targets;', overlay, flush=True)

if __name__ == '__main__':
    main()
