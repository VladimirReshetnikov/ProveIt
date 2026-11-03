#!/usr/bin/env python3
"""Guarded, resumable author build of the compact/iPRA endpoint source cone."""
import fcntl
from hashlib import sha256
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import time

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[4]
SOURCE_ROOT = REPO / 'Computability/DiophantineConsistency/Lean'
PINS = HERE.parent / 'compact12-ipra-coherent-rebuild-plan/pins.json'
MANIFEST = HERE.parent / 'compact12-ipra-integration-build/observations/attempt01/manifest.json'
SCAN = HERE.parent / 'compact12-ipra-object-import-prototype/observations/attempt02/result.json'
OVERLAY = Path('/tmp/compact12-ipra-integrated-20261102/lib')
PACKAGE = Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib')
PROJECT = Path('/tmp/compact12-ipra-coherent-merged-endpoint-20261102')
LIB = PROJECT / 'lib'
LEAN = Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean')
EXPECT = {
    PINS: '69e58c487a271bd520c371f796f72dcccd8d025105b0909d5a1e425785d39a6d',
    MANIFEST: '36ee7a0c7b881cefffafebd7d3a3ff678aec8010ca2019fe71dc8ff8ed29486e',
    SCAN: '909a5db211132e97f6ebe8787c87a8861e9b896a65a3ee183c17fe86ec1bf3d9',
}
SUFFIXES = ('.olean', '.olean.private', '.olean.server', '.ir', '.ilean',
            '.olean.hash', '.olean.private.hash', '.olean.server.hash', '.ir.hash', '.ilean.hash')

def digest(path):
    return sha256(Path(path).read_bytes()).hexdigest()

def record(path):
    path = Path(path)
    if not os.path.lexists(path):
        return None
    if not path.is_file():
        raise RuntimeError(f'not a regular dependency or dangling link: {path}')
    return {'sha256': digest(path), 'resolved': str(path.resolve(strict=True)),
            'link': os.readlink(path) if path.is_symlink() else None}

def check_pins():
    for path, expected in EXPECT.items():
        if digest(path) != expected:
            raise RuntimeError(f'pinned prerequisite drift: {path}')

def check_overlay(manifest):
    expected = manifest['overlay']
    actual = {p.relative_to(OVERLAY).as_posix() for p in OVERLAY.rglob('*') if p.is_file()}
    if actual != set(expected):
        raise RuntimeError('selected overlay file set changed')
    for rel, old in expected.items():
        p = OVERLAY / rel
        if digest(p) != old['sha256'] or str(p.resolve(strict=True)) != old['resolved']:
            raise RuntimeError(f'selected overlay drift: {rel}')

def check_sources(pins):
    for module, row in pins['modules'].items():
        if digest(REPO / row['path']) != row['sha256']:
            raise RuntimeError(f'source drift: {module}')

def read_receipts(order, pins, manifest):
    stages = HERE / 'observations'
    first_batch = HERE.parent / 'compact12-ipra-incremental-rebuild-merged/observations'
    second_batch = HERE.parent / 'compact12-ipra-incremental-rebuild-merged-next/observations'
    previous = []
    gap = False
    for index, module in enumerate(order, 1):
        base = first_batch if index <= 5 else second_batch if index <= 10 else stages
        directory = base / f'stage-{index:02d}'
        receipt = directory / 'terminal.json'
        if not receipt.exists():
            if directory.exists():
                raise RuntimeError(f'incomplete previous stage requires inspection: {directory}')
            gap = True
            continue
        if gap:
            raise RuntimeError(f'noncontiguous previous stage: {directory}')
        row = json.loads(receipt.read_text())
        obj = LIB / (module.replace('.', '/') + '.olean')
        if (row.get('module') != module or row.get('exit_code') != 0 or
            not row.get('success') or not obj.is_file() or digest(obj) != row.get('object_sha256') or
            digest(REPO / pins['modules'][module]['path']) != row.get('source_sha256') or
            digest(directory / 'compile.log') != row.get('log_sha256')):
            raise RuntimeError(f'previous stage failed validation: {directory}')
        if row['guards'] != {path: record(path) for path in row['guards']}:
            raise RuntimeError(f'previous stage dependency or companion drift: {directory}')
        previous.append(row)
    actual = {p.relative_to(LIB).as_posix() for p in LIB.rglob('*') if p.is_file()}
    expected = set(manifest['overlay']) | {m.replace('.', '/') + '.olean' for m in order[:len(previous)]}
    if actual != expected:
        raise RuntimeError('merged output file set changed or contains incomplete objects')
    for rel, old in manifest['overlay'].items():
        p = LIB / rel
        if not p.is_symlink() or digest(p) != old['sha256'] or str(p.resolve(strict=True)) != old['resolved']:
            raise RuntimeError(f'merged provider drift: {rel}')
    return previous

def main():
    count = int(sys.argv[1]) if len(sys.argv) == 2 else 1
    if not 1 <= count <= 5:
        raise ValueError('pass a stage count from 1 through 5')
    if shutil.disk_usage('/tmp').free < 4 * 1024**3:
        raise RuntimeError('less than 4 GiB free')
    PROJECT.mkdir(exist_ok=True)
    lock = (PROJECT / 'build.lock').open('a+')
    fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
    check_pins()
    manifest = json.loads(MANIFEST.read_text())
    scan = json.loads(SCAN.read_text())
    pins = json.loads(PINS.read_text())
    if (not scan['complete'] or scan['unplanned_dirty_modules'] or
        scan['outside_pinned_source_closure'] or not scan['objects_and_sources_unchanged'] or
        not scan['overlay_unchanged'] or not scan['helper_unchanged']):
        raise RuntimeError('serialized import inventory did not pass')
    missing = set(manifest['omitted_stale_modules'])
    order = [m for m in pins['order'] if m in missing]
    if len(order) != 59 or set(order) != missing:
        raise RuntimeError('unexpected source rebuild order')
    check_sources(pins)
    check_overlay(manifest)
    if not LIB.exists():
        LIB.mkdir()
        for rel, old in manifest['overlay'].items():
            target = LIB / rel
            target.parent.mkdir(parents=True, exist_ok=True)
            target.symlink_to(old['resolved'])
    previous = read_receipts(order, pins, manifest)
    env = {'PATH': '/usr/bin:/bin', 'LEAN_PATH': f'{LIB}:{PACKAGE}', 'LEAN_NUM_THREADS': '1'}
    for index in range(len(previous), min(len(previous) + count, len(order))):
        if shutil.disk_usage('/tmp').free < 4 * 1024**3:
            raise RuntimeError('less than 4 GiB free')
        module = order[index]
        source = REPO / pins['modules'][module]['path']
        output = LIB / (module.replace('.', '/') + '.olean')
        output.parent.mkdir(parents=True, exist_ok=True)
        obs = HERE / 'observations' / f'stage-{index + 1:02d}'
        obs.mkdir(parents=True, exist_ok=False)
        (obs / 'source.lean').write_bytes(source.read_bytes())
        deps = subprocess.run([str(LEAN), '--deps', str(source)], env=env,
                              capture_output=True, text=True, timeout=120)
        (obs / 'deps').write_text(deps.stdout)
        (obs / 'deps.stderr').write_text(deps.stderr)
        if deps.returncode != 0 or deps.stderr:
            raise RuntimeError(f'dependency scan failed: {module}')
        guards = {}
        for line in deps.stdout.splitlines():
            path = Path(line)
            if not path.is_absolute() or not path.is_file() or path.suffix != '.olean':
                raise RuntimeError(f'bad dependency: {line}')
            stem = str(path)[:-len('.olean')]
            for suffix in SUFFIXES:
                guards[stem + suffix] = record(stem + suffix)
        command = [str(LEAN), '-M3000', '-j1', '-DElab.async=false', f'--root={SOURCE_ROOT}',
                   str(source), '-o', str(output)]
        start = time.monotonic()
        try:
            proc = subprocess.run(command, env=env, capture_output=True, text=True, timeout=180)
            code, log = proc.returncode, proc.stdout + proc.stderr
        except subprocess.TimeoutExpired as exc:
            code = None
            log = ((exc.stdout or b'').decode(errors='replace') if isinstance(exc.stdout, bytes) else (exc.stdout or ''))
            log += ((exc.stderr or b'').decode(errors='replace') if isinstance(exc.stderr, bytes) else (exc.stderr or ''))
        (obs / 'compile.log').write_text(log)
        guards_unchanged = guards == {path: record(path) for path in guards}
        source_unchanged = digest(source) == pins['modules'][module]['sha256']
        success = (code == 0 and output.is_file() and guards_unchanged and source_unchanged and
                   not any(s in log for s in ('error:', 'warning:', 'sorryAx')))
        row = {'module': module, 'index': index + 1, 'command': command, 'exit_code': code,
               'duration_seconds': round(time.monotonic() - start, 3),
               'runner_sha256': digest(Path(__file__)),
               'source_sha256': digest(source), 'source_unchanged': source_unchanged,
               'guards': guards, 'guards_unchanged': guards_unchanged,
               'object_sha256': digest(output) if output.is_file() else None,
               'log_sha256': digest(obs / 'compile.log'), 'success': success,
               'scope': 'author exploratory stage; no full transitive or package ancestry audit'}
        (obs / 'terminal.json').write_text(json.dumps(row, indent=2, sort_keys=True) + '\n')
        print(json.dumps({k: row[k] for k in ('module', 'index', 'exit_code', 'duration_seconds', 'success')},
                         sort_keys=True), flush=True)
        if not success:
            raise RuntimeError(f'build stopped at {module}; inspect evidence before any retry')
    check_pins()
    check_sources(pins)
    check_overlay(manifest)
    validated = read_receipts(order, pins, manifest)
    print(json.dumps({'completed': len(validated), 'total': len(order), 'overlay_unchanged': True},
                     sort_keys=True), flush=True)

if __name__ == '__main__':
    main()
