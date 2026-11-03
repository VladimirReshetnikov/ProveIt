#!/usr/bin/env python3
"""Inventory selected project object headers and reverse-impact paths."""
from hashlib import sha256
import json
from pathlib import Path
import shutil
import subprocess
import time

HERE = Path(__file__).resolve().parent
MANIFEST = HERE.parent / 'compact12-ipra-integration-build/observations/attempt01/manifest.json'
PRIOR = HERE.parent / 'compact12-ipra-object-import-prototype/observations/attempt02/result.json'
OVERLAY = Path('/tmp/compact12-ipra-integrated-20261102/lib')
NINE = Path('/tmp/nine-ipra-guarded-author-20261102-h/lib')
PACKAGE = Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib')
LEANROOT = Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0')
LEAN = LEANROOT / 'bin/lean'
HELPER = HERE / 'ReadObjectImports.lean'
OUT = HERE / 'observations/attempt01'
EXPECTED_MANIFEST = '36ee7a0c7b881cefffafebd7d3a3ff678aec8010ca2019fe71dc8ff8ed29486e'
EXPECTED_PRIOR = '909a5db211132e97f6ebe8787c87a8861e9b896a65a3ee183c17fe86ec1bf3d9'

def digest(p):
    return sha256(Path(p).read_bytes()).hexdigest()

def verify_overlay(selected):
    actual = {p.relative_to(OVERLAY).as_posix() for p in OVERLAY.rglob('*') if p.is_file()}
    if actual != set(selected):
        raise RuntimeError('overlay file set drift')
    for rel, old in selected.items():
        p = OVERLAY / rel
        if digest(p) != old['sha256'] or str(p.resolve(strict=True)) != old['resolved']:
            raise RuntimeError(f'overlay drift: {rel}')

def main():
    if OUT.exists():
        raise RuntimeError('refusing to overwrite previous attempt')
    if shutil.disk_usage('/tmp').free < 4 * 1024**3:
        raise RuntimeError('less than 4 GiB free')
    if digest(MANIFEST) != EXPECTED_MANIFEST or digest(PRIOR) != EXPECTED_PRIOR:
        raise RuntimeError('manifest or prior scan drift')
    prep = json.loads(MANIFEST.read_text())
    prior = json.loads(PRIOR.read_text())
    if not prior['complete'] or not prior['overlay_unchanged']:
        raise RuntimeError('prior scan incomplete')
    selected = prep['overlay']
    verify_overlay(selected)
    helper_hash = digest(HELPER)
    objects = {}
    for rel, old in selected.items():
        if not rel.endswith('.olean'):
            raise RuntimeError(f'unexpected non-olean selected file: {rel}')
        module = rel[:-len('.olean')].replace('/', '.')
        objects[module] = {'path': str(OVERLAY / rel), 'sha256': old['sha256'],
                           'selection_path': prep['selected_files'][rel]['path'], 'omitted': False}
    for module in prep['omitted_stale_modules']:
        path = NINE / (module.replace('.', '/') + '.olean')
        if module in objects or not path.is_file():
            raise RuntimeError(f'bad omitted fallback: {module}')
        old = prior['objects'][module]
        if digest(path) != old['sha256']:
            raise RuntimeError(f'omitted object drift: {module}')
        objects[module] = {'path': str(path), 'sha256': old['sha256'],
                           'selection_path': str(path), 'omitted': True}
    seeds = {x[:-len('.olean')].replace('/', '.') for x in prep['full_shared_conflicts']
             if x.endswith('.olean')}
    if len(seeds) != len(prep['full_shared_conflicts']) or not seeds <= set(objects):
        raise RuntimeError('unsupported conflict seed family')
    OUT.mkdir(parents=True)
    inputs = sorted(objects.items())
    imports, batches = {}, []
    start_time = time.monotonic()
    for offset in range(0, len(inputs), 16):
        batch = inputs[offset:offset + 16]
        command = [str(LEAN), '-M3000', '-j1', '-DElab.async=false', '--run', str(HELPER)]
        command += [row['path'] for _, row in batch]
        try:
            proc = subprocess.run(command, capture_output=True, text=True, timeout=45)
            code, stdout, stderr = proc.returncode, proc.stdout, proc.stderr
        except subprocess.TimeoutExpired as exc:
            code = None
            stdout = (exc.stdout or b'').decode(errors='replace') if isinstance(exc.stdout, bytes) else (exc.stdout or '')
            stderr = (exc.stderr or b'').decode(errors='replace') if isinstance(exc.stderr, bytes) else (exc.stderr or '')
        n = offset // 16
        (OUT / f'batch-{n:03d}.stdout').write_text(stdout)
        (OUT / f'batch-{n:03d}.stderr').write_text(stderr)
        batches.append({'offset': offset, 'count': len(batch), 'command': command, 'exit_code': code})
        if code != 0 or stderr:
            break
        paths = {row['path']: m for m, row in batch}
        current = None
        for line in stdout.splitlines():
            if line.startswith('BEGIN '):
                path = line[6:]
                if current is not None or path not in paths:
                    raise RuntimeError(f'bad BEGIN {line}')
                current = paths[path]
                imports[current] = []
            elif line.startswith('IMPORT '):
                if current is None:
                    raise RuntimeError('IMPORT without BEGIN')
                imports[current].append(line[7:])
            elif line == 'END':
                if current is None:
                    raise RuntimeError('END without BEGIN')
                current = None
            else:
                raise RuntimeError(f'unexpected output {line}')
        if current is not None or any(m not in imports for m, _ in batch):
            raise RuntimeError('incomplete batch output')
        if len(imports) % 160 == 0 or len(imports) == len(inputs):
            print(json.dumps({'scanned': len(imports), 'total': len(inputs)}, sort_keys=True), flush=True)
    complete = len(imports) == len(inputs) and all(x['exit_code'] == 0 for x in batches)
    edges = {m: set(xs) & set(objects) for m, xs in imports.items()}
    reverse = {m: set() for m in objects}
    for module, dependencies in edges.items():
        for dep in dependencies:
            reverse[dep].add(module)
    dirty = set(seeds)
    queue = list(seeds)
    while queue:
        for module in reverse[queue.pop()]:
            if module not in dirty:
                dirty.add(module)
                queue.append(module)
    stale_nine = sorted(m for m in dirty if m not in seeds and not objects[m]['omitted'] and
                        Path(objects[m]['selection_path']).is_relative_to(NINE))
    dirty_omitted = sorted(m for m in dirty if objects[m]['omitted'])
    omitted_not_dirty = sorted(m for m in objects if objects[m]['omitted'] and m not in dirty)
    unselected = sorted({x for xs in imports.values() for x in xs if x not in objects})
    unresolved = []
    external = []
    for module in unselected:
        rel = module.replace('.', '/') + '.olean'
        if (PACKAGE / rel).is_file() or (LEANROOT / 'lib/lean' / rel).is_file():
            external.append(module)
        else:
            unresolved.append(module)
    verify_overlay(selected)
    omitted_unchanged = all(digest(row['path']) == row['sha256'] for row in objects.values() if row['omitted'])
    result = {'complete': complete, 'objects': objects, 'imports': imports,
              'seeds': sorted(seeds), 'dirty': sorted(dirty), 'dirty_omitted': dirty_omitted,
              'omitted_not_dirty': omitted_not_dirty, 'stale_nine_selected': stale_nine,
              'external_direct_imports': external, 'unresolved_direct_imports': unresolved,
              'overlay_unchanged': True, 'omitted_unchanged': omitted_unchanged,
              'helper_sha256': helper_hash, 'helper_unchanged': digest(HELPER) == helper_hash,
              'duration_seconds': round(time.monotonic() - start_time, 3), 'batches': batches}
    (OUT / 'result.json').write_text(json.dumps(result, indent=2, sort_keys=True) + '\n')
    print(json.dumps({'complete': complete, 'objects': len(objects), 'seeds': len(seeds),
                      'dirty': len(dirty), 'omitted_dirty': len(dirty_omitted),
                      'stale_nine': len(stale_nine), 'unresolved': len(unresolved),
                      'unchanged': omitted_unchanged and digest(HELPER) == helper_hash}, sort_keys=True), flush=True)
    if not complete or not omitted_unchanged or digest(HELPER) != helper_hash:
        raise SystemExit(1)

if __name__ == '__main__':
    main()
