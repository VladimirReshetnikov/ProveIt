#!/usr/bin/env python3
"""Retain point-in-time evidence for seven completed author-side stages."""
from hashlib import sha256
import json
from pathlib import Path
import shutil
import sys

if not __debug__:
    raise RuntimeError('optimized Python is rejected')
HERE = Path(__file__).resolve().parent
LIVE = Path('/tmp/nine-ipra-guarded-author-20261102-h')
OUT = HERE / 'author'
if OUT.exists():
    raise RuntimeError('refusing to overwrite evidence')


def digest(path):
    return sha256(Path(path).read_bytes()).hexdigest()


def copy(relative):
    src = LIVE / relative
    dst = OUT / relative
    dst.parent.mkdir(parents=True, exist_ok=True)
    shutil.copyfile(src, dst)
    if digest(src) != digest(dst):
        raise RuntimeError(f'copy mismatch: {relative}')


copy(Path('manifest.json'))
results = []
for index in range(24, 31):
    number = f'{index:03d}'
    rel = Path('receipts') / f'{number}.json'
    copy(rel)
    receipt = json.loads((OUT / rel).read_text())
    if receipt['status'] != 'PASS':
        raise RuntimeError(f'stage {index} was not accepted')
    module = receipt['module']
    source = Path('src') / Path(*module.split('.')).with_suffix('.lean')
    copy(source)
    if digest(OUT / source) != receipt['source_sha256']:
        raise RuntimeError(f'source mismatch: {module}')
    target = LIVE / 'lib' / Path(*module.split('.')).with_suffix('.olean')
    if digest(target) != receipt['output']['sha256']:
        raise RuntimeError(f'object mismatch: {module}')
    success = Path(receipt['log']).parent.relative_to(LIVE)
    for name in ('compile.log', 'deps.stdout', 'deps.stderr'):
        copy(success / name)
    if digest(OUT / success / 'compile.log') != receipt['log_sha256']:
        raise RuntimeError(f'log mismatch: {module}')
    policy = receipt['warning_policy']
    if policy is not None:
        for extension in ('json', 'log'):
            copy(Path('warning-policies') / f'{number}.{extension}')
        failed = Path(policy['evidence_attempt']).relative_to(LIVE)
        for name in ('compile.log', 'deps.stdout', 'deps.stderr', 'failure.json'):
            copy(failed / name)
        source_path = str(LIVE / source)
        accepted = (OUT / success / 'compile.log').read_text().replace(source_path, '<SOURCE>')
        rejected = (OUT / failed / 'compile.log').read_text().replace(source_path, '<SOURCE>')
        baseline = (OUT / 'warning-policies' / f'{number}.log').read_text()
        if accepted != baseline or rejected != baseline:
            raise RuntimeError(f'warning baseline mismatch: {module}')
    results.append({'stage': index, 'module': module, 'receipt_sha256': digest(OUT / rel),
                    'object_sha256': digest(target), 'warning_count':
                    0 if policy is None else policy['warning_count']})

(HERE / 'CHECK.json').write_text(json.dumps({
    'status': 'PASS_AUTHOR_OBSERVATION_STAGES_24_30', 'stages': results,
    'scope': 'Point-in-time retained author evidence; not an independent replay or full closure audit.'
}, sort_keys=True, indent=2) + '\n')
print('PASS_AUTHOR_OBSERVATION_STAGES_24_30')
