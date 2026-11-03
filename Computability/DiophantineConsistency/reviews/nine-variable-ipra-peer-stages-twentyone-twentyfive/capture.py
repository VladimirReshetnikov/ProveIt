#!/usr/bin/env python3
"""Retain the scoped stage 21–25 comparison and live receipt evidence."""
from hashlib import sha256
import json
from pathlib import Path
import shutil
import subprocess
import sys

if not __debug__ or not sys.flags.isolated or not sys.flags.no_site:
    raise RuntimeError('invoke python3 -I -S -B without optimization')
HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]
OUT = HERE / 'observations'
AUTHOR = Path('/tmp/nine-ipra-guarded-author-20261102-h')
PEER = Path('/tmp/nine-ipra-guarded-peer-20261102-a')
OUT.mkdir(exist_ok=False)


def digest(path):
    return sha256(Path(path).read_bytes()).hexdigest()


result = subprocess.run([sys.executable, '-I', '-S', '-B', str(HERE / 'audit.py')],
                        cwd=ROOT, capture_output=True, text=True, timeout=120)
(OUT / 'audit.stdout').write_text(result.stdout)
(OUT / 'audit.stderr').write_text(result.stderr)
with (OUT / 'terminal.json').open('x') as f:
    json.dump({'exit_code': result.returncode, 'audit_sha256': digest(HERE / 'audit.py'),
               'stdout_sha256': digest(OUT / 'audit.stdout'),
               'stderr_sha256': digest(OUT / 'audit.stderr'),
               'capture_sha256': digest(__file__)}, f, indent=2, sort_keys=True)
    f.write('\n')
if result.returncode or result.stderr or json.loads(result.stdout)['status'] != \
        'STAGES_21_TO_25_COMPILED_OBJECT_DIFFERENCE_REMAINS':
    raise RuntimeError('audit did not pass; evidence retained')
for name, root in [('author', AUTHOR), ('peer', PEER)]:
    for i in range(21, 26):
        source = root / 'receipts' / f'{i:03d}.json'
        record = json.loads(source.read_text())
        target = OUT / name / f'{i:03d}'
        target.mkdir(parents=True)
        shutil.copyfile(source, target / 'receipt.json')
        log = Path(record['log'])
        for path in [log, log.parent / 'deps.stdout', log.parent / 'deps.stderr',
                     Path(record['command'][5])]:
            shutil.copyfile(path, target / path.name)
print('CAPTURED_STAGES_21_TO_25_DISCREPANCY')
