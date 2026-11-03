#!/usr/bin/env python3
"""Capture the first-five byte comparison and exact live stage receipts."""
from hashlib import sha256
import json
from pathlib import Path
import shutil
import subprocess
import sys

if not __debug__ or not sys.flags.isolated or not sys.flags.no_site:
    raise RuntimeError('invoke python3 -I -S -B without optimization')
HERE = Path(__file__).resolve().parent
DC = HERE.parents[1]
ROOT = DC.parents[1]
OUT = HERE / 'observations'
AUTHOR = Path('/tmp/nine-ipra-guarded-author-20261102-h')
PEER = Path('/tmp/nine-ipra-guarded-peer-20261102-a')
OUT.mkdir(exist_ok=False)


def digest(path):
    return sha256(Path(path).read_bytes()).hexdigest()


run = subprocess.run([sys.executable, '-I', '-S', '-B', str(HERE / 'compare.py')],
                     cwd=ROOT, capture_output=True, text=True, timeout=120)
(OUT / 'compare.stdout').write_text(run.stdout)
(OUT / 'compare.stderr').write_text(run.stderr)
with (OUT / 'terminal.json').open('x') as f:
    json.dump({'exit_code': run.returncode, 'compare_sha256': digest(HERE / 'compare.py'),
               'stdout_sha256': digest(OUT / 'compare.stdout'),
               'stderr_sha256': digest(OUT / 'compare.stderr'),
               'capture_sha256': digest(__file__)}, f, indent=2, sort_keys=True)
    f.write('\n')
if run.returncode or run.stderr or json.loads(run.stdout)['status'] != \
        'FIRST_FIVE_COMPARED_STAGE2_PATH_BYTES_DIFFER':
    raise RuntimeError('comparison did not pass; evidence retained')
for name, root in [('author', AUTHOR), ('peer', PEER)]:
    target = OUT / name
    target.mkdir()
    shutil.copyfile(root / 'manifest.json', target / 'manifest.json')
    for i in range(1, 6):
        receipt = root / 'receipts' / f'{i:03d}.json'
        record = json.loads(receipt.read_text())
        stage = target / f'{i:03d}'
        stage.mkdir()
        shutil.copyfile(receipt, stage / 'receipt.json')
        log = Path(record['log'])
        for path in [log, log.parent / 'deps.stdout', log.parent / 'deps.stderr',
                     Path(record['command'][5])]:
            shutil.copyfile(path, stage / path.name)
print('CAPTURED_FIRST_FIVE_PATH_DIFFERENCE')
