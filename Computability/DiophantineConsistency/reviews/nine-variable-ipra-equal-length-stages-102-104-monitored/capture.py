#!/usr/bin/env python3
"""Capture a prefix check and exact author/verify records for one stage batch."""
import argparse
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
AUTHOR = Path('/tmp/nine-ipra-guarded-author-20261102-h')
VERIFY = Path('/tmp/nine-ipra-guarded-verify-20261102-a')
parser = argparse.ArgumentParser()
parser.add_argument('--first', type=int, required=True)
parser.add_argument('--last', type=int, required=True)
args = parser.parse_args()
if not 1 <= args.first <= args.last <= 104:
    raise RuntimeError('bad stage range')
OUT = HERE / 'observations' / f'stages-{args.first:03d}-{args.last:03d}'
OUT.mkdir(parents=True, exist_ok=False)
run = subprocess.run([sys.executable, '-I', '-S', '-B', str(HERE / 'audit.py'),
                      '--upto', str(args.last)], cwd=ROOT, capture_output=True, text=True, timeout=180)
(OUT / 'audit.json').write_text(run.stdout)
(OUT / 'stderr').write_text(run.stderr)
record = {'exit_code': run.returncode, 'first_stage': args.first, 'last_stage': args.last,
          'audit_sha256': sha256((HERE / 'audit.py').read_bytes()).hexdigest(),
          'capture_sha256': sha256(Path(__file__).read_bytes()).hexdigest(),
          'stdout_sha256': sha256((OUT / 'audit.json').read_bytes()).hexdigest(),
          'stderr_sha256': sha256((OUT / 'stderr').read_bytes()).hexdigest()}
(OUT / 'terminal.json').write_text(json.dumps(record, indent=2, sort_keys=True) + '\n')
if run.returncode or run.stderr or json.loads(run.stdout)['status'] != 'EQUAL_LENGTH_PREFIX_SCOPED_COMPARISON_PASS':
    raise RuntimeError('prefix audit failed; evidence retained')
for name, root in [('author', AUTHOR), ('verify', VERIFY)]:
    for i in range(args.first, args.last+1):
        source = root / 'receipts' / f'{i:03d}.json'
        receipt = json.loads(source.read_text())
        target = OUT / name / f'{i:03d}'
        target.mkdir(parents=True)
        shutil.copyfile(source, target / 'receipt.json')
        log = Path(receipt['log'])
        for path in [log, log.parent / 'deps.stdout', log.parent / 'deps.stderr',
                     Path(receipt['command'][5])]:
            shutil.copyfile(path, target / path.name)
print('CAPTURED_EQUAL_LENGTH_PREFIX', args.first, args.last)
