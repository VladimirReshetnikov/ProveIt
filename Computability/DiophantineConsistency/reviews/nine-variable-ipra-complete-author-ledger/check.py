#!/usr/bin/env python3
"""Recheck the completed 104-stage author ledger without running Lean."""
from hashlib import sha256
import json
from pathlib import Path
import subprocess
import sys

if not __debug__:
    raise RuntimeError('optimized Python is rejected')
HERE = Path(__file__).resolve().parent
DC = HERE.parents[1]
ROOT = DC.parents[1]
LIVE = Path('/tmp/nine-ipra-guarded-author-20261102-h')
RUNNER = DC / 'research/nine-variable-ipra/bounded-build-preflight/replay.py'


def digest(path):
    return sha256(Path(path).read_bytes()).hexdigest()


result = subprocess.run([sys.executable, '-I', '-S', '-B', str(RUNNER),
                         '--output', str(LIVE), '--check'], cwd=ROOT,
                        capture_output=True, text=True, timeout=120)
if result.returncode != 0 or result.stderr or result.stdout.strip() != 'ALL_STAGES_RECORDED 104':
    raise RuntimeError(('ledger check failed', result.returncode, result.stdout, result.stderr))
manifest = json.loads((LIVE / 'manifest.json').read_text())
rows = []
for index, item in enumerate(manifest['modules'], 1):
    path = LIVE / 'receipts' / f'{index:03d}.json'
    receipt = json.loads(path.read_text())
    if receipt['status'] != 'PASS' or receipt['module'] != item['module']:
        raise RuntimeError(f'ledger mismatch at stage {index}')
    rows.append({'stage': index, 'module': item['module'], 'receipt_sha256': digest(path),
                 'source_sha256': receipt['source_sha256'],
                 'object_sha256': receipt['output']['sha256']})
if len(rows) != 104 or rows[79]['module'] != 'DiophantineConsistency.IPRANineCurrent' or \
        rows[80]['module'] != 'DiophantineConsistency.IPRANineChecks' or \
        rows[-1]['module'] != 'DiophantineConsistency.IPRAExplicitZFCFinal':
    raise RuntimeError('unexpected endpoint order')
print(json.dumps({'status': 'ALL_STAGES_RECORDED_104',
                  'manifest_sha256': digest(LIVE / 'manifest.json'), 'stages': rows,
                  'scope': 'Incremental single-author ledger; no paired replay or full closure.'},
                 sort_keys=True, indent=2))
