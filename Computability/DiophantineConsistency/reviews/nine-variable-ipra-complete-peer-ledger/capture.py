#!/usr/bin/env python3
"""Capture the complete guarded nine-variable author/peer ledger audit."""
from hashlib import sha256
import json
from pathlib import Path
import subprocess
import sys

if not __debug__ or not sys.flags.isolated or not sys.flags.no_site:
    raise RuntimeError('invoke python3 -I -S -B without optimization')
HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]
OUT = HERE / 'observations'
OUT.mkdir(exist_ok=False)
run = subprocess.run([sys.executable, '-I', '-S', '-B', str(HERE / 'audit.py')],
                     cwd=ROOT, capture_output=True, text=True, timeout=180)
(OUT / 'audit.json').write_text(run.stdout)
(OUT / 'stderr').write_text(run.stderr)
record = {'exit_code': run.returncode,
          'audit_sha256': sha256((HERE / 'audit.py').read_bytes()).hexdigest(),
          'capture_sha256': sha256(Path(__file__).read_bytes()).hexdigest(),
          'stdout_sha256': sha256((OUT / 'audit.json').read_bytes()).hexdigest(),
          'stderr_sha256': sha256((OUT / 'stderr').read_bytes()).hexdigest()}
(OUT / 'terminal.json').write_text(json.dumps(record, indent=2, sort_keys=True) + '\n')
if run.returncode or run.stderr or json.loads(run.stdout)['status'] != \
        'BOTH_104_STAGE_LEDGERS_RECORDED_IMPORT_DIFFERENCES_REMAIN':
    raise RuntimeError('ledger audit failed; observation retained')
print('CAPTURED_COMPLETE_NINE_VARIABLE_PEER_LEDGER')
